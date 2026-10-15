"""Phase 2 planner using only official Lean declaration and sketch-oracle facts.

No source declaration is discovered by text matching. The strict default waits
for every participating module's exact-source receipt before classification.
--pending is a read-only extraction progress report, not a partial node plan.
"""
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
VER = HERE / 'verification'
MODEL_ONLY = '--model' in sys.argv
ORACLES = VER / ('model-sketch-oracles' if MODEL_ONLY else 'sketch-oracles')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    plan_name='model-upload-plan.json' if MODEL_ONLY else 'machine-upload-plan.json'
    if '--plan' in sys.argv:
        plan_name=sys.argv[sys.argv.index('--plan')+1]
        assert Path(plan_name).name==plan_name
    plan = json.loads((VER / plan_name).read_text(encoding='utf-8'))
    oracle_sha = sha(ROOT / 'scripts/extract_sketch_info.lean')
    facts_by_module = {}
    receipts = {}
    pending = []
    for module in plan['participating_modules']:
        stem = module.replace('.', '_')
        receipt_path = ORACLES / (stem + '.receipt.json')
        facts_path = ORACLES / (stem + '.jsonl')
        source = HERE / 'machine/lean' / Path(*module.split('.')).with_suffix('.lean')
        if not receipt_path.exists() or not facts_path.exists():
            pending.append(module)
            continue
        receipt = json.loads(receipt_path.read_text(encoding='utf-8'))
        if not (receipt.get('source_sha256') == sha(source)
                and receipt.get('oracle_sha256') == oracle_sha
                and receipt.get('exit_code') == 0):
            pending.append(module)
            continue
        facts = [json.loads(line) for line in facts_path.read_text(encoding='utf-8').splitlines()
                 if line.strip()]
        assert all(f['kind'] in ('decl', 'ref') for f in facts), module
        assert sum(f['kind'] == 'decl' for f in facts) == receipt['declaration_count'], module
        facts_by_module[module] = facts
        receipts[module] = {**receipt, 'facts_sha256': sha(facts_path),
                           'oracle_input_sha256': hashlib.sha256(
                               source.read_text(encoding='utf-8').encode('utf-8')).hexdigest(),
                           'offset_coordinate_system': 'UTF-8 bytes after CRLF-to-LF normalization'}
    print('Exact-source Stage 2 receipts:', len(receipts), '/', len(plan['participating_modules']))
    if '--pending' in sys.argv:
        print('Next pending:', ', '.join(pending[:8]))
        return 0
    if pending:
        print('Classification not started: waiting for', len(pending), 'modules.')
        return 2

    all_rows = [json.loads(line) for line in (VER / 'machine-decl-graph.jsonl')
                .read_text(encoding='utf-8').splitlines() if line.strip()]
    by_name = {r['name']: r for r in all_rows}
    participating = set(plan['participating_modules'])
    sourced = [r for r in all_rows if r['module'] in participating and r['startLine'] > 0]
    units = {}
    unit_for_name = {}
    structural = []
    for module, facts in facts_by_module.items():
        for fact in facts:
            if fact['kind'] != 'decl':
                continue
            uid = module + ':' + str(fact['declStart']['offset'])
            units[uid] = {'id': uid, 'module': module, 'fact': fact, 'rows': [],
                          'type_units': set(), 'value_units': set()}
        # Keep a shadow index of all sourced commands. A reused theorem can
        # become a closed Def-embedded proof later; its proof dependencies
        # must then be recoverable even though initial reachability cut it.
        for row in (r for r in sourced if r['module'] == module):
            matches = [u for u in units.values() if u['module'] == module
                       and u['fact']['declStart']['line'] <= row['startLine']
                       <= u['fact']['declEnd']['line']]
            # Official Stage 2 deliberately leaves notation/macro commands out.
            # Such spans are preserved, never guessed to be deletable declarations.
            if not matches:
                structural.append(row)
                continue
            assert len(matches) == 1, (row['name'], [u['id'] for u in matches])
            unit = matches[0]
            unit['rows'].append(row)
            unit_for_name[row['name']] = unit['id']
    units = {k: u for k, u in units.items() if u['rows']}

    generated_cache = {}
    private_reference_names = {}
    for row in sourced:
        prefix='_private.'+row['module']+'.'
        if row['isPrivate'] and row['name'].startswith(prefix):
            private_reference_names[(row['module'],'_private.'+row['name'][len(prefix):])]=row['name']

    def provided_units(name, active=None):
        if name in unit_for_name:
            return {unit_for_name[name]}
        if name in generated_cache:
            return generated_cache[name]
        if name not in by_name or by_name[name]['startLine'] > 0:
            return set()
        active = set() if active is None else active
        if name in active:
            return set()
        row = by_name[name]
        found = set()
        for dep in row['typeDeps'] + row['valueDeps']:
            found.update(provided_units(dep, active | {name}))
        # Cache only top-level traversals: a cycle-cut nested result is partial.
        if not active:
            generated_cache[name] = found
        return found

    for uid, unit in units.items():
        fact = unit['fact']
        name_text=fact['nameText'].removeprefix('_root_.') if fact['nameText'] else None
        candidates = [r for r in unit['rows'] if name_text and
                      (r['userName'] == name_text or
                       r['userName'].endswith('.' + name_text))]
        if not candidates:
            candidates = [r for r in unit['rows'] if r['isInstance']]
        if not candidates:
            candidates = unit['rows']
        primary = min(candidates, key=lambda r: (len(r['userName']), r['userName']))
        unit['primary'] = primary['name']
        unit['is_theorem'] = primary['kind'] == 'theorem'
        unit['private'] = primary['isPrivate']
        unit['is_instance'] = any(r['isInstance'] for r in unit['rows'])
        unit['proof_lines'] = (fact['declEnd']['line'] - fact['valStart']['line']
                               if fact['valStart'] is not None else None)
        for row in unit['rows']:
            for dep in row['typeDeps']:
                unit['type_units'].update(provided_units(dep))
            for dep in row['valueDeps']:
                unit['value_units'].update(provided_units(dep))
            if row['kind']=='inductive':
                for ctor in all_rows:
                    if ctor['kind']=='ctor' and row['name'] in ctor['typeDeps']:
                        unit['type_units'].update(provided_units(ctor['name']))
        # Source tactics can mention a theorem that disappears from the final
        # kernel proof (e.g. a simp rule producing reflexivity). Its declaration
        # is nevertheless required to re-elaborate the transplanted source.
        # Use exact resolved references from the official oracle, never text.
        for ref in facts_by_module[unit['module']]:
            if ref['kind']!='ref':continue
            first,last=ref['start']['offset'],ref['end']['offset']
            if not (fact['declStart']['offset']<=first and last<=fact['declEnd']['offset']):continue
            name=private_reference_names.get((unit['module'],ref['const']),ref['const'])
            target=(unit['type_units'] if fact['valStart'] is None or first<fact['valStart']['offset']
                    else unit['value_units'])
            target.update(provided_units(name))
        unit['type_units'].discard(uid)
        unit['value_units'].discard(uid)

    accepted = plan.get('accepted_library_nodes', plan['reusable_accepted_nodes'])
    all_reuse_units = {unit_for_name[name]: name for name in accepted if name in unit_for_name}
    reuse_definitions = {}
    reuse_definition_path=VER/'machine-definition-reuse.json'
    if not MODEL_ONLY and reuse_definition_path.exists():
        definition_reuse=json.loads(reuse_definition_path.read_text(encoding='utf-8'))
        assert definition_reuse['approved']
        for module,record in definition_reuse['modules'].items():
            assert record['native_sha256']==sha(HERE/'machine/lean'/Path(*module.split('.')).with_suffix('.lean'))
            providers=record.get('providers',[record])
            for provider in providers:
                assert provider['public_sha256']==sha(ROOT/Path(*provider['definition_module'].split('.')).with_suffix('.lean'))
        for uid,unit in units.items():
            if unit['primary'] in definition_reuse['definitions']:
                if definition_reuse.get('schema_version',1)>=2:
                    assert all(r['name'] in definition_reuse['definitions'] for r in unit['rows']), ('partial source-command reuse',uid)
                reuse_definitions[uid]=definition_reuse['definitions'][unit['primary']]
    context_path=VER/'machine-scope-contexts.json'
    contexts=({c['module']:c for c in json.loads(context_path.read_text(encoding='utf-8'))}
              if context_path.exists() else {})
    diagnostic_kinds={'Lean.Parser.Command.printAxioms','Lean.Parser.Command.print',
                      'Lean.Parser.Command.check','Lean.Parser.Command.eval',
                      'Lean.Parser.Command.reduce','Lean.Parser.Command.synth'}
    context_roots = set()
    macro_dependencies_path=VER/'machine-macro-context-dependencies.json'
    if macro_dependencies_path.exists():
        for record in json.loads(macro_dependencies_path.read_text(encoding='utf-8')):
            if record['module'] not in participating:continue
            for name in record['dependencies']:
                if name in by_name and by_name[name]['module'] in participating:
                    context_roots.add(name)
    for module, facts in facts_by_module.items():
        spans = [(f['declStart']['offset'], f['declEnd']['offset']) for f in facts if f['kind']=='decl']
        private_lookup = {}
        for row in sourced:
            if row['module']==module and row['isPrivate']:
                prefix='_private.'+module+'.'
                if row['name'].startswith(prefix):
                    private_lookup['_private.'+row['name'][len(prefix):]]=row['name']
        for fact in facts:
            if fact['kind']!='ref':continue
            if any(a<=fact['start']['offset']<b for a,b in spans):continue
            if any(c['syntaxKind'] in diagnostic_kinds
                   and c['startOffset']<=fact['start']['offset']<c['endOffset']
                   for c in contexts.get(module,{}).get('commands',[])):
                continue
            name=private_lookup.get(fact['const'],fact['const'])
            if name in by_name and by_name[name]['module'] in participating:
                context_roots.add(name)
    roots=set()
    for name in plan['roots']+plan['instance_roots']+sorted(context_roots):
        roots.update(provided_units(name))
    live=set()
    todo=list(roots)
    while todo:
        uid=todo.pop()
        if uid in live:continue
        live.add(uid)
        todo.extend(units[uid]['type_units'])
        if uid not in all_reuse_units and uid not in reuse_definitions:
            todo.extend(units[uid]['value_units'])

    # Definitions carry their proof-side dependencies, with proofs, so no Def
    # ever imports a sorry-bearing theorem stub. Structure-generated accessors
    # are already part of the same command unit and cannot be duplicated.
    bundles = {uid for uid in live if units[uid]['is_instance']
               or (not units[uid]['is_theorem'] and not units[uid]['private'])}
    bundles.update(set(reuse_definitions) & live)
    for name in context_roots:
        bundles.update(provided_units(name))
    todo = list(bundles)
    while todo:
        uid = todo.pop()
        if uid in reuse_definitions:continue
        for dep in units[uid]['type_units'] | units[uid]['value_units']:
            if dep not in bundles:
                bundles.add(dep)
                todo.append(dep)

    live.update(bundles)
    all_units=units
    units={uid:all_units[uid] for uid in live}

    target_units = {unit_for_name[name] for name in plan['roots']}
    reuse_units = {uid:name for uid,name in all_reuse_units.items() if uid in units and uid not in bundles}
    assert not (target_units & bundles), 'A target is embedded in definition material'
    nodes = target_units | set(reuse_units)
    type_needed = set().union(*(units[uid]['type_units'] for uid in nodes))
    reasons = defaultdict(list)
    for uid, u in units.items():
        if uid in bundles:
            continue
        if not u['is_theorem']:
            continue
        if uid in target_units:
            reasons[uid].append('target')
        if uid in reuse_units:
            reasons[uid].append('already accepted platform node')
        if u['private'] and uid not in type_needed:
            continue
        length = u['proof_lines']
        assert length is not None, (uid, 'theorem has no official value span')
        if uid in type_needed:
            nodes.add(uid)
            reasons[uid].append('required by another declaration statement')
        if length > 40:
            nodes.add(uid)
            reasons[uid].append('proof exceeds 40 lines')
        elif 10 < length <= 40:
            if u['fact']['docstring'] is not None:
                nodes.add(uid)
                reasons[uid].append('11-40 lines and documented')
            if any(uid in other['value_units'] and other['module'] != u['module']
                   for other in units.values()):
                nodes.add(uid)
                reasons[uid].append('11-40 lines and used across modules')

    def inline_closure(root, current_nodes):
        if root in reuse_units:
            return set(), units[root]['value_units'] & set(reuse_units)
        helpers, children = set(), set()
        todo = list(units[root]['type_units'] | units[root]['value_units'])
        while todo:
            uid = todo.pop()
            if uid in reuse_definitions:continue
            if uid == root or uid in bundles:
                continue
            if uid in current_nodes:
                children.add(uid)
                continue
            if uid in helpers:
                continue
            helpers.add(uid)
            todo.extend(units[uid]['type_units'] | units[uid]['value_units'])
        return helpers, children

    while True:
        old_nodes, old_bundles = set(nodes), set(bundles)
        type_needed = set().union(*(units[uid]['type_units'] for uid in nodes))
        todo = list(type_needed)
        visited = set()
        while todo:
            uid = todo.pop()
            if uid in visited or uid in bundles:
                continue
            visited.add(uid)
            if units[uid]['is_theorem']:
                nodes.add(uid)
                reasons[uid].append('required by a node statement')
                todo.extend(units[uid]['type_units'])
            else:
                bundles.add(uid)
        todo = list(bundles)
        while todo:
            uid = todo.pop()
            if uid in reuse_definitions:continue
            for dep in all_units[uid]['type_units'] | all_units[uid]['value_units']:
                if dep not in bundles:
                    bundles.add(dep)
                    units[dep]=all_units[dep]
                    todo.append(dep)
        assert not (target_units & bundles), 'A target is embedded in definition material'
        nodes.difference_update(bundles)
        consumers = defaultdict(set)
        for uid in nodes:
            helpers, _ = inline_closure(uid, nodes)
            for helper in helpers:
                consumers[helper].add(uid)
        promoted = {uid for uid, users in consumers.items() if len(users) >= 2
                    and units[uid]['is_theorem'] and not units[uid]['private']
                    and 10 < units[uid]['proof_lines'] <= 40}
        promoted.difference_update(nodes)
        if not promoted and old_nodes == nodes and old_bundles == bundles:
            break
        for uid in promoted:
            reasons[uid].append('11-40 lines and used by at least two node proofs')
        nodes.update(promoted)

    graph = {}
    for uid, u in units.items():
        if uid in reuse_definitions:
            kind = 'reuse-definition'
            u['reuse_definition']=reuse_definitions[uid]
        elif uid in bundles:
            kind = 'def-embedded-theorem' if u['is_theorem'] else 'def-material'
        elif uid in reuse_units:
            kind = 'reuse-node'
        elif uid in nodes:
            kind = 'node'
        else:
            kind = 'inline-helper'
        u['classification'] = kind
        u['reasons'] = reasons[uid]
        u['deprivatize'] = u['private'] and (uid in bundles or uid in type_needed)
        if uid in nodes:
            helpers, children = inline_closure(uid, nodes)
            u['inline_units'] = sorted(helpers)
            u['child_nodes'] = sorted(children)
            graph[uid] = set(children)

    # Deterministic leaves-first order. Reject an unexpected cycle before any
    # immutable publication, rather than silently breaking a real dependency.
    order = []
    remaining = {k: set(v) for k, v in graph.items()}
    while remaining:
        ready = sorted(k for k, v in remaining.items() if not v)
        assert ready, ('node dependency cycle', sorted(remaining)[:12])
        order.extend(ready)
        for k in ready:
            del remaining[k]
        for v in remaining.values():
            v.difference_update(ready)

    for u in units.values():
        u['type_units'] = sorted(u['type_units'] & units.keys())
        u['value_units'] = sorted(u['value_units'] & units.keys())
        u['names'] = [r['name'] for r in u.pop('rows')]
    counts = dict(Counter(u['classification'] for u in units.values()))
    result = {'stage': 'classification complete; generation and exact-type validation pending',
              'public_source_repository': plan['public_source_repository'],
              'public_source_commit': plan['public_source_commit'],
              'source_path_mapping': plan['source_path_mapping'],
              'oracle_sha256': oracle_sha,
              'declaration_graph_sha256': sha(VER / 'machine-decl-graph.jsonl'),
              'module_receipts': receipts, 'classification_counts': counts,
              'roots': plan['roots'], 'units': units, 'node_topological_order': order,
              'context_reference_roots': sorted(context_roots),
              'preserved_structural_declarations': structural,
              'source_generated': False, 'platform_uploaded': False}
    output_name=('model-node-classification.json' if MODEL_ONLY else 'machine-node-classification.json')
    if '--output' in sys.argv:
        output_name=sys.argv[sys.argv.index('--output')+1]
        assert Path(output_name).name==output_name
    (VER / output_name).write_text(
        json.dumps(result, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
    print('Classified:', counts, 'nodes in upload order:', len(order))
    return 0


if __name__ == '__main__':
    sys.exit(main())
