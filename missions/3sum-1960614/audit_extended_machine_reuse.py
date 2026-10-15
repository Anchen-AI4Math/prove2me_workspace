"""Conservative public reuse audit over compiler CIs and official source units.

Matching constants are dependency-closed and entire source commands are atomic.
This report is a preview; it never overwrites the approved reuse manifest.
"""
from collections import Counter, defaultdict
from bisect import bisect_left, bisect_right
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
VER = HERE / 'verification'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}


def digest(value):
    return hashlib.sha256(value.encode()).hexdigest()


def read(name):
    return json.loads((VER / name).read_text(encoding='utf-8'))


def jsonlines(name):
    with (VER / name).open(encoding='utf-8') as handle:
        return [json.loads(line) for line in handle if line.strip()]


def main():
    index = read('extended-reuse-compact-index.json')
    native, public = index['native'], index['public']
    rows = {r['name']: r for r in jsonlines('machine-decl-graph.jsonl')}
    matchers = set(read('machine-native-matchers.json'))
    seed = read('machine-definition-reuse.json')
    old_native = {r['name']: r for r in jsonlines('reuse-interfaces-native.jsonl')}
    old_public = {r['name']: r for r in jsonlines('reuse-interfaces-platform.jsonl')}
    direct, overrides = set(), []
    for name, left in native.items():
        right = public.get(name)
        if right is None or left['kind'] in ('axiom', 'quot'):
            continue
        if any(left[k] != right[k] for k in ('kind', 'universeCount', 'type_sha256', 'shape')):
            continue
        if not set(left['axioms']) <= STANDARD or not set(right['axioms']) <= STANDARD:
            continue
        if left['isProof'] or left['value_sha256'] == right['value_sha256']:
            direct.add(name)
            continue
        # Inherit a separately checked equality only for these exact snapshots.
        protected = seed['definitions'].get(name, {}).get('check') == 'kernel-definitional-equality'
        if not protected or name not in old_native or name not in old_public:
            continue
        if all(ci['raw_type_sha256'] == digest(old['type'])
               and ci['raw_value_sha256'] == digest(old['value'])
               for ci, old in ((left, old_native[name]), (right, old_public[name]))):
            direct.add(name)
            overrides.append(name)

    # Exact public theorem statements were elaborated independently against the
    # public data environment. A proved theorem may be reused by its type.
    theorem_types = VER / 'public-theorem-probe-types.json'
    catalog = {r['theorem_name']: r for r in read('machine-public-1962-catalog.json')['records']}
    theorem_candidates = set()
    if theorem_types.exists():
        for ci in read(theorem_types.name):
            name = ci['name']
            if name not in native or catalog[name]['status'] != 'Proved':
                continue
            if native[name]['kind'] != 'theorem':
                continue
            if ci['universeCount'] == native[name]['universeCount'] and digest(ci['type']) == native[name]['type_sha256']:
                direct.add(name)
                theorem_candidates.add(name)

    expand_cache = {}

    def expand_dependency(name, active=frozenset()):
        if name not in matchers or name not in rows:
            return {name}
        if name in active:
            return set()
        if name in expand_cache:
            return expand_cache[name]
        found = set()
        for dep in rows[name]['typeDeps'] + rows[name]['valueDeps']:
            found.update(expand_dependency(dep, active | {name}))
        if not active:
            expand_cache[name] = found
        return found

    constructors = defaultdict(set)
    for name, ci in native.items():
        if ci['kind'] == 'ctor':
            constructors[ci['shape']['induct']].add(name)
    requirements = {}
    for name in direct:
        row, ci = rows[name], native[name]
        deps = set(row['typeDeps'])
        if not ci['isProof']:
            deps.update(row['valueDeps'])
        deps.update(constructors[name])
        if ci['kind'] in ('inductive', 'recursor'):
            deps.update(ci['shape'].get('all', []))
        expanded = set()
        for dep in deps:
            expanded.update(expand_dependency(dep))
        requirements[name] = (expanded & set(rows)) - {name}

    # Couple every sourced member of one official declaration command. A
    # structure cannot be imported while its new field/projector is relocated.
    plan = read('machine-upload-plan.json')
    units, pending, covered = {}, [], set()
    facts_by_module, spans_by_module = {}, defaultdict(list)
    oracle_hash = hashlib.sha256((ROOT / 'scripts/extract_sketch_info.lean').read_bytes()).hexdigest()
    source_by_module = defaultdict(list)
    for row in rows.values():
        if row['startLine'] > 0:
            source_by_module[row['module']].append(row)
    for module in plan['participating_modules']:
        stem = module.replace('.', '_')
        receipt_path = VER / 'sketch-oracles' / (stem + '.receipt.json')
        source = HERE / 'machine/lean' / Path(*module.split('.')).with_suffix('.lean')
        if not receipt_path.exists():
            pending.append(module)
            continue
        receipt = json.loads(receipt_path.read_text(encoding='utf-8'))
        if receipt.get('exit_code') != 0 or receipt['oracle_sha256'] != oracle_hash or receipt['source_sha256'] != hashlib.sha256(source.read_bytes()).hexdigest():
            pending.append(module)
            continue
        facts = jsonlines('sketch-oracles/' + stem + '.jsonl')
        facts_by_module[module] = facts
        for fact in facts:
            if fact['kind'] != 'decl':
                continue
            names = {r['name'] for r in source_by_module[module]
                     if fact['declStart']['line'] <= r['startLine'] <= fact['declEnd']['line']}
            if not names:
                continue
            unit_id = module + ':' + str(fact['declStart']['offset'])
            assert not names & covered, (unit_id, names & covered)
            covered.update(names)
            units[unit_id] = names
            spans_by_module[module].append((fact['declStart']['offset'], fact['declEnd']['offset'], unit_id))

    # Field notation searches the receiver type's namespace, independent of
    # the current/open namespace (Lean.Elab.Term.findMethod?). Reusing a type
    # while relocating a needed unpublished method breaks source elaboration.
    # Keep that type and its dependents in the native upload namespace instead.
    contexts = {r['module']: r for r in read('machine-scope-contexts.json')}
    private_refs = {}
    for row in rows.values():
        prefix = '_private.' + row['module'] + '.'
        if row['isPrivate'] and row['name'].startswith(prefix):
            private_refs[(row['module'], '_private.' + row['name'][len(prefix):])] = row['name']
    receiver_conditions = []
    for module, facts in facts_by_module.items():
        commands = contexts[module]['commands']
        pairs = sorted((i['startOffset'], i['endOffset']) for cmd in commands for i in cmd.get('lexicalIdentifiers', []))
        starts = [a for a, b in pairs]
        max_ends, maximum = [], -1
        for first, last in pairs:
            maximum = max(maximum, last)
            max_ends.append(maximum)
        dots = {(i['startOffset'], i['endOffset']) for cmd in commands for i in cmd.get('dotSelectors', [])}
        spans = sorted(spans_by_module[module])
        span_starts = [a for a, b, uid in spans]
        for ref in facts:
            if ref['kind'] != 'ref':
                continue
            first, last = ref['start']['offset'], ref['end']['offset']
            j = bisect_left(starts, first) - 1
            if (first, last) not in dots and not (j >= 0 and max_ends[j] >= last):
                continue
            name = private_refs.get((module, ref['const']), ref['const'])
            row = rows.get(name)
            if row is None or row['kind'] == 'ctor':
                continue
            parent = row['userName'].rsplit('.', 1)[0]
            if parent not in native or native[parent]['isProof']:
                continue
            j = bisect_right(span_starts, first) - 1
            if j >= 0 and last <= spans[j][1]:
                receiver_conditions.append((spans[j][2], name, parent))

    compatible = set(direct)
    # The uploader reuses one existing theorem per source unit. Multi-member
    # commands are reusable as closed Def material only when every member is
    # actually present in the public definition environment.
    for members in units.values():
        if len(members) > 1 and not members <= set(public):
            compatible.difference_update(members & theorem_candidates)
    removed_dependencies, removed_atomic, removed_receivers = {}, {}, {}
    while True:
        bad = {n: sorted(requirements[n] - compatible) for n in compatible if requirements[n] - compatible}
        atomic = {}
        for uid, members in units.items():
            if members & compatible and not members <= compatible:
                atomic[uid] = sorted(members - compatible)
        removed = set(bad)
        for uid in atomic:
            removed.update(units[uid] & compatible)
        for uid, method, parent in receiver_conditions:
            if parent in compatible and method not in compatible and not units[uid] <= compatible:
                removed.add(parent)
                removed_receivers.setdefault(parent, set()).add(method)
        if not removed:
            break
        removed_dependencies.update(bad)
        removed_atomic.update(atomic)
        compatible.difference_update(removed)

    # Missing official receipts make this a preview, never approval evidence.
    result = {
        'not_approved': True,
        'all_participating_units_available': not pending,
        'pending_modules': pending,
        'direct_candidates': len(direct),
        'compatible_count': len(compatible),
        'compatible_names': sorted(compatible),
        'compatible_source_names': sorted(compatible & covered),
        'compatible_unit_count': sum(names <= compatible for names in units.values()),
        'compatible_units': {uid: sorted(names) for uid, names in units.items() if names <= compatible},
        'atomic_unit_count': len(units),
        'atomic_rejections': removed_atomic,
        'dependency_rejections': removed_dependencies,
        'receiver_namespace_rejections': {n: sorted(methods) for n, methods in sorted(removed_receivers.items())},
        'compatible_kind_counts': dict(Counter(native[n]['kind'] for n in compatible)),
        'kernel_checked_overrides': sorted(overrides),
        'public_theorem_candidate_count': len(theorem_candidates),
        'compatible_public_theorems': {n: catalog[n] for n in sorted(compatible & theorem_candidates)},
        'evidence': {name: hashlib.sha256((VER / name).read_bytes()).hexdigest() for name in
                     ('extended-reuse-compact-index.json', 'machine-decl-graph.jsonl', 'machine-native-matchers.json')},
        'method': 'Compiler type/value/ABI equality, protected kernel witnesses, standard axioms, matcher-only dependency expansion, transitive dependency closure, atomic official source commands, and receiver-namespace compatibility for retained source methods.'
    }
    path = VER / 'extended-reuse-atomic-audit.json'
    path.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print('Atomic compatible CIs:', len(compatible), '; complete units:', result['compatible_unit_count'])
    print('Proved public nodes compatible:', len(result['compatible_public_theorems']), '; pending modules:', len(pending))
    print('Preview only; active reuse manifest unchanged.')


if __name__ == '__main__':
    main()
