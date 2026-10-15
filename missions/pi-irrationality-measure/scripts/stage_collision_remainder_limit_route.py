"""Pure source-only AP19 next limit leaf; no compiler or publication actions."""
from __future__ import annotations
import argparse, json
from pathlib import Path
import stage_analytic_remainder_data_provider as data

TASK, V, SELF = data.TASK, data.V, Path(__file__).resolve()
STAGE = V / 'ap19/collision-remainder-limit-route'
TARGET = 'OAI.PiExponent.tendsto_collisionRemainder_of_normalized_pow'
PARENT = 'OAI.PiExponent.tendsto_log_div_of_normalized_pow'
PARENT_MODULE = 'Theorems.Thm_OAI_PiExponent_tendsto_log_div_of_normalized_pow'
PARENT_STAGE = V / 'nodes-preview/OAI_PiExponent_tendsto_log_div_of_normalized_pow'
IMPORTS = ['Mathlib.Analysis.SpecialFunctions.Log.Basic',
           'Mathlib.Analysis.SpecificLimits.Normed',
           'Mathlib.Analysis.Asymptotics.SpecificAsymptotics',
           'Mathlib.Tactic.Ring', data.PLATFORM_MODULE]
SPECS = [('OAI.PiExponent.tendsto_log_add_div_of_normalized_pow', 1069, 1461),
         (TARGET, 2609, 3065)]
read, sha, encode, need, rel = data.read, data.sha, data.encode, data.need, data.rel


def source_units():
    ast, scopes = read(data.base.AST), read(data.base.SCOPES)
    graph = {r['name']: r for r in map(json.loads, data.base.GRAPH.read_text(encoding='utf-8').splitlines())}
    owners = {r['source_name']: r for r in read(data.base.OWNERS)['owners']}
    pub = read(PARENT_STAGE / 'publication.json'); body = pub['target_readback']['body']
    theorem = next(PARENT_STAGE.glob('Thm_*.lean')); solution = next(PARENT_STAGE.glob('Sol_*.lean'))
    need(pub['theorem_id'] == '8b1c0341-2978-4a9d-8acc-8a5e3538cbda'
         and pub['submission_id'] == '43b585ea-75ce-438e-b485-11d72ec49ee8'
         and body['status'] == 'Proved' and body['theorem_name'] == PARENT
         and pub['last_verify_verdict']['body']['status'] == 'ACCEPTED'
         and (body['preamble'] + body['formal_statement']).encode() == theorem.read_bytes()
         and sha(solution) == pub['verify_intent']['solution_sha256'],
         'Actual Accepted LogDiv public wire/proof differs')
    need('theorem ' not in body['preamble'] and 'def ' not in body['preamble'],
         'Accepted LogDiv public preamble provides extra declarations')
    pins = {rel(p): sha(p) for p in [SELF, data.base.AST, data.base.SCOPES,
        data.base.GRAPH, data.base.OWNERS, PARENT_STAGE/'publication.json',
        PARENT_STAGE/'validation.json', theorem, solution,
        data.STAGE/'preparation.json', data.STAGE/data.PROVIDER_FILE]}
    rows = []
    for name, start, end in SPECS:
        module = next(m for m in ast['modules'] if any(name in u['graph_names'] for u in m['units']))
        unit = next(u for u in module['units'] if name in u['graph_names'])
        source = TASK/('port/lean/'+module['module'].replace('.', '/')+'.lean')
        original = TASK/('source/lean/'+module['module'].replace('.', '/')+'.lean')
        raw = source.read_bytes(); command = raw[start:end]
        sm = next(m for m in scopes['modules'] if m['source'] == module['module'].replace('.', '/')+'.lean')
        scope = next(s for s in sm['declarations'] if s['verified_name'] == name)
        contexts = [raw[c['range']['start']['offset']:c['range']['end']['offset']].decode()
                    for c in scope['context_commands']]
        expected = ['open Filter Topology', 'open scoped BigOperators'] if name != TARGET else ['open scoped BigOperators Topology', 'open Filter']
        need([unit['start']['offset'], unit['end']['offset']] == [start, end]
             and unit['graph_names'] == [name] and unit['graph_kinds'] == ['theorem']
             and unit['privateTok'] is None and not unit['is_instance_command']
             and not unit['is_local_instance'] and contexts == expected
             and scope['namespace'] == 'OAI.PiExponent'
             and all(s['kind'] == 'namespace' for s in scope['scope_stack'])
             and module['source_sha256'] == sm['source_sha256'] == sha(source)
             and owners[name]['source_sha256'] == sha(source)
             and original.read_bytes().replace(b'\r\n', b'\n').count(command.replace(b'\r\n', b'\n')) == 1,
             'Original two proof AST/scope/owner differs: '+name)
        rows.append({'name': name, 'module': module['module'], 'start': start, 'end': end,
            'source_lines': [unit['start']['line'], unit['end']['line']], 'ast': unit,
            'scope': scope, 'contexts': contexts, 'graph': graph[name], 'owner': owners[name],
            'source': rel(source), 'source_sha256': sha(source), 'original': rel(original),
            'original_sha256': sha(original), 'command_sha256': data.sha_bytes(command),
            'proof_suffix_sha256': data.sha_bytes(command[unit['valueStart']['offset']-start:]),
            'bytes': command})
        pins[rel(source)] = sha(source); pins[rel(original)] = sha(original)
    boundary = {PARENT, data.NAMES[0], data.NAMES[1]}; reached = set(); todo = [TARGET]
    while todo:
        n = todo.pop()
        if n in reached: continue
        need(n in graph, 'Unknown actual project CI: '+n); reached.add(n)
        if n not in boundary: todo += graph[n]['typeDeps'] + graph[n]['valueDeps']
    need(reached - boundary == {r['name'] for r in rows} and len(reached) == 5,
         'Two-proof stop-boundary closure differs')
    return rows, pins, reached


def files():
    rows, pins, closure = source_units(); target = rows[-1]; command = target['bytes']
    a = target['ast']['nameRange']['start']['offset'] - target['start']
    b = target['ast']['nameRange']['end']['offset'] - target['start']
    value = target['ast']['valueStart']['offset'] - target['start']
    need(command[value:value+5] == b':= by', 'Original proof delimiter differs')
    preamble = (''.join('import '+m+'\n' for m in IMPORTS)
                +'\nopen scoped BigOperators Topology\nopen Filter\nopen OAI.PiExponent\n\n').encode()
    formal = command[:a]+TARGET.encode()+command[b:value]+b':= by\n  sorry\n'
    helper = rows[0]
    solution = (''.join('import '+m+'\n' for m in IMPORTS+[PARENT_MODULE])+'\n').encode()
    solution += ('namespace OAI.PiExponent\n\n'+'\n'.join(helper['contexts'])+'\n\n').encode()
    solution += helper['bytes']+b'\n\nend OAI.PiExponent\n\n'
    solution += b'open scoped BigOperators Topology\nopen Filter\nopen OAI.PiExponent\n\n'
    solution += command[:a]+b'solution'+command[b:]+b'\n'
    metadata = {'theorem_title': 'Vanishing collision remainder for polynomially normalized counts',
        'natural_language_statement': r'Let $M:\mathbb R\to\mathbb N$, $d\in\mathbb N$, and $L>0$. Suppose $M(H)/H^d\to L$ as $H\to+\infty$. For the original collision ratio $r=\exp(-\log 2/2)$, the collision remainder satisfies'+'\n\n'+r'$$\frac{\log M(H)+\log 2/4-\log(1-r)}{H}\longrightarrow0.$$'+'\n\n'+'This generic limit is the collision-remainder child used by the original analytic aggregate proof.',
        'source': 'https://github.com/openai/math/blob/'+data.COMMIT+'/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean#L56-L64',
        'tags': ['asymptotics','number-theory','openai-pi-exponent-017']}
    result = {'candidate/Target.lean': preamble+formal, 'candidate/Sol.lean': solution,
              'candidate/preamble.lean': preamble, 'candidate/formal-statement.lean': formal,
              'metadata.json': encode(metadata)}
    for i, row in enumerate(rows, 1): result[f'source-unit-{i}.lean'] = row['bytes']
    result['route-preparation.json'] = encode({'schema_version': 1,
        'artifact_kind': 'ap19-collision-remainder-limit-source-only-route',
        'target': TARGET, 'source_commit': data.COMMIT, 'source_line_count': 15,
        'exact_source_units': [{k:v for k,v in r.items() if k!='bytes'} for r in rows],
        'source_closure': sorted(closure), 'literal_original_proof_suffixes': True,
        'accepted_parent': {'name': PARENT, 'theorem_id': '8b1c0341-2978-4a9d-8acc-8a5e3538cbda',
            'proof_id': '43b585ea-75ce-438e-b485-11d72ec49ee8', 'module': PARENT_MODULE},
        'public_stop_boundaries': [PARENT, data.NAMES[0], data.NAMES[1]],
        'pending_gates': ['Actual Published AP19 four-Def readback and full-Def certificate',
                         'Actual closed original-name Accepted LogDiv local mirror and strict boundary certificate'],
        'candidate_requires_pending_server_import_interfaces': True,
        'MatrixCounting_tendsto_rowCount_normalized_is_not_public_AP11_boundary': True,
        'tendsto_nat_add_one_div_pow_not_used_in_this_chain': True,
        'input_hashes': pins, 'files': {p:data.sha_bytes(raw) for p,raw in result.items()},
        'validated': False, 'submission_ready': False, 'proposal_status': 'Draft',
        'Lean_started': False, 'API_used': False})
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument('--prepare', action='store_true'); modes.add_argument('--check-only', action='store_true')
    args = parser.parse_args(); outputs = files()
    for path, raw in outputs.items():
        output = STAGE/path
        if output.exists(): need(output.read_bytes() == raw, 'Refusing changed route output: '+path)
        elif args.prepare: output.parent.mkdir(parents=True, exist_ok=True); output.write_bytes(raw)
        else: need(False, 'Route output missing: '+path)
    print(json.dumps({'checked_files': len(outputs), 'source_proof_count': 2,
        'source_line_count': 15, 'validated': False, 'Lean_started': False, 'API_used': False}, indent=2))


if __name__ == '__main__': main()
