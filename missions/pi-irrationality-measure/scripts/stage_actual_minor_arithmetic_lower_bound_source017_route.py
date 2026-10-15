"""Pure AP17 source-only route to the existing arithmetic-minor Open target."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import stage_selected_minor_arithmetic_lower_bound_route as lower

TASK, ROOT, V = lower.TASK, lower.ROOT, lower.V
SELF = Path(__file__).resolve()
STAGE = V / 'ap17/actual-minor-arithmetic-lower-bound'
COMMIT = lower.COMMIT
AST, SCOPES, GRAPH = lower.AST, lower.SCOPES, lower.GRAPH
SOURCE_MODULE = 'OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction'
PREFIX = 'OAI.PiExponent.DeterminantContradiction.'
SOURCE_NAME = PREFIX + 'actual_minor_arithmetic_lower_bound'
PLATFORM_NAME = SOURCE_NAME + '_source017'
TARGET_ID = '15c55202-44da-420f-bf88-f910c0e7060c'
TARGET_RANGE = [3210, 3998]
SOURCE_SHORTS = ['finiteDenominators_two_le', 'logWeights_eq',
                 'actual_minor_arithmetic_lower_bound']
OPEN_RECORD = V / 'graph-no-fixed-data-route-20261011-v2/publication-v3/pre-verify-readbacks/arithmetic.json'
OPEN_WIRE = V / 'graph-no-fixed-data-route-20261011-v2/publication-v3/arithmetic-open-wire.lean'
PUBLICATION = V / 'graph-no-fixed-data-route-20261011-v2/publication-v3/publication.json'
GENERIC_LOWER = lower.TARGET
read, sha, sha_bytes, encode, need, rel = lower.read, lower.sha, lower.sha_bytes, lower.encode, lower.need, lower.rel


def saved_public_target():
    actual = read(OPEN_RECORD)
    publication = read(PUBLICATION)
    preamble, formal = actual['preamble'], actual['formal_statement']
    need(actual['theorem_id'] == publication['arithmetic_theorem_id'] == TARGET_ID
         and actual['theorem_name'] == publication['arithmetic_source017_name'] == PLATFORM_NAME
         and actual['status'] == 'Open'
         and actual['mathlib_rev'] == '0df444a360eaa60ab8c11dca51a86af692955474'
         and publication['last_arithmetic_publish_verdict']['body']['status'] == 'PUBLISHED'
         and (preamble + formal).encode() == OPEN_WIRE.read_bytes()
         and 'FixedDeterminantFamily' not in (preamble + formal),
         'Saved public Open target identity, exact wire, or provenance differs')
    return actual


def source_units():
    lower.check_only()
    actual = saved_public_target()
    det = lower.clearing.base.ap10.config('determinant')
    detstage = det['stage']
    detcert = detstage / 'actual-provider-validation-helper-v2.json'
    detpub = detstage / 'publication-helper-v2/publication.json'
    cert, published = read(detcert), read(detpub)
    need(cert['validated'] is True and cert['Std3_only'] is True
         and cert['platform_module'] == det['platform_module']
         and cert['provided_names'] == det['names']
         and published['last_publish_verdict']['body']['status'] == 'PUBLISHED'
         and published['target_readback']['body']['status'] == 'Definition'
         and published['target_readback']['body']['definition'].encode()
             == (detstage / det['provider_file']).read_bytes(),
         'Actual Published FixedData/core definitions differ')
    bindings, published_pins, _ = lower.clearing.base.ap10.published_bindings()
    provided = set(bindings) | {GENERIC_LOWER}
    for key in lower.clearing.base.ap10.CONFIGS:
        provided.update(lower.clearing.base.ap10.config(key)['names'])
    for key in lower.clearing.base.ap9.CONFIGS:
        provided.update(lower.clearing.base.ap9.config(key)['names'])
    graph = {r['name']: r for r in map(json.loads,
             GRAPH.read_text(encoding='utf-8').splitlines())}
    closure, pending = set(), [SOURCE_NAME]
    while pending:
        name = pending.pop()
        if name in closure:
            continue
        need(name in graph, 'Unknown actual source graph dependency: ' + name)
        closure.add(name)
        if name not in provided:
            pending += graph[name]['typeDeps'] + graph[name]['valueDeps']
    expected = {PREFIX + short for short in SOURCE_SHORTS}
    need(len(closure) == 41 and closure - provided == expected
         and GENERIC_LOWER in closure and len(expected) == 3,
         'Actual three-original-command reduction differs')
    port = lower.clearing.base.source_path(SOURCE_MODULE)
    original = lower.clearing.base.source_path(SOURCE_MODULE, 'source')
    raw = port.read_bytes()
    orig = original.read_bytes().replace(b'\r\n', b'\n')
    am = next(m for m in read(AST)['modules'] if m['module'] == SOURCE_MODULE)
    sm = next(m for m in read(SCOPES)['modules']
              if m['source'] == SOURCE_MODULE.replace('.', '/') + '.lean')
    need(am['source_sha256'] == sm['source_sha256'] == sha(port),
         'Actual source AST/scope input hash differs')
    rows, commands = [], []
    for short in SOURCE_SHORTS:
        name = PREFIX + short
        unit = next(u for u in am['units'] if name in u['graph_names'])
        scope = next(s for s in sm['declarations'] if s['verified_name'] == name)
        a, b = unit['start']['offset'], unit['end']['offset']
        command = raw[a:b]
        contexts = [raw[c['range']['start']['offset']:c['range']['end']['offset']].decode()
                    for c in scope['context_commands']]
        need(unit['graph_names'] == [name] and unit['graph_kinds'] == ['theorem']
             and unit['privateTok'] is None and not unit['is_instance_command']
             and not unit['is_local_instance'] and scope['namespace'] == PREFIX[:-1]
             and all(c['kind'] == 'namespace' for c in scope['scope_stack'])
             and contexts == ['open Filter', 'open scoped Topology']
             and orig.count(command.replace(b'\r\n', b'\n')) == 1,
             'Original source AST, namespace, context, or proof differs: ' + name)
        rows.append({'name': name, 'module': SOURCE_MODULE, 'kind': 'theorem',
                     'ast': unit, 'scope': scope, 'graph': graph[name],
                     'source': rel(port), 'source_sha256': sha(port),
                     'original': rel(original), 'original_sha256': sha(original),
                     'start': a, 'end': b, 'command_sha256': sha_bytes(command),
                     'original_port_command_equal_modulo_line_endings': True})
        commands.append((a, name, command))
    need(commands == sorted(commands), 'Original source theorem order differs')
    target = rows[-1]
    need([target['start'], target['end']] == TARGET_RANGE,
         'Original target AST byte range differs')
    lines = sum(r['ast']['end']['line'] - r['ast']['start']['line'] + 1 for r in rows)
    need(lines == 17, 'Original three-theorem source line count differs')
    command = commands[-1][2]
    unit = target['ast']
    offset = unit['nameRange']['start']['offset'] - target['start']
    stop = unit['nameRange']['end']['offset'] - target['start']
    value = unit['valueStart']['offset'] - target['start']
    need(command[offset:stop] == b'actual_minor_arithmetic_lower_bound'
         and command[value:value + 5] == b':= by'
         and command.count(b'actual_minor_arithmetic_lower_bound') == 1,
         'Original target has an unexpected name or proof delimiter')
    renamed = command[:offset] + PLATFORM_NAME.encode() + command[stop:]
    formal = renamed[:renamed.index(b':= by')] + b':= by\n  sorry\n'
    need(formal == actual['formal_statement'].encode()
         and (actual['preamble'] + actual['formal_statement']).encode() == OPEN_WIRE.read_bytes()
         and renamed[renamed.index(b':= by'):] == command[value:],
         'Published source017 formal wire is not the single original target-name replacement')
    pins = dict(published_pins)
    for p in [SELF, AST, SCOPES, GRAPH, port, original,
              OPEN_RECORD, OPEN_WIRE, PUBLICATION,
              detstage / 'preparation.json', detstage / det['provider_file'],
              detcert, detpub,
              lower.STAGE / 'route-preparation.json',
              lower.STAGE / 'original-target-command.lean.txt']:
        pins[rel(p)] = sha(p)
    return graph, closure, provided, rows, commands, pins, renamed, actual, det


def stage_files():
    graph, closure, provided, rows, commands, pins, renamed, actual, det = source_units()
    target = commands[-1][2]
    value = rows[-1]['ast']['valueStart']['offset'] - rows[-1]['start']
    result = {'schema_version': 1,
              'artifact_kind': 'ap17-actual-minor-arithmetic-lower-bound-source-route-only',
              'source_commit': COMMIT, 'source_name': SOURCE_NAME,
              'platform_name': PLATFORM_NAME, 'platform_theorem_id': TARGET_ID,
              'saved_public_target_status_at_readback': 'Open',
              'source_module': SOURCE_MODULE,
              'source_graph_closure_names': sorted(closure),
              'actual_provided_names': sorted(closure & provided),
              'inline_exact_source_units': rows,
              'inline_proof_ast_count': 3, 'inline_source_line_count': 17,
              'target_ast': rows[-1]['ast'],
              'target_source_command_sha256': sha_bytes(target),
              'target_proof_suffix_sha256': sha_bytes(target[value:]),
              'target_original_command_equal_modulo_line_endings': True,
              'source017_only_target_name_replaced': True,
              'published_preamble': actual['preamble'],
              'published_formal_statement': actual['formal_statement'],
              'saved_public_wire_sha256': sha(OPEN_WIRE),
              'actual_FixedData_provider_module': det['platform_module'],
              'actual_FixedData_provider_certificate': rel(det['stage'] / 'actual-provider-validation-helper-v2.json'),
              'actual_FixedData_provider_publication': rel(det['stage'] / 'publication-helper-v2/publication.json'),
              'generic_lower_public_boundary_name': GENERIC_LOWER,
              'generic_lower_Accepted_and_closed_mirror_pending': True,
              'final_solution_snapshots_manifests_pending': True,
              'compiled': False, 'Lean_started': False, 'API_used': False,
              'validated': False, 'submission_ready': False,
              'proposal_status': 'Draft', 'input_hashes': pins}
    outputs = {'route-preparation.json': encode(result),
               'original-target-command.lean.txt': target,
               'source017-target-command-preview.lean.txt': renamed,
               'saved-public-open-wire.lean': OPEN_WIRE.read_bytes()}
    for _, name, command in commands:
        outputs['source-units/' + name.replace('.', '_') + '.port.lean.txt'] = command
    return outputs


def check_only():
    outputs = stage_files()
    for name, raw in outputs.items():
        need((STAGE / name).is_file() and (STAGE / name).read_bytes() == raw,
             'Immutable AP17 source-only route differs: ' + name)
    return {'checked_files': len(outputs), 'source_AST_units': 3,
            'source_lines': 17, 'single_source017_target_name_replacement': True,
            'generic_lower_boundary_pending': True,
            'compiler_manifests_created': False,
            'all_original_commands_equal_modulo_line_endings': True,
            'Lean_started': False, 'API_used': False, 'validated': False}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    g = p.add_mutually_exclusive_group(required=True)
    g.add_argument('--prepare', action='store_true')
    g.add_argument('--check-only', action='store_true')
    args = p.parse_args()
    if args.prepare:
        for name, raw in stage_files().items():
            path = STAGE / name
            if path.exists():
                need(path.read_bytes() == raw, 'Refusing overwrite: ' + name)
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(raw)
    print(json.dumps(check_only(), ensure_ascii=False, indent=2))


if __name__ == '__main__':
    main()
