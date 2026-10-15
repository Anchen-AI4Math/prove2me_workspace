"""Pure AP16 source-unit inventory; final proof stage waits for an actual AP15 closed mirror."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import stage_selected_minor_clearing_bound_node as clearing
import stage_shifted_gaussian_node as shifted

TASK, ROOT, V = clearing.TASK, clearing.ROOT, clearing.V
SELF = Path(__file__).resolve()
STAGE = V / 'ap16/selected-minor-arithmetic-lower-bound'
COMMIT = clearing.COMMIT
AST, SCOPES, GRAPH = clearing.AST, clearing.SCOPES, clearing.GRAPH
TARGET_MODULE = clearing.TARGET_MODULE
TARGET = 'OAI.PiExponent.MatrixArithmetic.selectedMinor_arithmetic_lower_bound'
TARGET_SOURCE_RANGE = [17647, 19731]
PUBLISHED_CONSTANT_POS = 'OAI.PiExponent.Arithmetic.lcmConstant_pos'
HELPER_NAMES = {
    clearing.SIMPLEX: ['mem_realWeightedSimplex', 'mem_strictWeightedSimplex'],
    clearing.INTERPOLATION: ['column_mem_iff', 'row_mem_iff',
                             'column_weight_le', 'row_weight_lt'],
    clearing.ARITHMETIC: ['log_lcmUpto_le', 'log_lcm_power_product_le',
                          'log_lcm_floor_product_le',
                          'sum_ceil_truncation_div_le',
                          'truncation_denominator_log_le',
                          'column_log_cost_le', 'sum_exponents_le_weight_div',
                          'row_log_cost_lower',
                          'normalized_arithmetic_bound'],
    TARGET_MODULE: ['log_denominator_le', 'actual_row_card_pos',
                    'ceil_log_weight_pos', 'column_log_cost_le_H',
                    'selected_column_log_cost_le', 'row_weighted_cost_le'],
}
PREFIXES = clearing.PREFIXES
read, sha, sha_bytes, encode, need = clearing.read, clearing.sha, clearing.sha_bytes, clearing.encode, clearing.need
rel = clearing.rel


def published_constant_pos():
    witness, pubpath = shifted.provider()
    need(PUBLISHED_CONSTANT_POS in witness['provided_declarations'],
         'Actual published Arithmetic package did not declare lcmConstant_pos')
    module = clearing.ARITHMETIC
    ast = next(m for m in read(AST)['modules'] if m['module'] == module)
    unit = next(u for u in ast['units'] if PUBLISHED_CONSTANT_POS in u['graph_names'])
    source = clearing.base.source_path(module)
    original = clearing.base.source_path(module, 'source')
    command = source.read_bytes()[unit['start']['offset']:unit['end']['offset']]
    body = read(pubpath)['target_readback']['body']['definition'].encode()
    need(unit['graph_names'] == [PUBLISHED_CONSTANT_POS]
         and unit['graph_kinds'] == ['theorem']
         and original.read_bytes().replace(b'\r\n', b'\n').count(command.replace(b'\r\n', b'\n')) == 1
         and body.replace(b'\r\n', b'\n').count(command.replace(b'\r\n', b'\n')) == 1,
         'Published lcmConstant_pos is not the exact source theorem command')
    return {'name': PUBLISHED_CONSTANT_POS,
            'published_definition_module': witness['module'],
            'publication_record': rel(pubpath),
            'publication_record_sha256': sha(pubpath),
            'source_command_sha256': sha_bytes(command),
            'actual_published_body_contains_original_command_once': True}


def source_units():
    clearing.check_only()
    lcm = published_constant_pos()
    bindings, _, _ = clearing.base.ap10.published_bindings()
    provided = set(bindings) | set(clearing.scales.NAMES) | {
        clearing.entry.TARGET, clearing.TARGET, PUBLISHED_CONSTANT_POS}
    for key in clearing.base.ap10.CONFIGS:
        provided.update(clearing.base.ap10.config(key)['names'])
    for key in clearing.base.ap9.CONFIGS:
        provided.update(clearing.base.ap9.config(key)['names'])
    graph = {r['name']: r for r in map(json.loads,
             GRAPH.read_text(encoding='utf-8').splitlines())}
    closure, pending = set(), [TARGET]
    while pending:
        name = pending.pop()
        if name in closure:
            continue
        need(name in graph, 'Unknown actual source graph dependency: ' + name)
        closure.add(name)
        if name not in provided:
            pending += graph[name]['typeDeps'] + graph[name]['valueDeps']
    expected = {PREFIXES[m] + n for m, names in HELPER_NAMES.items()
                for n in names} | {TARGET}
    need(closure - provided == expected and len(expected) == 22,
         'Actual 22-original-command source closure differs')
    ast_modules = {m['module']: m for m in read(AST)['modules']}
    scope_modules = {m['source']: m for m in read(SCOPES)['modules']}
    rows, commands, pins = [], {}, {rel(p): sha(p) for p in [
        SELF, AST, SCOPES, GRAPH,
        clearing.STAGE / 'preparation.json',
        clearing.STAGE / clearing.TARGET_OUTPUT,
        clearing.STAGE / clearing.SOLUTION_OUTPUT,
        clearing.scales.STAGE / 'preparation.json',
        clearing.scales.STAGE / clearing.scales.PROVIDER_FILE,
        clearing.entry.STAGE / 'publication-v3/publication.json',
        TASK / lcm['publication_record']]}
    for module, shorts in HELPER_NAMES.items():
        port = clearing.base.source_path(module)
        original = clearing.base.source_path(module, 'source')
        raw = port.read_bytes()
        orig = original.read_bytes().replace(b'\r\n', b'\n')
        am = ast_modules[module]
        sm = scope_modules[module.replace('.', '/') + '.lean']
        need(am['source_sha256'] == sm['source_sha256'] == sha(port),
             'Source AST/scope input hash differs: ' + module)
        pins.update({rel(p): sha(p) for p in [port, original]})
        selected = []
        for short in shorts + ([TARGET.rsplit('.', 1)[1]] if module == TARGET_MODULE else []):
            name = PREFIXES[module] + short
            unit = next(u for u in am['units'] if name in u['graph_names'])
            scope = next(s for s in sm['declarations'] if s['verified_name'] == name)
            a, b = unit['start']['offset'], unit['end']['offset']
            command = raw[a:b]
            contexts = [raw[c['range']['start']['offset']:c['range']['end']['offset']].decode()
                        for c in scope['context_commands']]
            need(unit['graph_names'] == [name] and unit['graph_kinds'] == ['theorem']
                 and unit['privateTok'] is None and not unit['is_instance_command']
                 and not unit['is_local_instance'] and scope['namespace'] == PREFIXES[module][:-1]
                 and all(c['kind'] == 'namespace' for c in scope['scope_stack'])
                 and contexts == clearing.scope_context(module)
                 and orig.count(command.replace(b'\r\n', b'\n')) == 1,
                 'Original source theorem command/context differs: ' + name)
            selected.append((a, name, command))
            rows.append({'name': name, 'module': module, 'kind': 'theorem',
                         'ast': unit, 'scope': scope, 'graph': graph[name],
                         'source': rel(port), 'source_sha256': sha(port),
                         'original': rel(original), 'original_sha256': sha(original),
                         'start': a, 'end': b, 'command_sha256': sha_bytes(command),
                         'original_port_command_equal_modulo_line_endings': True})
        need(selected == sorted(selected), 'Original source theorem order differs')
        commands[module] = selected
    target = rows[-1]
    need([target['start'], target['end']] == TARGET_SOURCE_RANGE,
         'Original lower-bound target byte range differs')
    lines = sum(r['ast']['end']['line'] - r['ast']['start']['line'] + 1 for r in rows)
    need(lines == 247, 'Original lower-bound source line count differs')
    return graph, closure, provided, rows, commands, pins, lcm


def stage_files():
    graph, closure, provided, rows, commands, pins, lcm = source_units()
    target = rows[-1]
    target_command = commands[TARGET_MODULE][-1][2]
    unit = target['ast']
    value_start = unit['valueStart']['offset'] - target['start']
    need(target_command[value_start:value_start + 5] == b':= by',
         'Original target proof delimiter differs')
    result = {'schema_version': 1,
              'artifact_kind': 'ap16-selected-minor-lower-bound-source-route-only',
              'source_commit': COMMIT, 'source_name': TARGET,
              'source_module': TARGET_MODULE,
              'target_ast': unit,
              'target_source_command_sha256': sha_bytes(target_command),
              'target_proof_suffix_sha256': sha_bytes(target_command[value_start:]),
              'target_original_command_equal_modulo_line_endings': True,
              'source_graph_closure_names': sorted(closure),
              'actual_provided_names': sorted(closure & provided),
              'inline_exact_source_units': rows,
              'inline_proof_ast_count': 22,
              'inline_source_line_count': 247,
              'actual_published_lcmConstant_pos': lcm,
              'AP15_clearing_public_boundary_name': clearing.TARGET,
              'AP15_clearing_closed_original_name_mirror_pending': True,
              'AP15_mirror_must_expose_only_target': True,
              'AP15_mirror_actual_certificate_and_olean_pending': True,
              'final_preamble_solution_snapshots_manifests_pending': True,
              'compiled': False, 'Lean_started': False, 'API_used': False,
              'validated': False, 'submission_ready': False,
              'proposal_status': 'Draft', 'input_hashes': pins}
    outputs = {'route-preparation.json': encode(result),
               'original-target-command.lean.txt': target_command}
    for selected in commands.values():
        for _, name, command in selected:
            outputs['source-units/' + name.replace('.', '_') + '.port.lean.txt'] = command
    return outputs


def check_only():
    outputs = stage_files()
    for name, raw in outputs.items():
        need((STAGE / name).is_file() and (STAGE / name).read_bytes() == raw,
             'Immutable AP16 source-only route differs: ' + name)
    return {'checked_files': len(outputs), 'source_AST_units': 22,
            'source_lines': 247, 'mirror_boundary_pending': True,
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
