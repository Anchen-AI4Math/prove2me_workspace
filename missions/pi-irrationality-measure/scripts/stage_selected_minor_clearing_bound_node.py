"""Pure AP15 staging of the original selected-minor clearing-bound proof."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import generate_equation_provenance_probe as equation
import stage_entry_gaussian_node as entry
import stage_entry_gaussian_child_mirror as child
import stage_scales_costs_data_provider as scales

base = entry.base
TASK, ROOT, V = entry.TASK, entry.ROOT, entry.V
SELF = Path(__file__).resolve()
STAGE = V / 'ap15/selected-minor-clearing-bound'
COMMIT = entry.COMMIT
AST, SCOPES, GRAPH = entry.AST, entry.SCOPES, entry.GRAPH
RUNTIME, SNAPSHOT_CORE = entry.RUNTIME, entry.SNAPSHOT_CORE
TARGET_MODULE = 'OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic'
TARGET = 'OAI.PiExponent.MatrixArithmetic.selectedMinor_clearing_bound'
PLATFORM_NAME = TARGET
TARGET_OUTPUT = 'Theorems/Thm_' + TARGET.replace('.', '_') + '.lean'
SOLUTION_MODULE = 'Solutions.Sol_OAI_PiExponent_MatrixArithmetic_selectedMinor_clearing_bound_ap15_global'
SOLUTION_OUTPUT = SOLUTION_MODULE.replace('.', '/') + '.lean'
SOURCE_SNAPSHOT, GENERATED_SNAPSHOT = 'SourceSnapshot.lean', 'GeneratedSnapshot.lean'
SOURCE_TYPE_JSON, GENERATED_TYPE_JSON = 'source-types.json', 'generated-types.json'
SOURCE_REFS_JSON, GENERATED_REFS_JSON = 'source-proof-references.json', 'generated-proof-references.json'
FILES = [TARGET_OUTPUT, SOLUTION_OUTPUT, SOURCE_SNAPSHOT, GENERATED_SNAPSHOT]
MODES = ['modecheck', 'emit-olean', 'modecheck', 'modecheck']
MANIFESTS = ['c1.json', 'c2.json', 'c3.json', 'c4.json']
CERTIFICATE = 'node-validation.json'
SIMPLEX = 'OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting'
INTERPOLATION = 'OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix'
ARITHMETIC = 'OAI.NumberTheory.PiExponent.Approximation.Arithmetic'
HELPER_NAMES = {
    SIMPLEX: ['mem_realWeightedSimplex'],
    INTERPOLATION: ['column_mem_iff', 'column_weight_le'],
    ARITHMETIC: ['gaussian_norm_one_le', 'gaussian_det_norm_one_le',
                 'det_row_column_scale', 'cleared_det_norm_bound',
                 'cleared_det_log_bound', 'cleared_det_log_bound_of_entries',
                 'cleared_det_log_bound_with_denominator'],
    TARGET_MODULE: ['columnScale_pos', 'rowScale_pos', 'denominator_pos',
                    'log_columnScale', 'log_rowScale', 'ceil_log_weight_pos',
                    'column_coordinate_le_floor', 'selectedMinor_entries_gaussian'],
}
PREFIXES = {
    SIMPLEX: 'OAI.PiExponent.',
    INTERPOLATION: 'OAI.PiExponent.InterpolationMatrix.',
    ARITHMETIC: 'OAI.PiExponent.Arithmetic.',
    TARGET_MODULE: 'OAI.PiExponent.MatrixArithmetic.',
}
EQUATIONS = [PREFIXES[TARGET_MODULE] + 'columnScale.eq_1',
             PREFIXES[TARGET_MODULE] + 'rowScale.eq_1']
IMPORTS = ['Mathlib.Tactic',
           base.ap10.config('interpolation')['platform_module'],
           base.ap10.config('arithmetic')['platform_module'],
           base.ap10.config('determinant')['platform_module'],
           scales.PLATFORM_MODULE, child.MODULE]
read, sha, sha_bytes, encode, need = entry.read, entry.sha, entry.sha_bytes, entry.encode, entry.need
rel, workspace_rel, verification_rel = entry.rel, entry.workspace_rel, entry.verification_rel
PROBE = entry.mean.PROBE.replace('ActualMeanBoundsProofSnapshot', 'SelectedMinorProofSnapshot')


def scope_context(module):
    if module == SIMPLEX:
        return ['open scoped BigOperators', 'open Filter Topology']
    if module == ARITHMETIC:
        return []
    return ['open scoped BigOperators']


def authority():
    scales.check_only()
    child.check_only()
    graph = {x['name']: x for x in map(json.loads, GRAPH.read_text(encoding='utf-8').splitlines())}
    bindings, published_pins, _ = base.ap10.published_bindings()
    provided = set(bindings) | set(scales.NAMES) | {entry.TARGET}
    ap10_paths = []
    for key in base.ap10.CONFIGS:
        config = base.ap10.config(key)
        provided.update(config['names'])
        ap10_paths += [config['stage'] / 'preparation.json',
                       config['stage'] / config['provider_file'],
                       config['stage'] / ('actual-provider-validation-helper-v2.json'
                                          if key == 'determinant' else 'actual-provider-validation.json'),
                       config['stage'] / ('publication-helper-v2/publication.json'
                                          if key == 'determinant' else 'publication/publication.json')]
    for key in base.ap9.CONFIGS:
        provided.update(base.ap9.config(key)['names'])
    closure, pending = set(), [TARGET]
    while pending:
        name = pending.pop()
        if name in closure:
            continue
        need(name in graph, 'Unknown source graph dependency: ' + name)
        closure.add(name)
        if name not in provided and name not in EQUATIONS:
            pending += graph[name]['typeDeps'] + graph[name]['valueDeps']
    expected = {PREFIXES[m] + short for m, names in HELPER_NAMES.items() for short in names} | {TARGET}
    need(len(closure) == 39 and closure - provided - set(EQUATIONS) == expected
         and len(expected) == 19 and set(EQUATIONS) <= closure,
         'Actual 19-original-command, two-equation proof closure differs')
    ast_modules = {m['module']: m for m in read(AST)['modules']}
    scope_modules = {m['source']: m for m in read(SCOPES)['modules']}
    rows, commands, pins = [], {}, dict(published_pins)
    pins.update({rel(p): sha(p) for p in ap10_paths})
    for module, shorts in HELPER_NAMES.items():
        port = base.source_path(module)
        original = base.source_path(module, 'source')
        raw = port.read_bytes()
        orig = original.read_bytes().replace(b'\r\n', b'\n')
        am, sm = ast_modules[module], scope_modules[module.replace('.', '/') + '.lean']
        need(am['source_sha256'] == sm['source_sha256'] == sha(port),
             'Exact source inventory differs: ' + module)
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
                 and contexts == scope_context(module)
                 and orig.count(command.replace(b'\r\n', b'\n')) == 1,
                 'Original theorem AST, context or proof differs: ' + name)
            selected.append((a, name, command))
            rows.append({'name': name, 'module': module, 'kind': 'theorem',
                         'ast': unit, 'scope': scope, 'graph': graph[name],
                         'source': rel(port), 'source_sha256': sha(port),
                         'original': rel(original), 'original_sha256': sha(original),
                         'start': a, 'end': b, 'command_sha256': sha_bytes(command),
                         'original_port_command_equal_modulo_line_endings': True})
        need(selected == sorted(selected), 'Original helper source order differs: ' + module)
        commands[module] = selected
    pubpath = entry.STAGE / 'publication-v3/publication.json'
    pub = read(pubpath)
    body = pub['target_readback']['body']
    need(pub['confirmed_proved'] is True and body['status'] == 'Proved'
         and body['theorem_name'] == entry.TARGET
         and body['formal_statement'] == read(entry.STAGE / 'preparation.json')['formal_statement'],
         'Actual AP14 public target is not the exact Proved theorem')
    for path in [pubpath, entry.STAGE / entry.CERTIFICATE,
                 scales.SELF, scales.STAGE / 'preparation.json',
                 scales.STAGE / scales.PROVIDER_FILE,
                 child.SELF, child.STAGE / 'preparation.json',
                 child.STAGE / child.OUTPUT,
                 V / 'ap12/arithmetic-route.json']:
        pins[rel(path)] = sha(path)
    return graph, closure, provided, rows, commands, pins


def equation_specs(side):
    module = TARGET_MODULE if side == 'source' else scales.PLATFORM_MODULE
    return [(name.removesuffix('.eq_1'), module, side + '-equation-' + str(i) + '.json')
            for i, name in enumerate(EQUATIONS, 1)]


def snapshot(side, names, boundary):
    module = TARGET_MODULE if side == 'source' else SOLUTION_MODULE
    owners = list(HELPER_NAMES) + ['SourceSnapshot'] if side == 'source' else [
        SOLUTION_MODULE, scales.PLATFORM_MODULE, child.MODULE,
        base.ap10.config('interpolation')['platform_module'],
        base.ap10.config('arithmetic')['platform_module'],
        base.ap10.config('determinant')['platform_module'], 'GeneratedSnapshot']
    types = SOURCE_TYPE_JSON if side == 'source' else GENERATED_TYPE_JSON
    refs = SOURCE_REFS_JSON if side == 'source' else GENERATED_REFS_JSON
    init = ''.join('  PiExponentEquationProvenanceProbe.exportEquationSnapshot `'
                   + primary + ' ' + json.dumps(owner) + ' '
                   + json.dumps(workspace_rel(STAGE / output)) + ' '
                   + json.dumps(side) + '\n'
                   for primary, owner, output in equation_specs(side))
    roots = '#[' + ', '.join('`' + n for n in names) + ']'
    return ('import Lean\nimport ' + module + '\n\n'
            + SNAPSHOT_CORE.read_text(encoding='utf-8').rstrip() + '\n'
            + base.ap8.PROBE + '\n' + PROBE + '\n' + equation.PROBE
            + '\nrun_meta do\n' + init
            + '  PiExponentInterfaceSnapshot.exportSnapshot ' + roots + ' '
            + json.dumps(workspace_rel(STAGE / types)) + '\n'
            + '  SelectedMinorProofSnapshot.exportBundle ' + json.dumps(side) + ' '
            + json.dumps(workspace_rel(STAGE / refs)) + ' ' + roots + ' #['
            + ', '.join(json.dumps(x) for x in owners) + '] #['
            + ', '.join(json.dumps(x) for x in sorted(boundary)) + ']\n'
            + '#print axioms ' + names[-3] + '\n').encode()


def metadata():
    return {'title': 'A denominator-clearing lower bound for a selected interpolation minor',
            'statement': 'For the original truncated-logarithm interpolation matrix, choose a square minor with nonzero determinant. Under the stated positive integer denominator and weight assumptions, its logarithmic determinant is bounded below by the negative row-count times the logarithm of the common denominator, minus the selected column cost, plus the row cost. The definitions and indices are exactly those of the source theorem.',
            'explanation': 'Clear denominators entrywise into Gaussian integers, then apply the source determinant norm bound and expand the logarithms of row and column scales.',
            'tags': ['number-theory', 'linear-algebra', 'openai-pi-exponent-017'],
            'source_commit': COMMIT,
            'source_url': 'https://github.com/openai/math/blob/' + COMMIT
                          + '/lean/OAI/NumberTheory/PiExponent/Approximation/MatrixArithmetic.lean#L337-L358'}


def stage_files():
    graph, closure, provided, rows, commands, pins = authority()
    target = rows[-1]
    unit = target['ast']
    command = commands[TARGET_MODULE][-1][2]
    a = target['start']
    need([a, target['end']] == [16341, 17643], 'Pinned target AST differs')
    ns = unit['nameRange']['start']['offset'] - a
    ne = unit['nameRange']['end']['offset'] - a
    vs = unit['valueStart']['offset'] - a
    need(command[vs:vs + 5] == b':= by', 'Original proof delimiter differs')
    preamble = (''.join('import ' + m + '\n' for m in IMPORTS)
                + '\nopen OAI.PiExponent OAI.PiExponent.MatrixArithmetic\n'
                + 'open scoped BigOperators\n\n').encode()
    formal = command[:ns] + PLATFORM_NAME.encode() + command[ne:vs] + b':= by\n  sorry\n'
    parts = [(''.join('import ' + m + '\n' for m in IMPORTS) + '\n').encode()]
    for module, selected in commands.items():
        namespace = PREFIXES[module][:-1]
        header = 'namespace ' + namespace + '\n\n'
        for context in scope_context(module):
            header += context + '\n'
        parts.append((header + '\n').encode())
        parts.extend(c + b'\n\n' for _, name, c in selected if name != TARGET)
        parts.append(('end ' + namespace + '\n\n').encode())
    renamed = command[:ns] + b'solution' + command[ne:]
    need(renamed[renamed.index(b':= by'):] == command[vs:],
         'Literal source target proof changed')
    parts += [b'open OAI.PiExponent OAI.PiExponent.MatrixArithmetic\n'
              b'open scoped BigOperators\n\n', renamed + b'\n']
    helpers = [r['name'] for r in rows[:-1]]
    boundary = closure & provided
    source_names = helpers + [TARGET] + EQUATIONS
    generated_names = helpers + ['solution'] + EQUATIONS
    generated = {TARGET_OUTPUT: preamble + formal,
                 SOLUTION_OUTPUT: b''.join(parts),
                 SOURCE_SNAPSHOT: snapshot('source', source_names, boundary),
                 GENERATED_SNAPSHOT: snapshot('generated', generated_names, boundary),
                 'wire-theorem-source.lean': preamble + formal,
                 'original-target-command.lean.txt': command,
                 'academic-metadata.json': encode(metadata())}
    for selected in commands.values():
        for _, name, c in selected:
            generated['source-units/' + name.replace('.', '_') + '.port.lean.txt'] = c
    inputs = {rel(p): sha(p) for p in [SELF, Path(entry.__file__),
              Path(entry.mean.__file__), Path(base.__file__), AST, SCOPES,
              GRAPH, RUNTIME, SNAPSHOT_CORE, Path(base.ap8.__file__),
              Path(base.runner.__file__), Path(equation.__file__)]}
    inputs.update(pins)
    files, commands_text = {}, []
    for output, mode, manifest, imports in zip(FILES, MODES, MANIFESTS,
            [IMPORTS, IMPORTS, ['Lean', TARGET_MODULE], ['Lean', SOLUTION_MODULE]], strict=True):
        files[output] = {'sha256': sha_bytes(generated[output]), 'mode': mode,
                         'emit_olean': mode == 'emit-olean',
                         'manifest': manifest, 'imports': imports}
        generated[manifest] = encode({'schema_version': 1,
             'artifact_kind': 'ap15-selected-minor-clearing-bound-bounded-compiler-manifest',
             'output': workspace_rel(STAGE / output),
             'output_sha256': sha_bytes(generated[output]), 'imports': imports,
             'input_hashes': inputs, 'runtime_sha256': sha(RUNTIME),
             'mode': mode, 'emit_olean': mode == 'emit-olean',
             'timeout_seconds': 300, 'validated': False, 'submission_ready': False})
        commands_text.append('python scripts/preflight_staged_module.py '
             + verification_rel(STAGE / output) + ' --root ap15/selected-minor-clearing-bound'
             + ' --imports-manifest ' + verification_rel(STAGE / manifest)
             + ' --timeout-seconds 300' + (' --emit-olean' if mode == 'emit-olean' else ''))
    route = read(V / 'ap12/arithmetic-route.json')['steps'][2]
    selected_line_count = sum(r['ast']['end']['line'] - r['ast']['start']['line'] + 1
                              for r in rows)
    need(route['source_graph_names'] == sorted(set(route['source_graph_names']))
         and TARGET in route['source_graph_names']
         and route['genuine_lazy_equation_CIs_without_standalone_AST'] == EQUATIONS
         and selected_line_count == 201,
         'Original arithmetic route / official equation inventory differs')
    generated['preparation.json'] = encode({
        'schema_version': 1, 'artifact_kind': 'ap15-selected-minor-clearing-bound-node-preparation',
        'source_name': TARGET, 'platform_name': PLATFORM_NAME,
        'source_module': TARGET_MODULE, 'source_commit': COMMIT,
        'target_ast': unit, 'target_source_command_sha256': sha_bytes(command),
        'target_proof_suffix_sha256': sha_bytes(command[vs:]),
        'target_original_command_equal_modulo_line_endings': True,
        'global_solution_preserves_literal_source_proof': True,
        'all_helper_proofs_literal_original': True,
        'existing_port_adaptations': [], 'preamble': preamble.decode(),
        'formal_statement': formal.decode(),
        'graph_closure_names': sorted(closure),
        'provider_subtracted_names': sorted(boundary),
        'inline_helper_names': helpers, 'inline_exact_source_units': rows[:-1],
        'target_exact_source_unit': target,
        'source_type_only_names': source_names,
        'generated_type_only_names': generated_names,
        'source_theorem_values_null': True, 'generated_theorem_values_null': True,
        'original_route_target_source_lines': [337, 358],
        'original_proof_AST_units_after_data_and_AP14': 19,
        'original_proof_source_lines_after_data_and_AP14': 201,
        'genuine_lazy_equation_CIs': EQUATIONS,
        'official_equation_API': 'Lean.Meta.getEqnsFor? / Lean.Meta.isEqnThm? with full primary Def values and closed equation type/Std3',
        'input_hashes': inputs, 'files': files, 'compile_commands': commands_text,
        'metadata': metadata(), 'exactName_lookup_required_by_root': TARGET,
        'required_scales_costs_certificate': rel(scales.STAGE / 'actual-provider-validation.json'),
        'required_entry_gaussian_child_mirror_certificate': rel(child.STAGE / child.CERTIFICATE),
        'Lean_started': False, 'API_used': False, 'validated': False,
        'submission_ready': False, 'proposal_status': 'Draft'})
    generated['compile-commands.txt'] = ('\n'.join(commands_text) + '\n').encode()
    return generated


def check_only():
    generated = stage_files()
    for name, raw in generated.items():
        need((STAGE / name).is_file() and (STAGE / name).read_bytes() == raw,
             'Immutable stage differs: ' + name)
    for output, manifest in zip(FILES, MANIFESTS, strict=True):
        m = read(STAGE / manifest)
        base.runner.verify_manifest_inputs(m)
        base.runner.verify_source_certificate(STAGE / output, m)
    return {'checked_files': len(generated), 'source_AST_units': 19,
            'inline_helpers': 18, 'genuine_equations': 2,
            'all_original_port_proofs_equal_modulo_line_endings': True,
            'all_hashes_match': True, 'Lean_started': False,
            'API_used': False, 'validated': False}


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
