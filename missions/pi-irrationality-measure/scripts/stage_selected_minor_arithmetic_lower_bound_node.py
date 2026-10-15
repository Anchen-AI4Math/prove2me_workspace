"""Pure AP16 lower-bound proof stage; freeze compiler manifests only after the real clearing mirror."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import stage_selected_minor_arithmetic_lower_bound_route as route
import stage_selected_minor_clearing_bound_node as clearing
import stage_selected_minor_clearing_child_mirror_probe_v4 as mirror
import stage_selected_minor_clearing_child_mirror_validation_v5 as mirror_validation
import stage_shifted_gaussian_node as shifted

TASK, ROOT, V = route.TASK, route.ROOT, route.V
SELF = Path(__file__).resolve()
STAGE = route.STAGE
COMMIT, TARGET_MODULE, TARGET = route.COMMIT, route.TARGET_MODULE, route.TARGET
PLATFORM_NAME = TARGET
TARGET_OUTPUT = 'Theorems/Thm_' + TARGET.replace('.', '_') + '.lean'
SOLUTION_MODULE = 'Solutions.Sol_OAI_PiExponent_MatrixArithmetic_selectedMinor_arithmetic_lower_bound_ap16_global'
SOLUTION_OUTPUT = SOLUTION_MODULE.replace('.', '/') + '.lean'
SOURCE_SNAPSHOT, GENERATED_SNAPSHOT = 'SourceSnapshot.lean', 'GeneratedSnapshot.lean'
SOURCE_TYPE_JSON, GENERATED_TYPE_JSON = 'source-types.json', 'generated-types.json'
SOURCE_REFS_JSON, GENERATED_REFS_JSON = 'source-proof-references.json', 'generated-proof-references.json'
FILES = [TARGET_OUTPUT, SOLUTION_OUTPUT, SOURCE_SNAPSHOT, GENERATED_SNAPSHOT]
MODES = ['modecheck', 'emit-olean', 'modecheck', 'modecheck']
MANIFESTS = ['c1.json', 'c2.json', 'c3.json', 'c4.json']
CERTIFICATE = 'node-validation.json'
RUNNER = TASK / 'scripts/preflight_staged_module_windows_bounded.py'
LEGACY_RUNNER = TASK / 'scripts/preflight_staged_module.py'
HELPER_NAMES, PREFIXES = route.HELPER_NAMES, route.PREFIXES
IMPORTS = ['Mathlib.Tactic', shifted.DEFINITION_MODULE,
           clearing.base.ap10.config('interpolation')['platform_module'],
           clearing.base.ap10.config('arithmetic')['platform_module'],
           clearing.base.ap10.config('determinant')['platform_module'],
           clearing.scales.PLATFORM_MODULE, mirror.MODULE]
read, sha, sha_bytes, encode, need, rel = route.read, route.sha, route.sha_bytes, route.encode, route.need, route.rel
workspace_rel, verification_rel = clearing.workspace_rel, clearing.verification_rel


def snapshot(side, names, boundary):
    module = TARGET_MODULE if side == 'source' else SOLUTION_MODULE
    owners = list(HELPER_NAMES) if side == 'source' else [
        SOLUTION_MODULE, mirror.MODULE, shifted.DEFINITION_MODULE,
        clearing.scales.PLATFORM_MODULE,
        *[clearing.base.ap10.config(k)['platform_module'] for k in clearing.base.ap10.CONFIGS],
        *[clearing.base.ap9.config(k)['platform_module'] for k in clearing.base.ap9.CONFIGS]]
    roots = '#[' + ', '.join('`' + n for n in names) + ']'
    typ = SOURCE_TYPE_JSON if side == 'source' else GENERATED_TYPE_JSON
    refs = SOURCE_REFS_JSON if side == 'source' else GENERATED_REFS_JSON
    return ('import Lean\nimport ' + module + '\n\n'
            + clearing.SNAPSHOT_CORE.read_text(encoding='utf-8').rstrip() + '\n'
            + clearing.base.ap8.PROBE + '\n' + clearing.PROBE
            + '\nrun_meta do\n'
            + '  PiExponentInterfaceSnapshot.exportSnapshot ' + roots + ' '
            + json.dumps(workspace_rel(STAGE / typ)) + '\n'
            + '  SelectedMinorProofSnapshot.exportBundle ' + json.dumps(side) + ' '
            + json.dumps(workspace_rel(STAGE / refs)) + ' ' + roots + ' #['
            + ', '.join(json.dumps(x) for x in owners) + '] #['
            + ', '.join(json.dumps(x) for x in sorted(boundary)) + ']\n'
            + '#print axioms ' + names[-1] + '\n').encode()


def proof_files():
    route.check_only()
    graph, closure, provided, rows, commands, _, lcm = route.source_units()
    command = commands[TARGET_MODULE][-1][2]
    target = rows[-1]
    ast = target['ast']
    a = target['start']
    ns = ast['nameRange']['start']['offset'] - a
    ne = ast['nameRange']['end']['offset'] - a
    vs = ast['valueStart']['offset'] - a
    need(command[vs:vs + 5] == b':= by' and [a, target['end']] == route.TARGET_SOURCE_RANGE,
         'Original target AST/proof delimiter differs')
    preamble = (''.join('import ' + m + '\n' for m in IMPORTS)
                + '\nopen OAI.PiExponent OAI.PiExponent.MatrixArithmetic\n'
                + 'open scoped BigOperators\n\n').encode()
    formal = command[:ns] + PLATFORM_NAME.encode() + command[ne:vs] + b':= by\n  sorry\n'
    parts = [(''.join('import ' + m + '\n' for m in IMPORTS) + '\n').encode()]
    for module, selected in commands.items():
        namespace = PREFIXES[module][:-1]
        header = 'namespace ' + namespace + '\n\n'
        for context in clearing.scope_context(module):
            header += context + '\n'
        parts.append((header + '\n').encode())
        parts.extend(c + b'\n\n' for _, name, c in selected if name != TARGET)
        parts.append(('end ' + namespace + '\n\n').encode())
    renamed = command[:ns] + b'solution' + command[ne:]
    need(renamed[renamed.index(b':= by'):] == command[vs:],
         'Original target proof suffix changed')
    parts += [b'open OAI.PiExponent OAI.PiExponent.MatrixArithmetic\n'
              b'open scoped BigOperators\n\n', renamed + b'\n']
    helpers = [r['name'] for r in rows[:-1]]
    boundary = closure & provided
    source_names, generated_names = helpers + [TARGET], helpers + ['solution']
    files = {TARGET_OUTPUT: preamble + formal, SOLUTION_OUTPUT: b''.join(parts),
             SOURCE_SNAPSHOT: snapshot('source', source_names, boundary),
             GENERATED_SNAPSHOT: snapshot('generated', generated_names, boundary),
             'wire-theorem-source.lean': preamble + formal,
             'academic-metadata.json': encode({
                 'title': 'An arithmetic lower bound for a selected interpolation minor',
                 'statement': 'The original selected minor satisfies the source arithmetic lower bound under its stated row, column, and denominator assumptions.',
                 'explanation': 'The proof copies the 22 original source theorem commands, using the established clearing bound and original arithmetic definitions.',
                 'source_commit': COMMIT,
                 'source_url': 'https://github.com/openai/math/blob/' + COMMIT
                               + '/lean/OAI/NumberTheory/PiExponent/Approximation/MatrixArithmetic.lean#L360-L393',
                 'tags': ['number-theory', 'linear-algebra', 'openai-pi-exponent-017']})}
    need(len(rows) == 22 and len(helpers) == 21 and b'sorry' not in files[SOLUTION_OUTPUT]
         and files[SOLUTION_OUTPUT].count(b'theorem solution') == 1,
         'Original 22-theorem global proof assembly differs')
    return files, rows, closure, boundary, lcm, command, vs


def candidate_files():
    files, rows, closure, boundary, lcm, command, vs = proof_files()
    output = {'candidate/' + f + '.txt': raw for f, raw in files.items()
              if f in FILES + ['wire-theorem-source.lean', 'academic-metadata.json']}
    output['candidate-spec.json'] = encode({
        'schema_version': 1, 'artifact_kind': 'ap16-selected-minor-lower-bound-candidate',
        'source_commit': COMMIT, 'source_name': TARGET, 'source_module': TARGET_MODULE,
        'target_ast': rows[-1]['ast'], 'target_command_sha256': sha_bytes(command),
        'target_proof_suffix_sha256': sha_bytes(command[vs:]),
        'source_AST_units': 22, 'source_lines': 247,
        'source_type_only_names': [r['name'] for r in rows],
        'generated_type_only_names': [r['name'] for r in rows[:-1]] + ['solution'],
        'provider_subtracted_names': sorted(boundary),
        'clearing_public_boundary_name': clearing.TARGET,
        'published_lcmConstant_pos': lcm,
        'imports': IMPORTS, 'files': {f: sha_bytes(files[f]) for f in FILES},
        'AP15_private_mirror_certificate_pending': True,
        'compiler_manifests_finalized': False, 'Lean_started': False,
        'API_used': False, 'validated': False, 'submission_ready': False})
    return output


def check_candidate():
    files = candidate_files()
    for name, raw in files.items():
        need((STAGE / name).is_file() and (STAGE / name).read_bytes() == raw,
             'AP16 candidate differs: ' + name)
    need(not (STAGE / 'preparation.json').exists(),
         'Final AP16 preparation already exists; use --check-only')
    return {'checked_files': len(files), 'source_AST_units': 22,
            'source_lines': 247, 'final_manifests_pending': True,
            'Lean_started': False, 'API_used': False}


def mirror_boundary():
    cert_path = mirror_validation.STAGE / mirror_validation.CERTIFICATE
    publication = clearing.STAGE / 'publication-v4/publication.json'
    need(cert_path.is_file() and publication.is_file(),
         'Actual AP15 private mirror certificate and Accepted/Proved publication are pending')
    cert, pub = read(cert_path), read(publication)
    clearing_prep = read(clearing.STAGE / 'preparation.json')
    emitter = mirror.EMITTER_STAGE / mirror.OUTPUT
    olean = TASK / cert.get('provider_olean', '')
    need(cert.get('validated') is True and cert.get('Std3_only') is True
         and cert.get('public_platform_boundary_names') == [clearing.TARGET]
         and cert.get('platform_boundary_certification_pending') is False
         and cert.get('accepted_parent_Proved') is True
         and cert.get('public_platform_boundary_remains_original_target_only') is True
         and cert.get('artifact_kind') == 'ap16-private-clearing-child-mirror-validation-v5'
         and cert.get('derived_ledger_sha256') == sha(mirror_validation.LEDGER)
         and cert.get('frozen_v4_consumer_sha256') == sha(mirror_validation.FROZEN_V4_CONSUMER)
         and cert.get('actual_closed_automatic_data_helper_pair', {}).get('name') ==
             mirror_validation.AUTO_HELPER
         and cert['actual_closed_automatic_data_helper_pair']['full_type_axioms_and_all_actual_refs_equal'] is True
         and cert.get('provider_source_sha256') == sha(emitter)
         and cert.get('provider_olean_sha256') == mirror.EXPECTED_OLEAN == sha(olean)
         and cert.get('preparation_sha256') == sha(mirror.STAGE / 'preparation.json')
         and cert.get('accepted_evidence_sha256') == sha(publication)
         and cert.get('bounded_runner_sha256') == sha(RUNNER)
         and pub.get('confirmed_proved') is True
         and pub.get('target_readback', {}).get('body', {}).get('status') == 'Proved'
         and pub['target_readback']['body']['theorem_name'] == clearing.TARGET
         and pub['target_readback']['body']['preamble'] == clearing_prep['preamble']
         and pub['target_readback']['body']['formal_statement'] == clearing_prep['formal_statement'],
         'Actual AP15 mirror/public boundary differs')
    return cert_path, publication


def final_files():
    cert_path, publication = mirror_boundary()
    files, rows, closure, boundary, lcm, command, vs = proof_files()
    for output in FILES:
        candidate = STAGE / ('candidate/' + output + '.txt')
        need(candidate.is_file() and candidate.read_bytes() == files[output],
             'Final AP16 proof or probe differs from the checked candidate: ' + output)
    _, _, _, _, _, pins, _ = route.source_units()
    sources = [SELF, route.SELF, clearing.SELF, mirror.SELF,
               mirror_validation.SELF, mirror_validation.CONSUMER,
               mirror_validation.FROZEN_V4_CONSUMER, mirror_validation.LEDGER,
               RUNNER, LEGACY_RUNNER,
               clearing.RUNTIME, clearing.SNAPSHOT_CORE,
               Path(clearing.base.ap8.__file__), cert_path, publication,
               mirror.EMITTER_STAGE / mirror.OUTPUT,
               mirror.STAGE / 'preparation.json', mirror.STAGE / mirror.SNAPSHOT,
               mirror.ACCEPTED, STAGE / 'candidate-spec.json']
    inputs = {rel(p): sha(p) for p in sources}
    inputs.update(pins)
    manifests, commands = {}, []
    for output, mode, manifest, imports in zip(
            FILES, MODES, MANIFESTS,
            [IMPORTS, IMPORTS, ['Lean', TARGET_MODULE], ['Lean', SOLUTION_MODULE]], strict=True):
        manifests[output] = {'sha256': sha_bytes(files[output]), 'mode': mode,
                             'emit_olean': mode == 'emit-olean',
                             'manifest': manifest, 'imports': imports}
        files[manifest] = encode({
            'schema_version': 1,
            'artifact_kind': 'ap16-selected-minor-lower-bound-bounded-compiler-manifest',
            'output': workspace_rel(STAGE / output), 'output_sha256': sha_bytes(files[output]),
            'imports': imports, 'input_hashes': inputs,
            'runtime_sha256': sha(clearing.RUNTIME), 'mode': mode,
            'emit_olean': mode == 'emit-olean', 'timeout_seconds': 300,
            'bounded_runner': rel(RUNNER), 'bounded_runner_sha256': sha(RUNNER),
            'legacy_runner_sha256': sha(LEGACY_RUNNER),
            'validated': False, 'submission_ready': False})
        commands.append('python scripts/preflight_staged_module_windows_bounded.py '
            + verification_rel(STAGE / output)
            + ' --root ap16/selected-minor-arithmetic-lower-bound --imports-manifest '
            + verification_rel(STAGE / manifest) + ' --timeout-seconds 300'
            + (' --emit-olean' if mode == 'emit-olean' else ''))
    files['preparation.json'] = encode({
        'schema_version': 1, 'artifact_kind': 'ap16-selected-minor-lower-bound-node-preparation',
        'source_commit': COMMIT, 'source_name': TARGET, 'platform_name': PLATFORM_NAME,
        'source_module': TARGET_MODULE, 'target_ast': rows[-1]['ast'],
        'target_source_command_sha256': sha_bytes(command),
        'target_proof_suffix_sha256': sha_bytes(command[vs:]),
        'global_solution_preserves_literal_source_proof': True,
        'all_helper_proofs_literal_original': True,
        'existing_port_adaptations': [], 'preamble': files[TARGET_OUTPUT].decode().split('theorem ', 1)[0],
        'formal_statement': 'theorem ' + files[TARGET_OUTPUT].decode().split('theorem ', 1)[1],
        'graph_closure_names': sorted(closure), 'provider_subtracted_names': sorted(boundary),
        'inline_helper_names': [r['name'] for r in rows[:-1]],
        'inline_exact_source_units': rows[:-1], 'target_exact_source_unit': rows[-1],
        'source_type_only_names': [r['name'] for r in rows],
        'generated_type_only_names': [r['name'] for r in rows[:-1]] + ['solution'],
        'source_theorem_values_null': True, 'generated_theorem_values_null': True,
        'original_proof_AST_units': 22, 'original_source_lines': 247,
        'actual_published_lcmConstant_pos': lcm,
        'required_private_AP15_mirror_certificate': rel(cert_path),
        'required_Accepted_Proved_AP15_publication': rel(publication),
        'bounded_runner': rel(RUNNER), 'bounded_runner_sha256': sha(RUNNER),
        'input_hashes': inputs, 'files': manifests, 'compile_commands': commands,
        'Lean_started': False, 'API_used': False, 'validated': False,
        'submission_ready': False, 'proposal_status': 'Draft'})
    files['compile-commands.txt'] = ('\n'.join(commands) + '\n').encode()
    return files


def check_only():
    files = final_files()
    for name, raw in files.items():
        need((STAGE / name).is_file() and (STAGE / name).read_bytes() == raw,
             'Immutable AP16 final stage differs: ' + name)
    for output, manifest in zip(FILES, MANIFESTS, strict=True):
        m = read(STAGE / manifest)
        clearing.base.runner.verify_manifest_inputs(m)
        clearing.base.runner.verify_source_certificate(STAGE / output, m)
    return {'checked_files': len(files), 'source_AST_units': 22,
            'source_lines': 247, 'all_original_proofs_literal': True,
            'Lean_started': False, 'API_used': False, 'validated': False}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    g = p.add_mutually_exclusive_group(required=True)
    g.add_argument('--prepare-candidate', action='store_true')
    g.add_argument('--check-candidate', action='store_true')
    g.add_argument('--finalize', action='store_true')
    g.add_argument('--check-only', action='store_true')
    a = p.parse_args()
    if a.prepare_candidate:
        files = candidate_files()
    elif a.finalize:
        files = final_files()
    else:
        files = {}
    for name, raw in files.items():
        path = STAGE / name
        if path.exists():
            need(path.read_bytes() == raw, 'Refusing overwrite: ' + name)
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(raw)
    result = check_only() if a.check_only or a.finalize else check_candidate()
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == '__main__':
    main()
