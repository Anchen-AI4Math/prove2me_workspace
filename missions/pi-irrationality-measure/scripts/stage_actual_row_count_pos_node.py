"""Stage the seven literal source proofs for actualRowCount_pos, without Lean/API."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import stage_log_translation_count_node as base
import preflight_staged_module as runner
import validate_namespace_context_providers as context

TASK, V, ROOT = base.TASK, base.V, base.ROOT
SELF = Path(__file__).resolve()
STAGE = V / 'ap21/actual-row-count-pos-node'
ROUTE = V / 'ap20/analytic-small-leaf-candidates/actualRowCount_pos'
PUBLISHED = V / 'ap20/analytic-translated-two-layer-reduction-final-v3/publication-v4/publication.json'
SOURCE_STAGE = V / 'ap20/analytic-translated-two-layer-reduction-final'
SOURCE_PREPARATION = V / 'ap20/analytic-translated-two-layer-reduction-final-v3/preparation.json'
DATA_CERT = V / 'ap20/literal-interface-data/actual-provider-validation.json'
DATA_PUBLISHED = V / 'ap20/literal-interface-data/publication/publication.json'
CLOSURE = V / 'ap20/analytic-translated-two-layer-reduction-final-v3/type-import-closure-audit.json'
TARGET = 'OAI.PiExponent.LiteralAnalytic.actualRowCount_pos'
TARGET_ID = 'df6176c8-39cf-473c-b5f0-447ca52023f2'
MODULE = 'Theorems.Thm_OAI_PiExponent_LiteralAnalytic_actualRowCount_pos'
SOLUTION_MODULE = 'Solutions.Sol_OAI_PiExponent_LiteralAnalytic_actualRowCount_pos_ap21'
SOURCE_MODULE = 'OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand'
TARGET_OUTPUT = MODULE.replace('.', '/') + '.lean'
SOLUTION_OUTPUT = SOLUTION_MODULE.replace('.', '/') + '.lean'
SOURCE_SNAPSHOT = 'SourceSnapshot.lean'
GENERATED_SNAPSHOT = 'GeneratedSnapshot.lean'
SOURCE_TYPES = 'source-types.json'
GENERATED_TYPES = 'generated-types.json'
SOURCE_REFS = 'source-proof-references.json'
GENERATED_REFS = 'generated-proof-references.json'
INVENTORY = 'actual-owned-CI-inventory.json'
CERTIFICATE = 'node-validation.json'
RUNNER, LEGACY, RUNTIME = base.RUNNER, base.LEGACY, base.RUNTIME
FILES = [TARGET_OUTPUT, SOLUTION_OUTPUT, SOURCE_SNAPSHOT, GENERATED_SNAPSHOT]
MODES = ['reused-emit-olean', 'emit-olean', 'modecheck', 'modecheck']


def need(ok, reason):
    if not ok:
        raise ValueError(reason)


def digest(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha(path: Path) -> str:
    return digest(Path(path).read_bytes())


def read(path: Path):
    return json.loads(Path(path).read_text(encoding='utf-8'))


def encode(value) -> bytes:
    return (json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode('utf-8')


def rel(path: Path) -> str:
    return Path(path).resolve().relative_to(TASK.resolve()).as_posix()


def ws(path: Path) -> str:
    return Path(path).resolve().relative_to(ROOT.resolve()).as_posix()


def vr(path: Path) -> str:
    return Path(path).resolve().relative_to(V.resolve()).as_posix()


def route_units():
    route = read(ROUTE / 'source-route.json')
    need(route['target'] == TARGET and route['proof_AST_count'] == 7
         and route['source_line_count'] == 53 and len(route['source_units']) == 7
         and route['closure_order'] == [r['name'] for r in route['source_units']]
         and route['missing_data_names'] == []
         and route['uses_unProved_platform_boundaries'] is False
         and route['finite_port_adaptations'] == []
         and route['all_helpers_original_AST_inline'] is True
         and route['target_source_proof_suffix_unchanged_except_solution_name'] is True,
         'Seven original source AST route differs')
    units = route['source_units']
    source = []
    for row in units:
        src, original = TASK / row['source'], TASK / row['original']
        need(sha(src) == row['source_sha256'] and sha(original) == row['original_sha256'],
             'Original/port source full file changed: ' + row['name'])
        raw = src.read_bytes()[row['start']:row['end']]
        original_raw = original.read_bytes()
        need(digest(raw) == row['command_sha256']
             and row['scope']['verified_name'] == row['name']
             and row['ast']['nameText'] == row['name'].split('.')[-1]
             and row['ast']['graph_names'] == [row['name']]
             and row['ast']['graph_kinds'] == ['theorem'],
             'Original AST command or namespace differs: ' + row['name'])
        # The source archive uses LF and the port uses CRLF; normalize only that
        # transport detail before checking the complete original command.
        normalized = raw.replace(b'\r\n', b'\n')
        original_command = original_raw.replace(b'\r\n', b'\n')
        need(normalized.strip() in original_command
             and digest(normalized.strip()) == row['original_normalized_command_sha256'],
             'Literal original source theorem differs: ' + row['name'])
        source.append(normalized.strip())
    return route, units, source


def published_wire() -> tuple[bytes, dict, dict]:
    doc = read(PUBLISHED)
    key = 'actual-child-' + TARGET
    witness = doc['readbacks'][key]
    body = witness['body']
    verdict = doc['batches']['actual']['last_publish_verdicts'][TARGET]['body']
    need(doc['confirmed_two_SKETCH_ACCEPTED_with_actual_graphs'] is True
         and doc['theorem_ids'][TARGET] == TARGET_ID
         and witness['http_status'] == 200
         and digest(witness['raw_body_utf8'].encode()) == witness['raw_body_sha256']
         and body['theorem_id'] == verdict['theorem_id'] == TARGET_ID
         and body['theorem_name'] == verdict['theorem_name'] == TARGET
         and body['mathlib_rev'] == '0df444a360eaa60ab8c11dca51a86af692955474'
         and body['visibility'] == verdict['visibility'] == 'public'
         and body['status'] == 'Open' and body['deprecated_at'] is None
         and body['preamble'] == verdict['definitions']
         and body['formal_statement'] == verdict['formal_statement'],
         'Actual Published exact theorem wire/readback differs')
    raw = (body['preamble'] + body['formal_statement']).encode('utf-8')
    prior = SOURCE_STAGE / TARGET_OUTPUT
    reused = read(SOURCE_PREPARATION)['reused_actual_contexts'][TARGET_OUTPUT]
    record = context.record(TASK / reused['source'], TASK / reused['manifest'],
                            'emit-olean', MODULE, TASK / reused['root'])
    data = record['data']
    need(prior.read_bytes() == raw == (TASK / reused['source']).read_bytes()
         and data['success'] is True and data['exit_code'] == 0
         and data['timed_out'] is False and 0 < data['seconds'] <= 300
         and data['source_unchanged'] is True
         and data['source_sha256_before'] == data['source_sha256_after'] == digest(raw)
         and data['manifest_unchanged'] is True
         and data['manifest_sha256_before'] == data['manifest_sha256_after'] ==
             sha(TASK / reused['manifest'])
         and data['log_sha256'] == data['stdout_and_stderr_sha256'] ==
             sha(TASK / data['log'])
         and data['output_olean_sha256'] == sha(TASK / data['output_olean'])
         and sha(TASK / reused['preflight']['record']) == reused['preflight']['record_sha256'],
         'Reused genuine exact-wire emitter/preflight/OLean differs')
    return raw, reused, body


def solution_source(units, source) -> bytes:
    candidate = ROUTE / ('candidate/Solutions/'
                         'Sol_OAI_PiExponent_LiteralAnalytic_actualRowCount_pos_small_leaf_ap20.lean')
    raw = candidate.read_bytes().replace(b'\r\n', b'\n')
    for row, command in zip(units, source, strict=True):
        if row['name'] == TARGET:
            expected = command.replace(b'theorem actualRowCount_pos', b'theorem solution', 1)
            need(command.count(b'theorem actualRowCount_pos') == 1
                 and raw.count(expected) == 1,
                 'Global target proof differs from exact original AST')
        else:
            need(raw.count(command) == 1,
                 'Original helper source AST/proof is not literal: ' + row['name'])
            raw = raw.replace(command, b'private ' + command, 1)
    need(raw.count(b'private theorem ') == 6
         and raw.count(b'theorem solution ') == 1
         and b'sorry' not in raw
         and ('import ' + MODULE).encode() not in raw,
         'Global closed solution/helper visibility differs')
    return raw


def snapshot(source: bool, helpers: list[str], modules: list[str]) -> bytes:
    raw = (base.STAGE / base.GENERATED_SNAPSHOT).read_text(encoding='utf-8')
    prefix = raw.split('namespace TranslationCountOwnedInventory', 1)[0]
    need('namespace ActualMeanBoundsProofSnapshot' in prefix
         and prefix.startswith('import Lean\n'), 'Actual full-CI snapshot template differs')
    imported = SOURCE_MODULE if source else SOLUTION_MODULE
    prefix = prefix.replace('import ' + base.SOLUTION_MODULE + '\n',
                            'import ' + imported + '\n', 1)
    prefix = prefix.replace('open Lean Meta\n',
                            'set_option maxRecDepth 100000\n\nopen Lean Meta\n', 1)
    if source:
        init = '  let roots := #[' + ', '.join('`' + n for n in helpers + [TARGET]) + ']\n'
    else:
        probe = (base.PROBE.replace('TranslationCountOwnedInventory',
                                    'ActualRowCountOwnedInventory')
                 .replace('Three original source helpers', 'Six original source helpers')
                 .replace('Original translation helper', 'Original actual-row helper'))
        prefix += probe + '\n'
        init = ('  let roots ← ActualRowCountOwnedInventory.exportOwnedInventory #['
                + ', '.join('`' + n for n in helpers) + '] `solution '
                + json.dumps(SOLUTION_MODULE) + ' '
                + json.dumps(ws(STAGE / INVENTORY)) + '\n')
    root_owners = modules if source else [SOLUTION_MODULE]
    ending = ('run_meta do\n' + init
              + '  PiExponentInterfaceSnapshot.exportSnapshot roots '
              + json.dumps(ws(STAGE / (SOURCE_TYPES if source else GENERATED_TYPES))) + '\n'
              + '  ActualMeanBoundsProofSnapshot.exportBundle '
              + json.dumps('source' if source else 'generated') + ' '
              + json.dumps(ws(STAGE / (SOURCE_REFS if source else GENERATED_REFS)))
              + ' roots #[' + ', '.join(json.dumps(x) for x in root_owners) + '] #[]\n'
              + '#print axioms ' + (TARGET if source else 'solution') + '\n')
    return (prefix + ending).encode('utf-8')


def staged_files() -> dict[str, bytes]:
    route, units, original = route_units()
    wire, reused, body = published_wire()
    helpers = route['helper_names']
    modules = list(dict.fromkeys(r['source_module'] for r in units))
    need(units[-1]['source_module'] == SOURCE_MODULE,
         'Original target source module/order differs')
    source = snapshot(True, helpers, modules)
    generated = snapshot(False, helpers, modules)
    outputs = {TARGET_OUTPUT: wire,
               SOLUTION_OUTPUT: solution_source(units, original),
               SOURCE_SNAPSHOT: source, GENERATED_SNAPSHOT: generated}
    pins = [SELF, TASK / 'scripts/certify_actual_row_count_pos_node.py',
            ROUTE / 'source-route.json',
            ROUTE / ('candidate/Solutions/'
                     'Sol_OAI_PiExponent_LiteralAnalytic_actualRowCount_pos_small_leaf_ap20.lean'),
            PUBLISHED, SOURCE_PREPARATION, TASK / reused['source'],
            TASK / reused['manifest'], TASK / reused['preflight']['record'],
            TASK / reused['preflight']['data']['log'],
            DATA_CERT, DATA_PUBLISHED, CLOSURE,
            base.STAGE / base.GENERATED_SNAPSHOT,
            RUNNER, LEGACY, RUNTIME]
    for row in units:
        pins.extend([TASK / row['source'], TASK / row['original']])
        name = row['name'].replace('.', '_') + '.lean.txt'
        pins.extend([ROUTE / 'port-source-units' / name,
                     ROUTE / 'original-source-units' / name])
    input_hashes = {rel(path): sha(path) for path in dict.fromkeys(pins)}
    commands = []
    for i, name in enumerate(FILES[1:], 2):
        mode = MODES[i - 1]
        imports = [line[7:] for line in outputs[name].decode().splitlines()
                   if line.startswith('import ')]
        manifest = {'schema_version': 1,
                    'artifact_kind': 'ap21-actual-row-count-seven-original-AST-bounded-manifest',
                    'output': ws(STAGE / name), 'output_sha256': digest(outputs[name]),
                    'imports': imports, 'input_hashes': input_hashes,
                    'runtime_sha256': sha(RUNTIME), 'mode': mode,
                    'emit_olean': mode == 'emit-olean', 'timeout_seconds': 300,
                    'bounded_runner': rel(RUNNER), 'bounded_runner_sha256': sha(RUNNER),
                    'legacy_runner_sha256': sha(LEGACY),
                    'validated': False, 'submission_ready': False}
        outputs[f'c{i}.json'] = encode(manifest)
        commands.append('python scripts/preflight_staged_module_windows_bounded.py '
                        + vr(STAGE / name) + ' --root ap21/actual-row-count-pos-node'
                        + ' --imports-manifest ap21/actual-row-count-pos-node/c'
                        + str(i) + '.json --timeout-seconds 300'
                        + (' --emit-olean' if mode == 'emit-olean' else ''))
    outputs['compile-commands.txt'] = ('\n'.join(commands) + '\n').encode()
    outputs['preparation.json'] = encode({
        'schema_version': 1,
        'artifact_kind': 'ap21-actual-row-count-seven-original-AST-proof-preparation',
        'source_commit': 'adc7f1241b42e322a6451854ab7e4b4c146bf78a',
        'source_name': TARGET, 'platform_name': TARGET,
        'platform_theorem_id': TARGET_ID, 'platform_module': MODULE,
        'solution_module': SOLUTION_MODULE,
        'exact_source_units': units, 'original_AST_count': 7,
        'original_source_lines': 53,
        'original_proof_suffixes_unchanged': True,
        'six_helper_private_visibility_prefix_only': True,
        'target_global_solution_name_only_rewritten': True,
        'platform_wire_sha256': digest(wire),
        'published_target_readback_sha256': sha(PUBLISHED),
        'reused_original_stub_context': {
            'source': reused['source'], 'manifest': reused['manifest'],
            'root': reused['root'], 'preflight': reused['preflight']['record'],
            'preflight_sha256': reused['preflight']['record_sha256'],
            'output_olean': reused['preflight']['data']['output_olean'],
            'output_olean_sha256': reused['preflight']['data']['output_olean_sha256'],
            'seconds': reused['preflight']['data']['seconds'],
            'sorryAx_comparator_only': True},
        'source_type_only_names': helpers + [TARGET],
        'generated_private_helper_names_discovered_by_actual_probe': True,
        'raw_actual_owned_CI_inventory_first': INVENTORY,
        'full_source_and_generated_proof_reference_outputs': [SOURCE_REFS, GENERATED_REFS],
        'theorem_type_only_values_null': True,
        'finite_metadata_maxRecDepth': 100000,
        'published_data_certificate': rel(DATA_CERT),
        'published_data_record': rel(DATA_PUBLISHED),
        'actual_source_type_import_closure_audit': rel(CLOSURE),
        'source_modules': modules,
        'files': [{'output': name, 'mode': mode,
                   'sha256': digest(outputs[name]),
                   'manifest': None if i == 1 else f'c{i}.json'}
                  for i, (name, mode) in enumerate(zip(FILES, MODES, strict=True), 1)],
        'input_hashes': input_hashes, 'compile_commands': commands,
        'actual_new_compiler_contexts': 3, 'actual_reused_compiler_contexts': 1,
        'proposal_status': 'Draft', 'validated': False, 'submission_ready': False,
        'Lean_started_by_producer': False, 'API_used': False})
    return outputs


def check_only():
    outputs = staged_files()
    for name, raw in outputs.items():
        need((STAGE / name).is_file() and (STAGE / name).read_bytes() == raw,
             'Frozen AP21 staged file changed: ' + name)
    for index, name in enumerate(FILES[1:], 2):
        manifest = read(STAGE / f'c{index}.json')
        runner.verify_manifest_inputs(manifest)
        runner.verify_source_certificate(STAGE / name, manifest)
    return {'files': len(outputs), 'contexts': 4, 'new_contexts': 3,
            'reused_contexts': 1, 'original_AST_count': 7,
            'original_source_lines': 53, 'pure_stage_verified': True,
            'Lean_started_by_producer': False, 'API_used': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--prepare', action='store_true')
    mode.add_argument('--check-only', action='store_true')
    args = parser.parse_args()
    if args.prepare:
        for name, raw in staged_files().items():
            path = STAGE / name
            if path.exists():
                need(path.read_bytes() == raw, 'Refusing AP21 staged overwrite: ' + name)
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(raw)
    print(json.dumps(check_only(), ensure_ascii=False))


if __name__ == '__main__':
    main()
