"""Pure four-context stage for the literal collision remainder limit proof."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import stage_collision_remainder_limit_route as route
import stage_grouped_actual_mean_bounds_node as probe
import stage_log_div_child_mirror as inventory
import preflight_staged_module as runner

TASK, V = route.TASK, route.V
ROOT = TASK.parents[1]
SELF = Path(__file__).resolve()
STAGE = V / 'ap20/collision-remainder-limit-v2'
ROUTE = route.STAGE
TARGET = route.TARGET
HELPER = route.SPECS[0][0]
TARGET_MODULE = 'OAI.NumberTheory.PiExponent.Analysis.Collision'
SOLUTION_MODULE = 'Solutions.Sol_collision_remainder_limit_ap20'
TARGET_OUTPUT = 'Theorems/Thm_' + TARGET.replace('.', '_') + '.lean'
SOLUTION_OUTPUT = SOLUTION_MODULE.replace('.', '/') + '.lean'
SOURCE_SNAPSHOT = 'SourceSnapshot.lean'
GENERATED_SNAPSHOT = 'GeneratedSnapshot.lean'
SOURCE_TYPE_JSON, GENERATED_TYPE_JSON = 'source-types.json', 'generated-types.json'
SOURCE_REFS_JSON, GENERATED_REFS_JSON = 'source-proof-references.json', 'generated-proof-references.json'
OWNED_JSON = 'actual-owned-CI-inventory.json'
FILES = [TARGET_OUTPUT, SOLUTION_OUTPUT, SOURCE_SNAPSHOT, GENERATED_SNAPSHOT]
MODES = ['modecheck', 'emit-olean', 'modecheck', 'modecheck']
MANIFESTS = ['c1.json', 'c2.json', 'c3.json', 'c4.json']
CERTIFICATE = 'node-validation.json'
DATA_STAGE = V / 'ap19/analytic-remainder-data'
DATA_CERT = V / 'ap19/analytic-remainder-auto-ci-validation-v5/actual-provider-validation-auto-ci-v5.json'
DATA_PUBLICATION = DATA_STAGE / 'publication-v4/publication.json'
CHILD_STAGE = V / 'ap19/log-div-child-mirror'
CHILD_CERT = CHILD_STAGE / 'local-child-validation.json'
SNAPSHOT_CORE = V / 'TypeOnlyTheoremSnapshotCore.inc'
RUNTIME = V / 'lean-runtime.json'

read, sha, sha_bytes, encode, need, rel = route.read, route.sha, route.data.sha_bytes, route.encode, route.need, route.rel


def ws(path):
    return Path(path).resolve().relative_to(ROOT.resolve()).as_posix()


def vr(path):
    return Path(path).resolve().relative_to(V.resolve()).as_posix()


def authority():
    rows, pins, closure = route.source_units()
    routed = route.files()
    for name, raw in routed.items():
        need((ROUTE / name).is_file() and (ROUTE / name).read_bytes() == raw,
             'Frozen source-only route differs: ' + name)
    data = read(DATA_CERT)
    publication = read(DATA_PUBLICATION)
    child = read(CHILD_CERT)
    need(data['validated'] is True and data['Std3_only'] is True,
         'RemainderData full-Def certificate is not validated')
    body = publication['target_readback']['body']
    submitted_wire = publication['publish_intent']['payload']['definition']
    need(publication['definition_id'] == '04008248-130e-40ba-b6a3-df3e9b9df91b'
         and publication['last_publish_verdict']['body']['status'] == 'PUBLISHED'
         and body['status'] == 'Definition' and body['visibility'] == 'public'
         and body['definition'] == submitted_wire and body['deprecated_at'] is None,
         'Actual public RemainderData body differs')
    need(child['Std3_only'] is True and child['accepted_theorem_id'] == '8b1c0341-2978-4a9d-8acc-8a5e3538cbda'
         and child['public_platform_boundary_names'] == [route.PARENT]
         and sha(TASK / child['provider_olean']) == child['provider_olean_sha256'],
         'Actual closed LogDiv original-name mirror differs')
    for p in [SELF, ROUTE / 'route-preparation.json', ROUTE / 'candidate/Target.lean',
              ROUTE / 'candidate/Sol.lean', ROUTE / 'metadata.json', DATA_CERT,
              DATA_PUBLICATION, CHILD_CERT, TASK / child['provider_olean'],
              SNAPSHOT_CORE, RUNTIME, Path(probe.__file__), Path(probe.base.ap8.__file__),
              Path(inventory.__file__),
              Path(runner.__file__)]:
        if p.resolve().is_relative_to(TASK.resolve()):
            pins[rel(p)] = sha(p)
    return rows, pins, closure, child


def snapshot(side, names, boundary):
    module = TARGET_MODULE if side == 'source' else SOLUTION_MODULE
    owners = [TARGET_MODULE, 'OAI.NumberTheory.PiExponent.Polynomials.SimplexLog'] if side == 'source' else [SOLUTION_MODULE]
    out = SOURCE_TYPE_JSON if side == 'source' else GENERATED_TYPE_JSON
    refs = SOURCE_REFS_JSON if side == 'source' else GENERATED_REFS_JSON
    roots = '#[' + ', '.join('`' + n for n in names) + ']'
    owned = '' if side == 'source' else inventory.INVENTORY
    early = '' if side == 'source' else ('  LogDivOwnedInventory.exportInventory `solution '
              + json.dumps(SOLUTION_MODULE) + ' ' + json.dumps(ws(STAGE / OWNED_JSON)) + '\n')
    return ('import Lean\nimport ' + module + '\n\n' + SNAPSHOT_CORE.read_text(encoding='utf-8').rstrip()
            + '\n' + probe.base.ap8.PROBE + '\n' + probe.PROBE + '\n' + owned
            + '\nrun_meta do\n' + early + '  PiExponentInterfaceSnapshot.exportSnapshot ' + roots + ' ' + json.dumps(ws(STAGE / out))
            + '\n  ActualMeanBoundsProofSnapshot.exportBundle ' + json.dumps(side) + ' '
            + json.dumps(ws(STAGE / refs)) + ' ' + roots + ' #['
            + ', '.join(json.dumps(x) for x in owners) + '] #['
            + ', '.join(json.dumps(x) for x in sorted(boundary)) + ']\n#print axioms ' + names[-1] + '\n').encode()


def stage_files():
    rows, pins, closure, child = authority()
    boundary = {route.PARENT, route.data.NAMES[0], route.data.NAMES[1]}
    target = (ROUTE / 'candidate/Target.lean').read_bytes()
    solution = (ROUTE / 'candidate/Sol.lean').read_bytes()
    need(solution.count(('import ' + route.PARENT_MODULE + '\n').encode()) == 1
         and solution.count(rows[0]['bytes']) == 1,
         'Literal original helper or actual public child import differs')
    target_proof = rows[1]['bytes'][rows[1]['ast']['valueStart']['offset'] - rows[1]['start']:]
    need(solution.rstrip(b'\r\n').endswith(target_proof), 'Literal original target proof differs')
    generated = {
        TARGET_OUTPUT: target, SOLUTION_OUTPUT: solution,
        SOURCE_SNAPSHOT: snapshot('source', [HELPER, TARGET], boundary),
        GENERATED_SNAPSHOT: snapshot('generated', [HELPER, 'solution'], boundary),
        'wire-theorem-source.lean': target,
        'academic-metadata.json': (ROUTE / 'metadata.json').read_bytes(),
    }
    for p in [ROUTE / 'candidate/preamble.lean', ROUTE / 'candidate/formal-statement.lean']:
        pins[rel(p)] = sha(p)
    pins[rel(SELF)] = sha(SELF)
    files = {}
    commands = []
    import_rows = [route.IMPORTS, route.IMPORTS + [route.PARENT_MODULE],
                   ['Lean', TARGET_MODULE], ['Lean', SOLUTION_MODULE]]
    for output, mode, manifest, imports in zip(FILES, MODES, MANIFESTS, import_rows, strict=True):
        files[output] = {'sha256': sha_bytes(generated[output]), 'mode': mode,
                         'emit_olean': mode == 'emit-olean', 'manifest': manifest,
                         'imports': imports}
        generated[manifest] = encode({'schema_version': 1,
            'artifact_kind': 'ap20-collision-remainder-bounded-manifest',
            'output': ws(STAGE / output), 'output_sha256': sha_bytes(generated[output]),
            'imports': imports, 'input_hashes': pins, 'runtime_sha256': sha(RUNTIME),
            'mode': mode, 'emit_olean': mode == 'emit-olean', 'timeout_seconds': 300,
            'validated': False, 'submission_ready': False})
        commands.append('python scripts/preflight_staged_module_windows_bounded.py ' + vr(STAGE / output)
                        + ' --root ap20/collision-remainder-limit-v2 --imports-manifest '
                        + vr(STAGE / manifest) + ' --timeout-seconds 300'
                        + (' --emit-olean' if mode == 'emit-olean' else ''))
    generated['compile-commands.txt'] = ('\n'.join(commands) + '\n').encode()
    generated['preparation.json'] = encode({'schema_version': 1,
        'artifact_kind': 'ap20-collision-remainder-literal-proof-preparation',
        'source_commit': route.data.COMMIT, 'source_name': TARGET, 'platform_name': TARGET,
        'exact_source_units': [{k: v for k, v in row.items() if k != 'bytes'} for row in rows],
        'source_line_count': 15, 'original_proof_suffixes_unchanged': True,
        'accepted_child': route.PARENT, 'accepted_child_theorem_id': child['accepted_theorem_id'],
        'provider_boundary_names': sorted(boundary), 'source_closure': sorted(closure),
        'source_type_only_names': [HELPER, TARGET],
        'generated_type_only_names': [HELPER, 'solution'],
        'source_theorem_values_null': True, 'generated_theorem_values_null': True,
        'generated_raw_owned_inventory': OWNED_JSON,
        'source_module': TARGET_MODULE, 'solution_module': SOLUTION_MODULE,
        'input_hashes': pins, 'files': files, 'compile_commands': commands,
        'metadata': read(ROUTE / 'metadata.json'), 'proposal_status': 'Draft',
        'validated': False, 'submission_ready': False, 'Lean_started': False,
        'API_used': False})
    return generated


def check_only():
    generated = stage_files()
    for name, raw in generated.items():
        need((STAGE / name).is_file() and (STAGE / name).read_bytes() == raw,
             'Staged bytes changed: ' + name)
    for output, manifest in zip(FILES, MANIFESTS, strict=True):
        m = read(STAGE / manifest)
        runner.verify_manifest_inputs(m)
        runner.verify_source_certificate(STAGE / output, m)
    return {'files': len(generated), 'exact_source_AST_units': 2,
            'original_source_lines': 15, 'pure_stage_verified': True,
            'compiler_started': False, 'API_used': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--prepare', action='store_true')
    group.add_argument('--check-only', action='store_true')
    args = parser.parse_args()
    if args.prepare:
        for name, raw in stage_files().items():
            path = STAGE / name
            if path.exists():
                need(path.read_bytes() == raw, 'Refusing to overwrite staged file: ' + name)
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(raw)
    print(json.dumps(check_only(), ensure_ascii=False))


if __name__ == '__main__':
    main()
