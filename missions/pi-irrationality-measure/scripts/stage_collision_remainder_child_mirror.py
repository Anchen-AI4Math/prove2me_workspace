"""Freeze two bounded contexts for the genuine original-name Collision child mirror."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import prepare_collision_remainder_child_mirror_candidate as candidate
import stage_collision_remainder_limit_node_v2 as old
import preflight_staged_module as runner

TASK, V, MODULE = candidate.TASK, old.V, candidate.MODULE
STAGE = V / 'ap20/collision-remainder-child-mirror-final'
SELF = Path(__file__).resolve()
OUTPUT = MODULE.replace('.', '/') + '.lean'
SNAPSHOT = 'GeneratedSnapshot.lean'
TYPES = 'generated-types.json'
REFS = 'generated-proof-references.json'
INVENTORY = 'actual-owned-CI-inventory.json'
CERTIFICATE = 'local-child-validation.json'
RUNNER = TASK / 'scripts/preflight_staged_module_windows_bounded.py'
LEGACY = TASK / 'scripts/preflight_staged_module.py'
PUB = old.STAGE / 'publication-v3/publication.json'
SOURCE_TYPES = old.STAGE / old.SOURCE_TYPE_JSON
SOURCE_REFS = old.STAGE / old.SOURCE_REFS_JSON
SOURCE_CERT = old.STAGE / 'node-validation-v3.json'
TARGET, HELPER = candidate.TARGET, candidate.HELPER
SHA = candidate.sha
BYTE_SHA = candidate.digest


def ws(path: Path) -> str:
    return path.resolve().relative_to(TASK.parents[1].resolve()).as_posix()


def vr(path: Path) -> str:
    return path.resolve().relative_to(V.resolve()).as_posix()


def rel(path: Path) -> str:
    return path.resolve().relative_to(TASK.resolve()).as_posix()


def encoded(value: object) -> bytes:
    return (json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode()


RESOLVER = r'''
namespace CollisionRemainderPrivateMirrorSnapshot
open Lean Meta FullRowMinorProofSnapshot

def resolve (helper target : Name) (moduleName output : String) : MetaM (Array Name) := do
  let env ← getEnv
  let some moduleIndex := env.getModuleIdxFor? target
    | throwError "Original-name Collision target has no imported owner"
  unless env.header.moduleNames[moduleIndex.toNat]?.map Name.toString == some moduleName &&
      (Lean.privateToUserName? target).isNone && (env.find? helper).isNone do
    throwError "Collision target owner or private helper boundary differs"
  let mut names : Array Name := #[]
  let mut helpers : Array Name := #[]
  for (n, _) in env.constants.toList do
    if env.getModuleIdxFor? n == some moduleIndex then
      names := names.push n
      if Lean.privateToUserName? n == some helper then helpers := helpers.push n
  unless helpers.size == 1 do
    throwError "Actual private source helper is not uniquely resolved"
  names := names.qsort (fun a b => a.toString < b.toString)
  let mut rows : Array Json := #[]
  for n in names do
    let some ci := env.find? n | throwError "Owned Collision CI disappeared"
    let kind := match ci with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "def"
      | _ => "other"
    let value := valueOf ci
    rows := rows.push <| Json.mkObj [
      ("actualName",toJson n.toString), ("kind",toJson kind),
      ("privateUserName",toJson ((Lean.privateToUserName? n).map Name.toString)),
      ("isProp",toJson (← isProp ci.type)), ("CI",Json.mkObj (← ciRow n true)),
      ("closedValue",toJson (value.map fun v => !v.hasMVar && !v.hasFVar && !v.hasLooseBVars))]
  IO.FS.writeFile output <| (Json.mkObj [
    ("schemaVersion",toJson (1 : Nat)),
    ("probeMainModule",toJson env.mainModule.toString),
    ("mirrorModule",toJson moduleName),
    ("sourceHelper",toJson helper.toString),
    ("actualPrivateHelper",toJson helpers[0]!.toString),
    ("publicTarget",toJson target.toString),
    ("rawOwnedNames",toJson (names.map Name.toString)),
    ("rawOwnedCIs",Json.arr rows)]).compress
  return #[helpers[0]!, target]
end CollisionRemainderPrivateMirrorSnapshot
'''


def snapshot() -> bytes:
    old_raw = (old.STAGE / old.GENERATED_SNAPSHOT).read_text(encoding='utf-8')
    prefix = old_raw.split('namespace LogDivOwnedInventory', 1)[0]
    required = 'import Solutions.Sol_collision_remainder_limit_ap20\n'
    candidate.require(prefix.count(required) == 1, 'Historical snapshot core import differs')
    prefix = prefix.replace(required, 'import ' + MODULE + '\n', 1)
    ending = ('run_meta do\n'
              + '  let roots ← CollisionRemainderPrivateMirrorSnapshot.resolve `'
              + HELPER + ' `' + TARGET + ' ' + json.dumps(MODULE) + ' '
              + json.dumps(ws(STAGE / INVENTORY)) + '\n'
              + '  PiExponentInterfaceSnapshot.exportSnapshot roots '
              + json.dumps(ws(STAGE / TYPES)) + '\n'
              + '  ActualMeanBoundsProofSnapshot.exportBundle "generated" '
              + json.dumps(ws(STAGE / REFS)) + ' roots #[' + json.dumps(MODULE)
              + '] #["OAI.PiExponent.Collision.collisionRatio", '
              + '"OAI.PiExponent.Collision.collisionRemainder", '
              + '"OAI.PiExponent.tendsto_log_div_of_normalized_pow"]\n'
              + '#print axioms ' + TARGET + '\n')
    return (prefix + RESOLVER + '\n' + ending).encode()


def files() -> dict[str, bytes]:
    body, route = candidate.candidate()
    pub = json.loads(PUB.read_text(encoding='utf-8'))
    source_cert = json.loads(SOURCE_CERT.read_text(encoding='utf-8'))
    public = pub['post_accepted_target_readback']['body']
    candidate.require(pub['confirmed_ACCEPTED_and_Proved'] is True
        and pub['last_verify_verdict']['body']['status'] == 'ACCEPTED'
        and pub['theorem_id'] == public['theorem_id'] == '3d02d61e-2783-4a0c-82ca-a411ca66c0fc'
        and pub['submission_id'] == 'f31fb318-a908-4905-beef-f1f9d8d716d3'
        and public['theorem_name'] == TARGET and public['status'] == 'Proved'
        and public['visibility'] == 'public'
        and public['mathlib_rev'] == '0df444a360eaa60ab8c11dca51a86af692955474'
        and (public['preamble'] + public['formal_statement']).encode() ==
            (old.STAGE / old.TARGET_OUTPUT).read_bytes()
        and source_cert['validated'] is True and source_cert['Std3_only'] is True,
        'Historical Accepted public theorem, wire, or source proof certificate differs')
    from_path = old.STAGE / old.SOLUTION_OUTPUT
    candidate.require(SHA(from_path) == pub['verify_intent']['solution_sha256'],
                      'Actual Accepted solution proof bytes differ')
    pins = [SELF, TASK / 'scripts/certify_collision_remainder_child_mirror.py',
            Path(candidate.__file__), candidate.ROUTE / 'route-preparation.json',
            candidate.OUTPUT, candidate.STAGE / 'candidate-preparation.json',
            PUB, SOURCE_TYPES, SOURCE_REFS, SOURCE_CERT,
            old.STAGE / old.GENERATED_SNAPSHOT, old.STAGE / old.SOURCE_SNAPSHOT,
            old.STAGE / 'SourceSnapshot.lean.preflight.json',
            old.STAGE / old.TARGET_OUTPUT, from_path,
            old.DATA_CERT, old.DATA_PUBLICATION, old.CHILD_CERT,
            RUNNER, LEGACY, old.RUNTIME]
    input_hashes = {rel(p): SHA(p) for p in pins}
    imports = [line.removeprefix('import ') for line in body.decode().splitlines()
               if line.startswith('import ')]
    snap = snapshot()
    generated = {OUTPUT: body, SNAPSHOT: snap}
    commands = []
    for index, (name, imps, mode) in enumerate([
            (OUTPUT, imports, 'emit-olean'),
            (SNAPSHOT, ['Lean', MODULE], 'modecheck')], 1):
        manifest = {'schema_version': 1,
            'artifact_kind': 'ap20-collision-remainder-original-name-private-mirror-manifest',
            'output': ws(STAGE / name), 'output_sha256': BYTE_SHA(generated[name]),
            'imports': imps, 'input_hashes': input_hashes,
            'runtime_sha256': SHA(old.RUNTIME), 'mode': mode,
            'emit_olean': mode == 'emit-olean', 'timeout_seconds': 300,
            'bounded_runner': rel(RUNNER), 'bounded_runner_sha256': SHA(RUNNER),
            'legacy_runner_sha256': SHA(LEGACY), 'validated': False,
            'submission_ready': False}
        generated[f'c{index}.json'] = encoded(manifest)
        commands.append('python scripts/preflight_staged_module_windows_bounded.py '
                        + vr(STAGE / name) + ' --root ap20/collision-remainder-child-mirror-final'
                        + ' --imports-manifest ap20/collision-remainder-child-mirror-final/c'
                        + str(index) + '.json --timeout-seconds 300'
                        + (' --emit-olean' if mode == 'emit-olean' else ''))
    generated['compile-commands.txt'] = ('\n'.join(commands) + '\n').encode()
    generated['preparation.json'] = encoded({
        'schema_version': 1, 'artifact_kind': 'ap20-collision-remainder-original-name-private-mirror-preparation',
        'source_commit': route['source_commit'], 'source_units': route['exact_source_units'],
        'original_proof_suffixes_unchanged': True,
        'only_private_visibility_prefix_added': True, 'module': MODULE,
        'public_platform_boundary_names': [TARGET], 'private_helper_names': [HELPER],
        'accepted_theorem_id': pub['theorem_id'], 'accepted_proof_id': pub['submission_id'],
        'reused_actual_source_type_json_sha256': SHA(SOURCE_TYPES),
        'reused_actual_source_proof_references_json_sha256': SHA(SOURCE_REFS),
        'reused_actual_source_snapshot_preflight_sha256': SHA(old.STAGE / 'SourceSnapshot.lean.preflight.json'),
        'input_hashes': input_hashes,
        'files': {name: {'sha256': BYTE_SHA(raw), 'mode':
                  ('emit-olean' if name == OUTPUT else 'modecheck')}
                  for name, raw in list(generated.items())[:2]},
        'compile_commands': commands, 'validated': False,
        'submission_ready': False, 'proposal_status': 'Draft',
        'Lean_started_by_producer': False, 'API_used': False})
    return generated


def check_only() -> dict:
    staged = files()
    for name, raw in staged.items():
        candidate.require((STAGE / name).is_file() and (STAGE / name).read_bytes() == raw,
                          'Frozen mirror output differs: ' + name)
    for i, name in enumerate([OUTPUT, SNAPSHOT], 1):
        manifest = json.loads((STAGE / f'c{i}.json').read_text(encoding='utf-8'))
        runner.verify_manifest_inputs(manifest)
        runner.verify_source_certificate(STAGE / name, manifest)
    return {'files': len(staged), 'actual_source_context_reused': True,
            'new_bounded_contexts': 2, 'pure_stage_verified': True,
            'Lean_started_by_producer': False, 'API_used': False}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    x = parser.add_mutually_exclusive_group(required=True)
    x.add_argument('--prepare', action='store_true')
    x.add_argument('--check-only', action='store_true')
    args = parser.parse_args()
    if args.prepare:
        for name, raw in files().items():
            path = STAGE / name
            if path.exists():
                candidate.require(path.read_bytes() == raw, 'Refusing mirror overwrite: ' + name)
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(raw)
    print(json.dumps(check_only(), ensure_ascii=False))


if __name__ == '__main__':
    main()
