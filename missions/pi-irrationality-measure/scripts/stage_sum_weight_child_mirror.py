"""Stage the original-name Collision weight child with one private source helper."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import stage_translated_summand_bound_route as route
import stage_selected_minor_clearing_bound_node as core

TASK, ROOT, V = route.TASK, route.ROOT, route.V
SELF = Path(__file__).resolve()
STAGE = V / 'ap18/sum-weight-child-mirror-v5'
SOURCE_MODULE = 'OAI.NumberTheory.PiExponent.Analysis.CollisionCombinatorics'
MODULE = 'Theorems.Thm_OAI_PiExponent_Collision_sum_weight_ge_of_low_count_le'
OUTPUT = MODULE.replace('.', '/') + '.lean'
SOURCE_SNAPSHOT = 'SourceSnapshot.lean'
GENERATED_SNAPSHOT = 'GeneratedSnapshot.lean'
SOURCE_TYPE_JSON = 'source-types.json'
GENERATED_TYPE_JSON = 'generated-types.json'
SOURCE_REFS_JSON = 'source-proof-references.json'
GENERATED_REFS_JSON = 'generated-proof-references.json'
MAPPING_JSON = 'actual-private-mapping.json'
CERTIFICATE = 'local-child-validation.json'
HELPER = 'OAI.PiExponent.Collision.cutoff_mul_high_count_le_sum'
TARGET = route.PARENT
RANGES = [(HELPER, 5428, 6192), (TARGET, 6196, 7240)]
RUNNER = TASK / 'scripts/preflight_staged_module_windows_bounded.py'
LEGACY_RUNNER = TASK / 'scripts/preflight_staged_module.py'
CONSUMER = TASK / 'scripts/certify_sum_weight_child_mirror.py'
OLD = route.PARENT_STAGE
OLD_SOL = OLD / 'Sol_OAI_PiExponent_Collision_sum_weight_ge_of_low_count_le.lean'
OLD_THM = OLD / 'Thm_OAI_PiExponent_Collision_sum_weight_ge_of_low_count_le.lean'
SOURCE = TASK / 'port/lean/OAI/NumberTheory/PiExponent/Analysis/CollisionCombinatorics.lean'
ORIGINAL = TASK / 'source/lean/OAI/NumberTheory/PiExponent/Analysis/CollisionCombinatorics.lean'
read, sha, sha_bytes, encode, need, rel = (route.read, route.sha, route.sha_bytes,
                                          route.encode, route.need, route.rel)


def source_units():
    ast, scopes = read(route.data.ap9.AST), read(route.data.ap9.SCOPES)
    module = next(m for m in ast['modules'] if m['module'] == SOURCE_MODULE)
    scope_module = next(m for m in scopes['modules']
                        if m['source'] == SOURCE_MODULE.replace('.', '/') + '.lean')
    raw, original = SOURCE.read_bytes(), ORIGINAL.read_bytes().replace(b'\r\n', b'\n')
    need(module['source_sha256'] == scope_module['source_sha256'] == sha(SOURCE),
         'Collision original AST/scope source hash differs')
    rows = []
    for name, start, end in RANGES:
        unit = next(u for u in module['units'] if name in u['graph_names'])
        scope = next(s for s in scope_module['declarations'] if s['verified_name'] == name)
        command = raw[start:end]
        contexts = [raw[c['range']['start']['offset']:c['range']['end']['offset']].decode()
                    for c in scope['context_commands']]
        value = unit['valueStart']['offset'] - start
        need([unit['start']['offset'], unit['end']['offset']] == [start, end]
             and unit['graph_names'] == [name] and unit['graph_kinds'] == ['theorem']
             and unit['privateTok'] is None and not unit['is_instance_command']
             and not unit['is_local_instance'] and scope['namespace'] == 'OAI.PiExponent.Collision'
             and [s['kind'] for s in scope['scope_stack']] == ['namespace'] * 3
             and contexts == ['open scoped BigOperators']
             and original.count(command.replace(b'\r\n', b'\n')) == 1
             and command[value:value + 5] == b':= by',
             'Original Collision theorem AST, proof, or scope differs: ' + name)
        rows.append({'name': name, 'module': SOURCE_MODULE, 'source': rel(SOURCE),
                     'source_sha256': sha(SOURCE), 'original': rel(ORIGINAL),
                     'original_sha256': sha(ORIGINAL), 'start': start, 'end': end,
                     'source_lines': unit['end']['line'] - unit['start']['line'] + 1,
                     'command_sha256': sha_bytes(command),
                     'proof_suffix_sha256': sha_bytes(command[value:]),
                     'scope': scope, 'ast': unit, 'command': command})
    need([r['source_lines'] for r in rows] == [17, 18],
         'Original two-Collision-theorem line count differs')
    pub, historical = read(OLD / 'publication.json'), read(OLD / 'validation.json')
    body = pub['target_readback']['body']
    need(MODULE == 'Theorems.' + OLD_THM.stem
         and MODULE == 'Theorems.Thm_' + TARGET.replace('.', '_'),
         'Accepted public theorem standard import-module naming differs')
    need(pub['confirmed_proved'] is True and pub['theorem_id'] ==
         '84999320-3725-4c17-b1cb-428d9f92f6cc' and pub['submission_id'] ==
         '78ad72fd-0fdd-44e6-93c7-f0e607baa6fa' and body['status'] == 'Proved'
         and body['theorem_name'] == TARGET
         and body['theorem_id'] == pub['theorem_id']
         and body['mathlib_rev'] == '0df444a360eaa60ab8c11dca51a86af692955474'
         and body['visibility'] == 'public'
         and pub['last_verify_verdict']['body']['status'] == 'ACCEPTED'
         and (body['preamble'] + body['formal_statement']).encode() == OLD_THM.read_bytes()
         and sha(OLD_SOL) == pub['verify_intent']['solution_sha256']
         and historical['validated'] is True and historical['kernel_types_equal'] is True
         and historical['standard_axioms_only'] is True,
         'Genuine Accepted weight theorem historical proof/type/wire differs')
    return rows, pub, historical


def imports():
    lines = OLD_SOL.read_text(encoding='utf-8').splitlines()
    result = [line.removeprefix('import ').strip() for line in lines
              if line.startswith('import ')]
    need(len(result) == 18 and len(set(result)) == 18 and
         all(name.startswith('Mathlib.') for name in result),
         'Historically successful Mathlib import profile differs')
    return result


RESOLVER = r'''
namespace SumWeightPrivateMirrorSnapshot
open Lean Meta FullRowMinorProofSnapshot

def resolve (helper target : Name) (moduleName output : String) : MetaM (Array Name) := do
  let env ← getEnv
  let some moduleIndex := env.getModuleIdxFor? target
    | throwError "Public Collision target has no imported module owner"
  unless env.header.moduleNames[moduleIndex.toNat]?.map Name.toString == some moduleName &&
      (Lean.privateToUserName? target).isNone do
    throwError "Collision target is not the actual public original-name theorem"
  unless (env.find? helper).isNone do
    throwError "Original cutoff helper was exposed publicly"
  let mut helpers : Array Name := #[]
  let mut privateNames : Array Name := #[]
  let mut publicNames : Array Name := #[]
  for (actualName, _) in env.constants.toList do
    if env.getModuleIdxFor? actualName == some moduleIndex then
      match Lean.privateToUserName? actualName with
      | some userName =>
          privateNames := privateNames.push actualName
          if userName == helper then helpers := helpers.push actualName
      | none => publicNames := publicNames.push actualName
  unless helpers.size == 1 && privateNames.size == 1 &&
      privateNames[0]! == helpers[0]! do
    throwError "Owned private CI inventory differs from the sole source cutoff helper"
  let actualHelper := helpers[0]!
  let some helperCI := env.find? actualHelper
    | throwError "Actual cutoff helper CI is missing"
  match helperCI with
  | .thmInfo _ => pure ()
  | _ => throwError "Actual private cutoff helper is not a theorem"
  publicNames := publicNames.qsort (fun a b => a.toString < b.toString)
  let mut publicRows : Array Json := #[]
  for name in publicNames do
    let some ci := env.find? name | throwError "Owned public Collision CI vanished"
    match ci with
    | .thmInfo _ => pure ()
    | _ => throwError "Owned public Collision CI is not a theorem"
    publicRows := publicRows.push <| Json.mkObj [
      ("actualName",toJson name.toString),
      ("actualIsProp",toJson (← isProp ci.type)),
      ("CI",Json.mkObj (← ciRow name true))]
  IO.FS.writeFile output <| (Json.mkObj [
    ("schemaVersion",toJson (1 : Nat)),
    ("probeMainModule",toJson env.mainModule.toString),
    ("mirrorModule",toJson moduleName),
    ("sourceHelper",toJson helper.toString),
    ("actualPrivateHelper",toJson actualHelper.toString),
    ("actualPrivateUserName",toJson ((Lean.privateToUserName? actualHelper).map Name.toString)),
    ("actualOwnedPrivateNames",toJson (privateNames.map Name.toString)),
    ("privateOwner",← ownerOf env actualHelper),
    ("publicTarget",toJson target.toString),
    ("actualOwnedPublicNames",toJson (publicNames.map Name.toString)),
    ("actualOwnedPublicCIs",Json.arr publicRows)]).compress
  return #[actualHelper, target]
end SumWeightPrivateMirrorSnapshot
'''


def snapshot(side: str) -> bytes:
    source = side == 'source'
    module = SOURCE_MODULE if source else MODULE
    type_file = SOURCE_TYPE_JSON if source else GENERATED_TYPE_JSON
    refs_file = SOURCE_REFS_JSON if source else GENERATED_REFS_JSON
    roots = '#[`' + HELPER + ', `' + TARGET + ']'
    prefix = ('import Lean\nimport ' + module + '\n\n'
              + core.SNAPSHOT_CORE.read_text(encoding='utf-8').rstrip() + '\n'
              + core.base.ap8.PROBE + '\n' + core.PROBE + '\n')
    if source:
        init = '  let roots := ' + roots + '\n'
    else:
        prefix += RESOLVER + '\n'
        init = ('  let roots ← SumWeightPrivateMirrorSnapshot.resolve `'+HELPER+' `'+TARGET+' '
                + json.dumps(MODULE) + ' '
                + json.dumps(core.workspace_rel(STAGE / MAPPING_JSON)) + '\n')
    owner = SOURCE_MODULE if source else MODULE
    return (prefix + 'run_meta do\n' + init
            + '  PiExponentInterfaceSnapshot.exportSnapshot roots '
            + json.dumps(core.workspace_rel(STAGE / type_file)) + '\n'
            + '  SelectedMinorProofSnapshot.exportBundle ' + json.dumps(side) + ' '
            + json.dumps(core.workspace_rel(STAGE / refs_file)) + ' roots #['
            + json.dumps(owner) + '] #[]\n'
            + '#print axioms ' + TARGET + '\n').encode()


def staged_files():
    rows, pub, historical = source_units()
    profile = imports()
    helper, target = (r['command'] for r in rows)
    need(helper.startswith(b'theorem cutoff_mul_high_count_le_sum') and
         target.startswith(b'theorem sum_weight_ge_of_low_count_le'),
         'Actual original theorem command prefix differs')
    body = (''.join('import ' + name + '\n' for name in profile)
            + '\nnamespace OAI\n\nopen scoped BigOperators\n\n'
            + 'namespace PiExponent.Collision\n\n').encode()
    body += b'private ' + helper + b'\n\n' + target
    body += b'\n\nend PiExponent.Collision\n\nend OAI\n\n'
    need(body.count(b'private theorem ') == 1 and body.count(b'\ntheorem sum_weight_ge_of_low_count_le') == 1
         and b'sorry' not in body and b'import Solutions.' not in body and
         body[body.index(b'private theorem ') + len(b'private '):].startswith(helper),
         'Original child mirror proof bytes/public-private boundary differs')
    paths = [SELF, CONSUMER, route.SELF, route.data.ap9.AST, route.data.ap9.SCOPES,
             SOURCE, ORIGINAL, OLD / 'publication.json', OLD / 'validation.json',
             OLD / 'original-type.json', OLD / 'generated-type.json', OLD_SOL,
             OLD_THM, core.SNAPSHOT_CORE, Path(core.base.ap8.__file__),
             Path(core.__file__), RUNNER, LEGACY_RUNNER,
             route.STAGE / 'route-preparation.json']
    pins = {rel(path): sha(path) for path in paths}
    files = {OUTPUT: body, SOURCE_SNAPSHOT: snapshot('source'),
             GENERATED_SNAPSHOT: snapshot('generated')}
    commands = []
    for i, (output, imps, mode) in enumerate([
            (OUTPUT, profile, 'emit-olean'),
            (SOURCE_SNAPSHOT, ['Lean', SOURCE_MODULE], 'modecheck'),
            (GENERATED_SNAPSHOT, ['Lean', MODULE], 'modecheck')], 1):
        manifest = {'schema_version': 1, 'artifact_kind': 'ap18-sum-weight-child-bounded-manifest',
                    'output': core.workspace_rel(STAGE / output),
                    'output_sha256': sha_bytes(files[output]), 'imports': imps,
                    'input_hashes': pins, 'runtime_sha256': sha(core.RUNTIME),
                    'mode': mode, 'emit_olean': mode == 'emit-olean',
                    'timeout_seconds': 300, 'bounded_runner': rel(RUNNER),
                    'bounded_runner_sha256': sha(RUNNER),
                    'legacy_runner_sha256': sha(LEGACY_RUNNER),
                    'validated': False, 'submission_ready': False}
        files[f'c{i}.json'] = encode(manifest)
        commands.append('python scripts/preflight_staged_module_windows_bounded.py '
                        + core.verification_rel(STAGE / output)
                        + ' --root ap18/sum-weight-child-mirror-v5 --imports-manifest '
                        + f'ap18/sum-weight-child-mirror-v5/c{i}.json --timeout-seconds 300'
                        + (' --emit-olean' if mode == 'emit-olean' else ''))
    prep = {'schema_version': 1, 'artifact_kind': 'ap18-sum-weight-original-name-private-child-preparation',
            'source_commit': route.data.COMMIT, 'source_module': SOURCE_MODULE,
            'platform_module': MODULE, 'source_units': [{k: v for k, v in row.items()
                                                       if k != 'command'} for row in rows],
            'private_helper_names': [HELPER], 'public_platform_boundary_names': [TARGET],
            'original_AST_units': 2, 'original_source_lines': 35,
            'only_private_visibility_prefix_added': True,
            'all_original_proof_suffixes_unchanged': True,
            'historical_Accepted_theorem_id': pub['theorem_id'],
            'historical_Accepted_proof_id': pub['submission_id'],
            'historical_accepted_publication_sha256': sha(OLD / 'publication.json'),
            'historical_source_type_sha256': sha(OLD / 'original-type.json'),
            'historical_generated_type_sha256': sha(OLD / 'generated-type.json'),
            'historical_standard_axioms_only': historical['standard_axioms_only'],
            'compiler_manifests_finalized': True, 'input_hashes': pins,
            'compile_commands': commands, 'validated': False,
            'submission_ready': False, 'Lean_started': False, 'API_used': False}
    files['preparation.json'] = encode(prep)
    files['compile-commands.txt'] = ('\n'.join(commands) + '\n').encode()
    return files


def check_only():
    files = staged_files()
    for name, raw in files.items():
        need((STAGE / name).read_bytes() == raw, 'Immutable sum-weight child file differs: ' + name)
    for i, output in enumerate([OUTPUT, SOURCE_SNAPSHOT, GENERATED_SNAPSHOT], 1):
        manifest = read(STAGE / f'c{i}.json')
        core.base.runner.verify_manifest_inputs(manifest)
        core.base.runner.verify_source_certificate(STAGE / output, manifest)
    return {'checked_files': len(files), 'original_AST_units': 2,
            'private_helper_count': 1, 'public_platform_boundary_names': [TARGET],
            'validated': False, 'Lean_started': False, 'API_used': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--prepare', action='store_true')
    group.add_argument('--check-only', action='store_true')
    args = parser.parse_args()
    if args.prepare:
        for name, raw in staged_files().items():
            path = STAGE / name
            if path.exists():
                need(path.read_bytes() == raw, 'Refusing overwrite: ' + name)
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(raw)
    print(json.dumps(check_only(), ensure_ascii=False, indent=2))


if __name__ == '__main__':
    main()
