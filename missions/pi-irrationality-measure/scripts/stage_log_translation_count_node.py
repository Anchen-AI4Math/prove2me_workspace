"""Freeze four bounded original-source translation-count proof contexts."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import stage_log_translation_count_route as route
import stage_collision_remainder_limit_node_v2 as snapshot_base
import preflight_staged_module as runner

TASK, V = route.TASK, snapshot_base.V
ROOT = TASK.parents[1]
SELF = Path(__file__).resolve()
STAGE = V / 'ap20/log-translation-term-count-node-v2'
ROUTE = route.STAGE
LOOKUP = V / 'ap20/exact-analytic-remainder-two-frontier-lookup.json'
MODULE = route.MODULE
SOLUTION_MODULE = 'Solutions.Sol_OAI_PiExponent_tendsto_log_translationTermCount_div_ap20'
TARGET = route.TARGET
HELPERS = [r[0] for r in route.SPECS[:3]]
SOURCE_MODULES = [route.SPECS[0][1], route.SPECS[1][1]]
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
RUNNER = TASK / 'scripts/preflight_staged_module_windows_bounded.py'
LEGACY = TASK / 'scripts/preflight_staged_module.py'
RUNTIME = snapshot_base.RUNTIME
FILES = [TARGET_OUTPUT, SOLUTION_OUTPUT, SOURCE_SNAPSHOT, GENERATED_SNAPSHOT]
MODES = ['modecheck', 'emit-olean', 'modecheck', 'modecheck']


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def file_sha(path: Path) -> str:
    return sha(path.read_bytes())


def rel(path: Path) -> str:
    return path.resolve().relative_to(TASK.resolve()).as_posix()


def ws(path: Path) -> str:
    return path.resolve().relative_to(ROOT.resolve()).as_posix()


def vr(path: Path) -> str:
    return path.resolve().relative_to(V.resolve()).as_posix()


def need(cond: bool, reason: str) -> None:
    if not cond:
        raise ValueError(reason)


def encode(value) -> bytes:
    return (json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode()


PROBE = r'''
namespace TranslationCountOwnedInventory
open Lean Meta FullRowMinorProofSnapshot

def exportOwnedInventory (helpers : Array Name) (target : Name)
    (moduleName output : String) : MetaM (Array Name) := do
  let env ← getEnv
  let some moduleIndex := env.getModuleIdxFor? target
    | throwError "Global translation solution has no imported owner"
  unless env.header.moduleNames[moduleIndex.toNat]?.map Name.toString == some moduleName &&
      (Lean.privateToUserName? target).isNone do
    throwError "Global solution owner differs"
  let mut names : Array Name := #[]
  let mut mapped : Array Name := #[]
  for (n, _) in env.constants.toList do
    if env.getModuleIdxFor? n == some moduleIndex then
      names := names.push n
      if let some userName := Lean.privateToUserName? n then
        if helpers.contains userName then mapped := mapped.push n
  unless mapped.size == helpers.size do
    throwError "Three original source helpers were not uniquely resolved as private CIs"
  let mut roots : Array Name := #[]
  for sourceName in helpers do
    let candidates := mapped.filter (fun n => Lean.privateToUserName? n == some sourceName)
    unless candidates.size == 1 do
      throwError "Original translation helper private CI mapping is not unique"
    roots := roots.push candidates[0]!
  names := names.qsort (fun a b => a.toString < b.toString)
  let mut rows : Array Json := #[]
  for n in names do
    let some ci := env.find? n | throwError "Owned translation CI disappeared"
    let kind := match ci with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "def"
      | _ => "other"
    rows := rows.push <| Json.mkObj [
      ("actualName",toJson n.toString), ("kind",toJson kind),
      ("privateUserName",toJson ((Lean.privateToUserName? n).map Name.toString)),
      ("isProp",toJson (← isProp ci.type)), ("CI",Json.mkObj (← ciRow n true))]
  IO.FS.writeFile output <| (Json.mkObj [
    ("schemaVersion",toJson (1 : Nat)),
    ("probeMainModule",toJson env.mainModule.toString),
    ("solutionModule",toJson moduleName),
    ("sourceHelpers",toJson (helpers.map Name.toString)),
    ("actualPrivateHelpers",toJson (roots.map Name.toString)),
    ("publicPlatformTarget",toJson target.toString),
    ("rawOwnedNames",toJson (names.map Name.toString)),
    ("rawOwnedCIs",Json.arr rows)]).compress
  return roots.push target
end TranslationCountOwnedInventory
'''


def snapshot(side: str) -> bytes:
    old_raw = (snapshot_base.STAGE / snapshot_base.GENERATED_SNAPSHOT).read_text(encoding='utf-8')
    prefix = old_raw.split('namespace LogDivOwnedInventory', 1)[0]
    source = side == 'source'
    imported = SOURCE_MODULES[1] if source else SOLUTION_MODULE
    prefix = prefix.replace('import Solutions.Sol_collision_remainder_limit_ap20\n',
                            'import ' + imported + '\n', 1)
    roots = '#[' + ', '.join('`' + n for n in (HELPERS + [TARGET])) + ']'
    if source:
        init = '  let roots := ' + roots + '\n'
    else:
        prefix += PROBE + '\n'
        init = ('  let roots ← TranslationCountOwnedInventory.exportOwnedInventory #['
                + ', '.join('`' + n for n in HELPERS) + '] `solution '
                + json.dumps(SOLUTION_MODULE) + ' '
                + json.dumps(ws(STAGE / INVENTORY)) + '\n')
    owners = SOURCE_MODULES if source else [SOLUTION_MODULE]
    boundary = ['OAI.PiExponent.translationTermCount',
                'OAI.PiExponent.tendsto_log_div_of_normalized_pow']
    ending = ('run_meta do\n' + init
              + '  PiExponentInterfaceSnapshot.exportSnapshot roots '
              + json.dumps(ws(STAGE / (SOURCE_TYPES if source else GENERATED_TYPES))) + '\n'
              + '  ActualMeanBoundsProofSnapshot.exportBundle '
              + json.dumps(side) + ' '
              + json.dumps(ws(STAGE / (SOURCE_REFS if source else GENERATED_REFS)))
              + ' roots #[' + ', '.join(json.dumps(x) for x in owners) + '] #['
              + ', '.join(json.dumps(x) for x in boundary) + ']\n'
              + '#print axioms ' + (TARGET if source else 'solution') + '\n')
    return (prefix + ending).encode()


def authority() -> tuple[dict[str, bytes], list[dict], dict]:
    route.check_only()
    source_units, _ = route.source_units()
    lookup = json.loads(LOOKUP.read_text(encoding='utf-8'))
    match = [r for r in lookup['records'] if r['theorem_name'] == TARGET]
    need(lookup['environment'] == '0df444a360eaa60ab8c11dca51a86af692955474'
         and lookup['request_methods'] == ['GET'] and len(match) == 1
         and match[0]['lookup_total'] == 0 and match[0]['matches'] == []
         and len(match[0]['pages']) == 1 and match[0]['pages'][0]['http_status'] == 200
         and match[0]['pages'][0]['parsed_body'] == {'theorems': [], 'total': 0},
         'Actual exact-name platform lookup differs')
    out = {
        TARGET_OUTPUT: (ROUTE / 'candidate/Target-comparator.lean.txt').read_bytes(),
        SOLUTION_OUTPUT: (ROUTE / 'candidate/Sol.lean.txt').read_bytes(),
        SOURCE_SNAPSHOT: snapshot('source'),
        GENERATED_SNAPSHOT: snapshot('generated'),
    }
    route_prep = json.loads((ROUTE / 'route-preparation.json').read_text(encoding='utf-8'))
    need(route_prep['source_commit'] == route.COMMIT and
         route_prep['original_source_lines'] == 42 and
         route_prep['target_source_proof_suffix_unchanged'] is True and
         route_prep['source_helpers_private_visibility_prefix_only'] is True and
         route_prep['closed_solution_candidate_not_compiled'] is True,
         'Frozen exact original source route differs')
    for unit, expected in zip(source_units, route_prep['source_units'], strict=True):
        need(sha(unit[0]) == expected['command_sha256'],
             'Original source command changed: ' + expected['name'])
    return out, route_prep['source_units'], lookup


def staged_files() -> dict[str, bytes]:
    outputs, units, lookup = authority()
    pins = [SELF, TASK / 'scripts/certify_log_translation_count_node.py',
            Path(route.__file__), LOOKUP,
            ROUTE / 'route-preparation.json',
            ROUTE / 'candidate/Target-comparator.lean.txt',
            ROUTE / 'candidate/Sol.lean.txt',
            snapshot_base.STAGE / snapshot_base.GENERATED_SNAPSHOT,
            route.PUBLISHED, route.CERT, route.LOGDIV_CERT,
            RUNNER, LEGACY, RUNTIME]
    pins += [TASK / row['source'] for row in units]
    pins += [TASK / row['original'] for row in units]
    pins = list(dict.fromkeys(pins))
    input_hashes = {rel(p): file_sha(p) for p in pins}
    manifest_rows = []
    commands = []
    for index, (name, mode) in enumerate(zip(FILES, MODES, strict=True), 1):
        imports = [line.removeprefix('import ') for line in outputs[name].decode().splitlines()
                   if line.startswith('import ')]
        manifest = {
            'schema_version': 1,
            'artifact_kind': 'ap20-log-translation-count-four-AST-bounded-manifest',
            'output': ws(STAGE / name), 'output_sha256': sha(outputs[name]),
            'imports': imports, 'input_hashes': input_hashes,
            'runtime_sha256': file_sha(RUNTIME), 'mode': mode,
            'emit_olean': mode == 'emit-olean', 'timeout_seconds': 300,
            'bounded_runner': rel(RUNNER), 'bounded_runner_sha256': file_sha(RUNNER),
            'legacy_runner_sha256': file_sha(LEGACY),
            'validated': False, 'submission_ready': False,
        }
        outputs[f'c{index}.json'] = encode(manifest)
        manifest_rows.append({'output': name, 'mode': mode,
                              'manifest': f'c{index}.json', 'imports': imports,
                              'sha256': sha(outputs[name])})
        commands.append('python scripts/preflight_staged_module_windows_bounded.py '
                        + vr(STAGE / name) + ' --root ap20/log-translation-term-count-node-v2'
                        + ' --imports-manifest ap20/log-translation-term-count-node-v2/c'
                        + str(index) + '.json --timeout-seconds 300'
                        + (' --emit-olean' if mode == 'emit-olean' else ''))
    outputs['compile-commands.txt'] = ('\n'.join(commands) + '\n').encode()
    outputs['preparation.json'] = encode({
        'schema_version': 1,
        'artifact_kind': 'ap20-log-translation-count-four-original-AST-proof-preparation',
        'source_commit': route.COMMIT, 'source_name': TARGET,
        'platform_name': TARGET, 'platform_module': MODULE,
        'solution_module': SOLUTION_MODULE,
        'exact_source_units': units, 'original_source_lines': 42,
        'three_helper_proof_suffixes_unchanged': True,
        'target_proof_suffix_unchanged': True,
        'global_solution_name_only_rewritten': True,
        'source_type_only_names': HELPERS + [TARGET],
        'generated_actual_private_names_discovered_by_probe': True,
        'theorem_type_only_values_null': True,
        'generated_raw_owned_inventory': INVENTORY,
        'published_data_definition_name': 'OAI.PiExponent.translationTermCount',
        'published_data_definition_id': '04008248-130e-40ba-b6a3-df3e9b9df91b',
        'accepted_logdiv_theorem_id': '8b1c0341-2978-4a9d-8acc-8a5e3538cbda',
        'actual_exact_name_lookup_sha256': file_sha(LOOKUP),
        'input_hashes': input_hashes,
        'files': manifest_rows, 'compile_commands': commands,
        'proposal_status': 'Draft', 'validated': False,
        'submission_ready': False, 'Lean_started_by_producer': False,
        'API_used': False,
    })
    return outputs


def check_only() -> dict:
    outputs = staged_files()
    for name, raw in outputs.items():
        need((STAGE / name).is_file() and (STAGE / name).read_bytes() == raw,
             'Frozen staged translation proof file changed: ' + name)
    for index, name in enumerate(FILES, 1):
        manifest = json.loads((STAGE / f'c{index}.json').read_text(encoding='utf-8'))
        runner.verify_manifest_inputs(manifest)
        runner.verify_source_certificate(STAGE / name, manifest)
    return {'files': len(outputs), 'contexts': 4,
            'exact_source_AST_units': 4, 'original_source_lines': 42,
            'pure_stage_verified': True, 'Lean_started_by_producer': False,
            'API_used': False}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--prepare', action='store_true')
    group.add_argument('--check-only', action='store_true')
    args = parser.parse_args()
    if args.prepare:
        for name, raw in staged_files().items():
            path = STAGE / name
            if path.exists():
                need(path.read_bytes() == raw, 'Refusing staged translation overwrite: ' + name)
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(raw)
    print(json.dumps(check_only(), ensure_ascii=False))


if __name__ == '__main__':
    main()
