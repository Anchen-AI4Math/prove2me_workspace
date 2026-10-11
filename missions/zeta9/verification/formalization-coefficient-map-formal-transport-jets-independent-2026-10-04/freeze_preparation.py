"""Freeze pure preparation; only source reads/writes and Python parsing."""
from pathlib import Path
import ast, json, re, sys
import prepare_sources as p

OUT, TASK, ROOT, PROJECT = p.OUT, p.TASK, p.ROOT, p.PROJECT
CONTROL_MODULES = ['JetsIndependentTypes', 'JetsIndependentBoundaries',
                   'JetsIndependentSerializerControls', 'AuthorBoundaryReplay']

def main():
    sys.stdout.reconfigure(encoding='utf-8')
    assert not (OUT/'preparation-freeze.json').exists()
    state=p.load(OUT/'source-preparation.json')
    assert state['Lean_Lake_compiler_invocations']==0
    assert not (PROJECT/'b').exists() and not (PROJECT/'.lake').exists()
    assert not list(PROJECT.rglob('*.olean'))
    assert p.sha(p.AUTHOR/'author-audit.json')==p.AUTHOR_SHA
    bindings=p.load(OUT/'author-binding-review.json')
    assert bindings['verified_count']==439 and bindings['mismatch_count']==0
    assert bindings['actual_final_export']['sha256']==p.SOURCE_SHA
    for module in CONTROL_MODULES:
        source=OUT/(module+'.lean')
        p.write(PROJECT/(module+'.lean'),source.read_bytes())
    ownnames=re.findall(r'^theorem\s+(\w+)',(OUT/'JetsIndependentTypes.lean').read_text(encoding='utf-8-sig'),re.M)
    boundarynames=re.findall(r'^theorem\s+(\w+)',(OUT/'JetsIndependentBoundaries.lean').read_text(encoding='utf-8-sig'),re.M)
    actualnames=re.findall(r'^theorem\s+(\w+)',(PROJECT/'missions/zeta9/formalization/CoefficientMapFormalTransportJets.lean').read_text(encoding='utf-8-sig'),re.M)
    assert len(ownnames)==len(actualnames)==26 and ownnames==actualnames
    assert len(boundarynames)==31
    # Static statement inventory is for scheduling/review, not parser execution.
    p.dump(OUT/'prepared-declaration-inventory.json',dict(
        kind='static_source_and_expected_inventory_only',actual_source=p.SOURCE_SHA,
        actual_theorem_names=actualnames,own_full_expected_names=ownnames,
        own_boundary_names=boundarynames,Lean_parser_executed=False,
        expected_type_proofs_planned=26,actual_source_proofs_planned=26,
        own_boundary_proofs_planned=31,author_boundary_replay_proofs_planned=15))
    modules=[r['module'] for r in state['source']]+['IndependentExprDagV3',
        'IndependentExprDagValidationV3']+CONTROL_MODULES
    assert len(modules)==25 and len(set(modules))==25
    resolver='''import missions.zeta9.formalization.CoefficientMapFormalTransportJets
import JetsIndependentTypes
import JetsIndependentBoundaries
import JetsIndependentSerializerControls
import AuthorBoundaryReplay
import Lean
open Lean
set_option autoImplicit false
set_option maxHeartbeats 0
run_meta do
  let requested : List (Name × String) := [
'''
    resolver+=',\n'.join('    (`'+module+', '+json.dumps(str((PROJECT/'b/lib/lean'/(module.replace('.','/')+'.olean')).resolve()))+')' for module in modules)
    resolver+='''
  ]
  let env ← getEnv
  for (module, wanted) in requested do
    let actual ← IO.FS.realPath (← findOLean module)
    let expected ← IO.FS.realPath (System.FilePath.mk wanted)
    unless actual == expected do throwError "Borrowed proof object: {module}: {actual}"
    -- The duplicate fixture serializer is intentionally compiled separately.
    let mustBeInHeader := module != `IndependentExprDagValidationV3
    let inHeader := env.header.moduleNames.contains module
    unless !mustBeInHeader || inHeader do throwError "Actual imported header missing {module}"
    IO.println (Json.mkObj [("kind",Json.str "actual_own_findOLean"),
      ("module",Json.str module.toString),("olean",Json.str actual.toString),
      ("expected",Json.str expected.toString),("exact_own_cache",toJson true),
      ("actual_header_contains",toJson inHeader),
      ("separate_fixture_environment",toJson (!mustBeInHeader))]).compress
  IO.println (Json.mkObj [("kind",Json.str "actual_environment_module_header"),
    ("modules",toJson (env.header.moduleNames.toList.map Name.toString))]).compress
'''
    p.write(OUT/'JetsActualResolver.lean',resolver)
    p.write(PROJECT/'JetsActualResolver.lean',resolver)
    for script in OUT.glob('*.py'):
        ast.parse(script.read_text(encoding='utf-8-sig'),filename=str(script))
    assert (PROJECT/'lean-toolchain').read_bytes()==(ROOT/'lean-toolchain').read_bytes()
    assert (PROJECT/'lake-manifest.json').read_bytes()==(ROOT/'lake-manifest.json').read_bytes()
    files=sorted({q.resolve() for folder in [OUT,PROJECT] for q in folder.rglob('*')
                  if q.is_file() and '__pycache__' not in q.parts})
    stable=[p.binding(q) for q in files]
    assert all(len(str(TASK/r['task_relative']))<=259 for r in stable)
    grant_fields=dict(explicit_parent_Lean_lane_granted=True,lane=2,maximum_global_Lean_lanes=2,
        preparation_sha256='SHA256_OF_THIS_PREPARATION_FREEZE',author_sha256=p.AUTHOR_SHA,
        source_sha256=p.SOURCE_SHA,project_task_relative='.rt/tj1',
        parent_message_verbatim='PARENT_EXPLICIT_AUTHORIZATION_TEXT',
        only_this_serial_lane=True,Root_API_credentials_scope_modified=False)
    p.dump(OUT/'preparation-freeze.json',dict(status='PURE_INDEPENDENT_PREPARATION_ONLY',
        verdict=None,Lean_Lake_compiler_invocations=0,source_sha256=p.SOURCE_SHA,
        author_sha256=p.AUTHOR_SHA,author_439_bindings_actual_verified=True,
        independent_native_PASS_claimed=False,role_disclosure=bindings['role_disclosure'],
        project_task_relative='.rt/tj1',initial_absent_project=True,initial_cache_absent=True,
        native_source_builds_planned=19,serializer_source_builds_planned=2,
        actual_source_types_and_proofs_planned=26,independent_expected_types_planned=26,
        full_type_kernel_Meta_comparisons_planned=26,source_expected_DAG_reconstructions_planned=104,
        own_boundary_proofs_planned=31,author_boundary_replay_proofs_planned=15,
        actual_findOLean_objects_planned=25,serializer_fixture_replays_planned=20,
        serializer_small_source_replays_planned=3,own_serializer_controls_planned=6,
        cache_objects_borrowed=False,Root_or_author_proof_fallback_permitted=False,
        failed_historical_source_excluded=bindings['excluded_shared_historical_candidate'],
        source_records=state['source'],serializer_records=state['serializer_source_only'],
        planned_control_modules=CONTROL_MODULES,planned_resolver_modules=modules,
        path_checks=state['path_checks'],stable_files=stable,
        future_grant_file=(OUT/'lane-grant.json').relative_to(TASK).as_posix(),
        exact_required_grant_fields=grant_fields,
        startup_command='C:\\Users\\anche\\AppData\\Local\\Programs\\Python\\Python312\\python.exe -X utf8 '+
          str((OUT/'run.py').relative_to(TASK)).replace('\\','/')+' --parent-lane-authorized',
        mathematical_scope=dict(n_minimum=1,rows=5,all_poles=True,jet_orders='1..9',
          no_parity_assumption=True,constant_term_transport_proved=False,
          five_output_matrix_transport_proved=False,HasSum_parameter_transport_proved=False)))
    frozen=p.load(OUT/'preparation-freeze.json')
    for row in frozen['stable_files']:
        assert p.binding(TASK/row['task_relative'])==row
    p.dump(OUT/'preparation-postfreeze-verification.json',dict(
        preparation_file=p.binding(OUT/'preparation-freeze.json'),
        stable_files_actual_rehashed=len(stable),mismatches=0,
        cache_still_absent=not (PROJECT/'b').exists(),Lean_Lake_compiler_invocations=0))
    p.write(OUT/'pure-final-preparation-exit.txt','0\n')
    print(json.dumps(dict(preparation=p.binding(OUT/'preparation-freeze.json'),
        stable_files=len(stable),source=19,expected=26,boundaries=31,Lean_invocations=0),indent=2))

if __name__=='__main__':main()
