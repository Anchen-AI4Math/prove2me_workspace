"""Freeze actual native AUTHOR results only. Pure hashes/JSON, no Lean or API."""
from pathlib import Path
from datetime import datetime,timezone
import json
import execute_native_author as e

def rows(name):
 return [json.loads(line) for line in (e.OUT/name).read_text(encoding='utf-8-sig').splitlines() if line.startswith('{')]

def main():
 if (e.OUT/'private-proof-repairs.json').exists():
  import resume_author_v3
  resume_author_v3.install_gate()
 state=e.gate();receipt=e.load(e.OUT/'compile-receipt.json');checks=[]
 def require(name,value,details=None):
  assert value,name;checks.append(dict(name=name,passed=True,details=details))
 latest={r['label']:r for r in receipt['rows']};failed=[r for r in receipt['rows'] if r['exit_code']!=0]
 require('29 original and 2 additional final actual calls terminal PASS',len(latest)==31 and all(r['exit_code']==0 for r in latest.values()))
 require('actual failed calls preserved and excluded',all(r['failure_retained'] for r in failed))
 full=rows('control-ParameterSummationFullTypeAudit.log')
 defs=rows('control-ParameterSummationDefinitionAudit.log')
 bounds=rows('control-ParameterSummationBoundaryAudit.log')
 whole=rows('control-ParameterSummationWholeFunctionRflAudit.log')
 serializer=rows('control-IndependentExprDagValidationV3.log')
 names=['ZetaNine.CoefficientMapParameterSummationTransport.'+r['name'] for r in e.headers(e.SOURCE.read_bytes())]
 require('17 complete original forall expected types',len(full)==17 and [r['declaration'] for r in full]==names and
  all(r['kind']=='actual_complete_source_expected_type' and r['type_kernel_equal'] and r['all_fields_Expr_equal_roundtrip'] for r in full))
 require('one complete definition type and value kernel equality',len(defs)==1 and
  defs[0]['kind']=='actual_complete_definition_kernel_value' and defs[0]['type_kernel_equal'] and defs[0]['value_kernel_equal'])
 require('definition actual complete expected names',defs[0]['declaration']=='ZetaNine.CoefficientMapParameterSummationTransport.transferMultiplier' and
  defs[0]['expected']=='ParameterSummationAuthorDefinitionExpected.transferMultiplier')
 require('one actual whole-function rfl proof',len(whole)==1 and whole[0]['kind']=='actual_whole_function_rfl' and
  whole[0]['declaration']=='ParameterSummationAuthorWholeFunction.transferMultiplier_whole_rfl')
 require('nine typed closed boundary proofs',len(bounds)==9 and all(r['kind']=='actual_closed_boundary' for r in bounds))
 fixtures=[r for r in serializer if r['kind']=='expr_dag_validation'];small=[r for r in serializer if r['kind']=='expr_dag_small_source_validation']
 require('20 serializer field fixtures and 3 actual own small SOURCE controls',len(fixtures)==20 and len(small)==3 and
  all(r['all_fields_roundtrip'] and r['raw_repr_reconstruction_equal'] for r in serializer))
 axioms=[]
 for row in full+defs+bounds+whole+small:
  for key in ['axioms','source_axioms','expected_axioms']:
   if key in row:
    require('Std3 '+row.get('declaration',row.get('source_name',''))+' '+key,set(row[key])<={'propext','Classical.choice','Quot.sound'})
    axioms.append(dict(declaration=row.get('declaration',row.get('source_name')),field=key,axioms=row[key]))
 require('49 actual Std3 lists',len(axioms)==49)
 own=e.load(e.OUT/'actual-own-object-resolution.json');extra=e.load(e.OUT/'additional-actual-own-object-resolution.json')
 require('27 original actual own object resolutions',len(own)==27 and all(r['own_object_resolution_passed'] for r in own))
 require('all 28 own objects including full-function rfl',len(extra)==28 and all(r['own_object_resolution_passed'] for r in extra))
 private=e.PROJECT/(e.NATIVE.replace('.','/')+'.lean')
 require('all 17 complete original headers preserved',e.headers(private.read_bytes())==e.headers(e.SOURCE.read_bytes()))
 require('entire original transferMultiplier definition preserved',e.definition(private.read_bytes())==e.definition(e.SOURCE.read_bytes()))
 require('original bf215 candidate unchanged',e.sha(e.SOURCE)==e.SOURCE_SHA)
 require('actual Outputs8b2 native SOURCE',e.sha(e.PROJECT/'missions/zeta9/formalization/CoefficientMapFormalTransportOutputs.lean')=='8b2fc477c10a698f9b5bef004531861c392d93da0377a2874965c8ce470d2fa6')
 require('actual Jets ccef native SOURCE',e.sha(e.PROJECT/'missions/zeta9/formalization/CoefficientMapFormalTransportJets.lean')=='ccef5eaf7bad1b86ce8da45401b2ed3d5bb28e55aafc2626a92d4fc2a4cf4c02')
 export=e.OUT/'ParameterSummationVerifiedSource.lean'
 if export.exists():require('immutable existing verified SOURCE export',export.read_bytes()==private.read_bytes())
 else:e.write(export,private.read_bytes())
 paths=set()
 def add(record):
  path=e.TASK/record['task_relative']
  require('rehash '+record['task_relative'],path.stat().st_size==record['bytes'] and e.sha(path)==record['sha256'])
  paths.add(path)
 # Mutable private repairs are separately admitted by gate(); immutable SOURCE snapshots stay sealed.
 for record in e.load(e.PREP/'preparation-bindings.json')['files']:
  path=e.TASK/record['task_relative']
  if path.is_file() and e.sha(path)==record['sha256']:add(record)
  else:require('changed private SOURCE binding admitted by actual failed repair',str(path).startswith(str(e.PROJECT)) and bool(failed))
 for r in state['sources']:
  add(r['immutable_snapshot']);paths.add(e.PROJECT/r['project_relative'])
  origin=Path(r['origin_absolute'])
  require('actual origin rehash '+r['module'],origin.stat().st_size==r['bytes'] and e.sha(origin)==r['sha256'])
  if origin.is_relative_to(e.TASK):paths.add(origin)
 for r in state['controls']:add(r['immutable_source']);paths.add(e.PROJECT/r['project_relative'])
 for row in receipt['rows']:
  require('actual threads/command '+row['label'],row['command'][:6]==[str(e.LAKE),'env',str(e.PY312),str(e.LEAF),str(e.LEAN),'-j1'] and row['cwd']==str(e.PROJECT))
  for key in ['stdout','stderr','log','exit_file','selected_paths']:add(row[key])
  for key in ['retained_input_bindings','retained_output_bindings']:
   require('retained actual '+key+' '+row['label']+' '+str(row['attempt']),key in row)
   for record in row[key]:add(record['snapshot_binding'])
  for key in ['LEAN_PATH','LEAN_SRC_PATH']:
   selected=e.load(e.TASK/row['selected_paths']['task_relative'])[key]['filtered']
   require('only own/fixed-package paths '+row['label']+' '+key,all(Path(raw).resolve().is_relative_to(e.PROJECT.resolve()) or
    Path(raw).resolve().is_relative_to((e.ROOT/'.lake/packages').resolve()) for raw in selected))
 for row in latest.values():
  for record in row['input_bindings']+row['output_bindings']:add(record)
 for path in e.OUT.rglob('*'):
  if path.is_file() and '__pycache__' not in path.parts and path.name not in {'author-audit.json','AUTHOR_SHA256SUMS.txt'}:paths.add(path)
 for path in e.PROJECT.glob('b/lib/lean/**/*.olean*'):paths.add(path)
 stable=[e.binding(path) for path in sorted(paths)]
 require('all final stable bindings rehashed',all((e.TASK/r['task_relative']).stat().st_size==r['bytes'] and e.sha(e.TASK/r['task_relative'])==r['sha256'] for r in stable))
 success=sum(r['exit_code']==0 for r in receipt['rows'])
 counts=dict(actual_attempts=len(receipt['rows']),actual_successful_calls=success,actual_failed_Lean_calls=len(failed),
  actual_successful_Lean_calls=success-1,actual_runtime_calls=1,original_planned_calls=29,original_final_success_calls=29,
  additional_whole_function_rfl_and_resolver_final_success_calls=2,additional_resolver_failed_attempts_retained=1,fresh_native_sources=22,complete_expected_theorems=17,
  actual_complete_type_kernel_comparisons=17,whole_definitions=1,actual_definition_type_kernel_comparisons=1,
  actual_definition_value_kernel_comparisons=1,actual_whole_function_rfl=1,typed_closed_boundaries=9,
  full_source_expected_boundary_small_and_rfl_Expr_reconstructions=98,serializer_field_fixtures=20,serializer_small_sources=3,
  Std3_reports=49,actual_own_object_resolutions=28,stable_files=len(stable),checks=len(checks))
 audit=dict(verdict='PASS',role='parameter summation native AUTHOR; independent review required',
  frozen_at_utc=datetime.now(timezone.utc).isoformat(),checks=checks,counts=counts,
  original_candidate=e.binding(e.SOURCE),compiled_private_source=e.binding(private),verified_export=e.binding(export),
  original_complete_headers=e.headers(e.SOURCE.read_bytes()),original_definition_immutable=True,original_preparation_and_snapshots_immutable=True,
  actual_complete_expected_type_records=full,actual_complete_definition_records=defs,actual_whole_function_rfl_records=whole,
  actual_boundary_records=bounds,actual_Std3_records=axioms,actual_own_object_resolution_records=extra,
  actual_receipt=receipt,stable_files=stable,retained_failed_calls_excluded=failed,executor_provenance=e.load(e.OUT/'executor-provenance.json'),
  private_repairs=e.load(e.OUT/'private-proof-repairs.json') if (e.OUT/'private-proof-repairs.json').exists() else None,
  author_expected_and_serializer_SOURCE_reuse_disclosed=True,foreign_cache_objects_borrowed=False,
  continuation_recovery=e.load(e.OUT/'recovery-provenance-2026-10-07.json'),
  continuation_reuse_of_same_author_SOURCE_objects_disclosed=True,
  source_rebuilds_by_this_recovery=0,additional_resolver_actual_calls_by_this_recovery=1,
  own_fresh_native_SOURCE_rebuild=True,API_Root_module_scope_or_mission_operations=False,
  current_platform_target='19653cff-d481-498a-a717-10630d1ca1b7',
  all_n_ge_one_quartic_formal_five_output_and_exactL_value_transport_proved=True,
  even_n_ge_two_actual_HasSum_absolute_and_tsum_parameter_transport_proved=True,
  genuine_inverse_coefficient_row_and_same_selected_output_transport_proved=True,
  termwise_series_equality_claimed=False,integer_polynomial_or_height_J_or_zeta9_irrationality_proved=False,
  independent_review_claimed=False,platform_acceptance_claimed=False)
 e.dump(e.OUT/'author-audit.json',audit)
 entries=stable+[e.binding(e.OUT/'author-audit.json')]
 e.write(e.OUT/'AUTHOR_SHA256SUMS.txt',''.join(r['sha256']+'  '+r['task_relative']+'\n' for r in entries))
 print(json.dumps(dict(verdict='PASS',counts=counts,author_audit_sha256=e.sha(e.OUT/'author-audit.json'),
  verified_export_sha256=e.sha(export),independent_review_still_required=True)))

if __name__=='__main__':main()
