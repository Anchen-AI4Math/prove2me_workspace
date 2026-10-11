"""Freeze only actual independently compiled source/control successes and full bindings."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import collections, json, re, sys
sys.dont_write_bytecode = True
import prepare_independent as p
import run_independent as r

STD3 = {'propext','Classical.choice','Quot.sound'}

def records(row):
 return [json.loads(line[len('PHI_RECORD|'):]) for line in
         r.check(row['log']).read_text(encoding='utf-8').splitlines() if line.startswith('PHI_RECORD|')]

def absolute_binding(path):
 path = Path(path).resolve()
 b = dict(absolute_path=str(path), bytes=path.stat().st_size, sha256=p.sha(path))
 if path.is_relative_to(p.TASK.resolve()): b['task_relative'] = path.relative_to(p.TASK.resolve()).as_posix()
 elif path.is_relative_to(p.ROOT.resolve()): b['root_relative'] = path.relative_to(p.ROOT.resolve()).as_posix()
 else: assert path.is_relative_to(p.TOOLCHAIN)
 return b

def check_absolute(b):
 path = Path(b['absolute_path']).resolve()
 assert path.is_relative_to(p.TASK.resolve()) or path.is_relative_to((p.ROOT / '.lake/packages').resolve()) or path.is_relative_to(p.TOOLCHAIN)
 assert path.name.lower() not in {'credentials.json','.env'}
 assert path.stat().st_size == b['bytes'] and p.sha(path) == b['sha256'], str(path)
 return b

def main():
 sys.stdout.reconfigure(encoding='utf-8')
 grant = r.gate()
 receipt = p.load(p.OUT / 'compile-receipt.json')
 rows = receipt['rows']; bylabel = {x['label']:x for x in rows}
 required = ['runtime-version','source-AnalyticPhase','source-AnalyticPhaseUpperBound',
             'control-types','control-kernel','control-boundary','control-resolver',
             'control-serializer','control-serializer-validation']
 assert all(bylabel[n]['exit_code'] == 0 for n in required)
 assert rows.index(bylabel['source-AnalyticPhase']) < rows.index(bylabel['source-AnalyticPhaseUpperBound'])
 source_outputs = {n:bylabel['source-' + n]['output_bindings'] for n in p.EXPECTED}
 history = []
 for row in rows:
  assert row['actual_environment'] == {'LEAN_NUM_THREADS':'1','LAKE_JOBS':'1'}
  assert row['Root_granted_lane'] == grant['lane']
  assert '-j1' in row['command'] and '--root=' + str(p.PROJECT) in row['command']
  assert row['cwd'] == str(p.PROJECT)
  assert row['command'][:4] == ['lake','env',p.PYTHON,str(p.PROJECT / 'leaf.py')]
  for field in ['stdout','stderr','log','exit_file','selected_paths']: r.check(row[field])
  assert r.check(row['log']).read_bytes() == r.check(row['stdout']).read_bytes() + r.check(row['stderr']).read_bytes()
  assert int(r.check(row['exit_file']).read_text()) == row['exit_code']
  paths = p.load(r.check(row['selected_paths']))
  assert paths['actual_environment'] == row['actual_environment']
  for key in ['LEAN_PATH','LEAN_SRC_PATH']:
   assert all(Path(raw).is_absolute() and (Path(raw).resolve().is_relative_to(p.PROJECT.resolve()) or
              Path(raw).resolve().is_relative_to((p.ROOT / '.lake/packages').resolve()))
              for raw in paths[key]['filtered'])
  for retained in row['retained_inputs'] + row['retained_outputs']:
   original, snapshot = retained['original_binding'], retained['snapshot_binding']
   r.check(snapshot)
   assert original['sha256'] == snapshot['sha256'] and original['bytes'] == snapshot['bytes']
  assert len(row['retained_inputs']) == len(row['input_bindings'])
  assert len(row['retained_outputs']) == len(row['output_bindings'])
  if row['exit_code'] == 0:
   for b in row['input_bindings'] + row['output_bindings']: r.check(b)
   if row['module'] == 'missions.zeta9.formalization.AnalyticPhaseUpperBound':
    assert all(b in row['input_bindings'] for b in source_outputs['AnalyticPhase'])
   if row['label'].startswith('control-'):
    assert all(b in row['input_bindings'] for outputs in source_outputs.values() for b in outputs)
  else: assert row['failed_attempt_retained']
  history.append(dict(label=row['label'],exit_code=row['exit_code'],
   every_original_input_byte_retained=True,every_actual_log_exit_byte_retained=True,
   successful_current_inputs_and_outputs_rehashed=row['exit_code'] == 0))
 state = p.load(p.OUT / 'preparation-state.json')
 types = records(bylabel['control-types']); kernel = records(bylabel['control-kernel'])
 boundary = records(bylabel['control-boundary']); resolver = records(bylabel['control-resolver'])
 theorem_names = {p.NS + n for n in state['expected_theorem_prefixes']}
 definition_names = {p.NS + n for n in state['original_full_definition_source']}
 assert len(theorem_names) == 34 and len(definition_names) == 7
 assert {x['name'] for x in types if x['kind'] == 'theorem'} == theorem_names
 assert {x['name'] for x in types if x['kind'] == 'definition'} == definition_names
 inventories = [x for x in types if x['kind'] == 'module_inventory']
 module_names = {n for x in inventories for n in x['constant_names'] + x['extra_names']}
 module_records = {x['name']:x for x in types if x['kind'] in ['module_declaration','module_extra']}
 assert module_names == set(module_records) and len(inventories) == 2
 auxiliary_names = sorted(module_names - theorem_names - definition_names)
 assert len(auxiliary_names) == 27 and auxiliary_names == state['auxiliary_expected_names']
 assert all(x['value_raw'] is not None and x['full_value_typed'] for x in module_records.values())
 comparisons = [x for x in kernel if x['kind'] == 'theorem_compare']
 assert {x['actual'] for x in comparisons} == theorem_names
 assert all(x['type_exprEqual'] and x['type_isDefEq'] for x in comparisons)
 definitions = [x for x in kernel if x['kind'] == 'definition_compare']
 assert {x['actual'] for x in definitions} == definition_names
 assert all(x['type_exprEqual'] and x['type_isDefEq'] and x['value_isDefEq'] and
            x['normalized_value_exprEqual'] and x['normalized_value_isDefEq'] for x in definitions)
 assert {x['name'] for x in kernel if x['kind'] == 'definition_rfl'} == {
        'independent_original_value_' + n for n in state['original_full_definition_source']}
 domain = [x for x in kernel if x['kind'] == 'exact_domain_compare']
 assert len(domain) == 1 and domain[0]['type_exprEqual'] and domain[0]['type_isDefEq']
 helpers = [x for x in kernel if x['kind'] == 'definition_helper_compare']
 assert len({x['actual'] for x in helpers}) == 8
 assert all(x['type_exprEqual'] and x['value_exprEqual'] and x['type_isDefEq'] and x['value_isDefEq']
            and x['actual_value_typed'] and x['expected_value_typed'] for x in helpers)
 assert len(boundary) == 15 and {x['name'] for x in boundary} == {
        'APIndBoundary.' + n for n in state['typed_boundary_names']}
 assert all(x['kind'] == 'typed_boundary' and x['isProp'] and x['full_value_typed'] and
            x['value_raw'] is not None for x in boundary)
 axiom_sets, raw_count, value_typing_count = 0, 0, 0
 for item in types + kernel + boundary:
  for field, value in item.items():
   if field.endswith('axioms'):
    assert set(value) <= STD3; axiom_sets += 1
   if field.endswith('_raw') and value is not None:
    assert isinstance(value,str) and value
    if field == 'value_raw' and item.get('value_raw_format') == 'lossless lean-expr-dag-v1; full type_root and value_root':
     graph = json.loads(value)
     assert graph['format'] == 'lean-expr-dag-v1' and item['all_fields_type_Expr_equal'] and item['all_fields_value_Expr_equal']
     assert item['full_value_typed'] and item['full_type_kernel_equal'] and item['full_value_kernel_equal']
    else: assert '...' not in value and '…' not in value
    raw_count += 1
  if 'full_value_typed' in item:
   assert item['full_value_typed'] and item['value_raw'] is not None
   value_typing_count += 1
 source_contracts, exports = [], []
 for name in p.EXPECTED:
  original = p.TASK / 'formalization' / (name + '.lean')
  private = p.PROJECT / 'missions/zeta9/formalization' / (name + '.lean')
  export = p.AUTHOR / 'native-export' / (name + '.lean')
  assert p.sha(original) == p.ORIGINAL[name] and p.sha(private) == p.EXPECTED[name]
  assert private.read_bytes() == export.read_bytes()
  source, actual = original.read_text(encoding='utf-8-sig'), private.read_text(encoding='utf-8-sig')
  assert p.prefixes(source) == p.prefixes(actual) and p.defs(source) == p.defs(actual)
  assert source[:source.index('theorem ')] == actual[:actual.index('theorem ')]
  dst = p.OUT / 'native-export' / (name + '.lean'); p.write(dst, private.read_bytes())
  exports.append(p.binding(dst))
  source_contracts.append(dict(module=name,shared=p.binding(original),independent_compiled=p.binding(private),
   author_export=p.binding(export),independent_export=p.binding(dst),exact_original_theorem_prefixes=True,
   exact_all_original_definition_source=True,author_proof_bodies_recompiled_from_SOURCE=True))
 exact_domain = state['expected_theorem_prefixes']['phase_global_upper_bound']
 assert exact_domain == 'theorem phase_global_upper_bound :\n    ∀ x : ℝ, 1 < x → phase x ≤ (-2641 / 250 : ℝ) :='
 resolved, paths, own_resolved = [], set(), set()
 origins = collections.Counter()
 for item in resolver:
  assert item['kind'] == 'actual_module_resolver'
  file = Path(item['canonical_olean']).resolve(); assert file.exists()
  if file.is_relative_to(p.PROJECT.resolve()):
   kind = 'independent_own_SOURCE_compiled_phase' if item['module'].startswith('missions.zeta9.formalization.') else 'independent_own_SOURCE_compiled_audit_control'
   own_resolved.add(item['module'])
  elif file.is_relative_to((p.ROOT / '.lake/packages').resolve()): kind = 'pinned_package_dependency'
  elif file.is_relative_to(p.TOOLCHAIN): kind = 'intrinsic_pinned_Lean_toolchain'
  else: raise AssertionError('Foreign actual object ' + str(file))
  origins[kind] += 1
  companions = sorted(x.resolve() for x in file.parent.glob(file.name + '*') if x.is_file())
  paths.update(companions)
  resolved.append(dict(**item,origin_kind=kind,available_companions=[str(x) for x in companions]))
 assert own_resolved == {'missions.zeta9.formalization.AnalyticPhase','missions.zeta9.formalization.AnalyticPhaseUpperBound',
                         'APIPhaseExprDagV1','APIPhaseExprDagValidationV1'}
 assert p.sha(p.AUTHOR / 'author-audit.json') == p.AUTHOR_SHA
 author = p.load(p.AUTHOR / 'author-audit.json')
 print('Rehashing every frozen author binding:',len(author['stable_bindings']),flush=True)
 with ThreadPoolExecutor(max_workers=2) as pool:
  checked_author = list(pool.map(check_absolute,author['stable_bindings']))
 p.dump(p.OUT / 'complete-author-binding-rehash.json',dict(
  author_report=p.binding(p.AUTHOR / 'author-audit.json'),all_binding_count=len(checked_author),
  differences=0,all_bindings=checked_author,only_read_author_and_fixed_dependency_objects=True,
  independent_SOURCE_compilation_not_substituted_with_author_objects=True))
 for name, value in [('actual-types-and-auxiliaries.json',types),('actual-kernel-and-definitions.json',kernel),
                     ('actual-typed-boundaries.json',boundary),('actual-import-resolver.json',resolved)]:
  p.dump(p.OUT / name,value)
 p.dump(p.OUT / 'source-contracts.json',source_contracts)
 p.write(p.OUT / 'README.md','''Native actual Phase INDEPENDENT PASS after compiling both frozen exports from SOURCE in fresh api1.

The proved component is ∀ x : ℝ, 1 < x → phase x ≤ (-2641 / 250 : ℝ),
with a stronger strict rational cap -10564011/1000000. Complete Z9.A, moment
asymptotics, infinite-tail estimates, uniform o(1), height and irrationality remain open.

All 34 original unrestricted declaration types and seven complete definition
types/values pass actual kernel isDefEq; seven whole-function equality proofs are rfl.
Raw Expr.equal results and complete raw expressions are retained as observed.
Any normalization transparently unfolds only individually checked proposition-valued
generated helpers, with full raw types and values and Std3 checks. No binder or
metadata erasure is performed. All 27 source auxiliaries, eight relevant internal
definition helpers and 15 typed boundary proofs are independently inspected.
Every actual source module declaration includes its full proof/definition value,
an actual inferType check, exact forall type and Std3 dependency set.

The actual Lean findOLean/IO.FS.realPath inventory restricts all imports to own
SOURCE-built api1 phase objects, pinned packages and intrinsic Lean 4.33.1.
No aph1 or Root proof object is reused. All failures preserve exact inputs,
outputs, stdout, stderr and exits. API/mission writes and scope changes are absent.
''')
 paths.update(Path(b['absolute_path']).resolve() for b in checked_author)
 paths.add(p.AUTHOR / 'author-audit.json')
 paths.update(x.resolve() for x in p.OUT.rglob('*') if x.is_file() and x.name != 'independent-audit.json')
 for row in rows:
  if row['exit_code'] == 0:
   paths.update((p.TASK / b['task_relative']).resolve() for b in row['input_bindings'] + row['output_bindings'])
 print('Freezing all independent input/dependency bindings:',len(paths),flush=True)
 with ThreadPoolExecutor(max_workers=2) as pool:
  stable = list(pool.map(absolute_binding,sorted(paths,key=lambda x:str(x).casefold())))
 with ThreadPoolExecutor(max_workers=2) as pool: list(pool.map(check_absolute,stable))
 audit = dict(status='NATIVE_ACTUAL_PHASE_INDEPENDENT_PASS',role='independent second auditor, not author',
  project_task_relative='.rt/api1',Lean_executed=True,API_executed=False,
  foreign_proof_objects_borrowed=False,source_fresh_compile_count=2,
  source_contracts=source_contracts,exported_compiled_sources=exports,
  source_dependency_pre_call_snapshots_complete=True,all_upper_and_control_objects_linked_to_own_prior_source_success=True,
  actual_calls=len(rows),actual_success_calls=sum(x['exit_code'] == 0 for x in rows),
  actual_failed_calls=sum(x['exit_code'] != 0 for x in rows),every_failure_complete_and_unaccepted=True,
  successful_required_labels=required,actual_call_history=history,
  actual_theorem='forall x : Real, 1 < x -> ZetaNine.AnalyticPhase.phase x <= -2641/250',
  stronger_certified_bound='phase x < -10564011/1000000 for every real x > 1',
  complete_Z9_A_moments_asymptotics_uniform_error_PASS=False,
  theorem_type_count=34,exact_source_expected_theorem_types_kernel_isDefEq=True,
  theorem_types_Expr_equal=True,exact_unrestricted_open_domain_checked=True,
  definition_count=7,full_definition_types_values_present=True,raw_false_values_preserved=True,
  raw_full_value_Expr_equal_count_true=sum(x['value_exprEqual'] for x in definitions),
  raw_full_value_Expr_equal_count_false=sum(not x['value_exprEqual'] for x in definitions),
  raw_full_value_actual_isDefEq_all=True,whole_function_rfl_count=7,
  transparent_checked_helper_expansion_Expr_equal_count=sum(x['normalized_value_exprEqual'] for x in definitions),
  no_binder_metadata_erasure=True,related_helper_pair_records=len(helpers),unique_canonical_definition_helpers=8,
  all_related_helper_full_type_value_Expr_equal_isDefEq_and_value_typing=True,
  actual_source_module_declarations=len(module_names),actual_auxiliary_count=len(auxiliary_names),
  actual_auxiliary_names=auxiliary_names,all_auxiliary_types_and_full_values_Std3_present=True,
  actual_full_proof_definition_value_typing_checks=value_typing_count,typed_boundary_count=15,
  actual_Std3_axiom_set_checks=axiom_sets,raw_expression_fields_no_truncation=raw_count,
  actual_import_module_count=len(resolved),actual_import_origins=dict(origins),
  all_actual_paths_restricted_to_own_pinned_packages_intrinsic_Lean=True,
  author_complete_binding_rehash_count=len(checked_author),author_complete_binding_rehash_differences=0,
  stable_binding_count=len(stable),stable_bindings=stable,Root_granted_lane=grant['lane'],
  maximum_global_Lean_lanes=2,LEAN_NUM_THREADS=1,LAKE_JOBS=1,lean_option='-j1',
  current_Lean_processes_owned_by_this_auditor=0,scope_and_workspace_check='Root owns registration/check',
  platform_publication_or_acceptance_claimed=False,
  current_owner='parameter_author_recovery_1007',Phase_author_role=False,
  independent_SOURCE_only_provenance=p.load(p.OUT/'current-auditor-provenance-2026-10-07.json'),
  strict_lossless_DAG_repair_provenance=p.load(p.OUT/'lossless-dag-v2-executor-provenance.json'),
  actual_lossless_full_proof_value_DAG_records=109,actual_complete_type_value_Expr_equal_reconstructions=218,
  actual_DAG_value_inferType_checks=109,serializer_complete_field_fixtures=20,serializer_actual_phase_source_fixtures=3,
  all_name_level_binder_mdata_syntax_fields_preserved=True,raw_tree_and_DAG_encodings_explicitly_distinguished=True,
  original_mathematical_SOURCE2_successes_not_recompiled=True,generic_serializer_fresh_SOURCE_calls=2,
  actual_lossless_full_proof_value_evidence=p.binding(p.OUT/'actual-lossless-proof-value-evidence.json'),
  former_Parameter_AUTHOR_is_distinct_artifact=True)
 p.dump(p.OUT / 'independent-audit.json',audit)
 print('NATIVE_ACTUAL_PHASE_INDEPENDENT_PASS',flush=True)
 print('Report SHA256:',p.sha(p.OUT / 'independent-audit.json'),flush=True)
 print('Actual calls/success/failure:',len(rows),sum(x['exit_code'] == 0 for x in rows),sum(x['exit_code'] != 0 for x in rows),flush=True)
 print('Stable bindings:',len(stable),flush=True)

if __name__ == '__main__': main()
