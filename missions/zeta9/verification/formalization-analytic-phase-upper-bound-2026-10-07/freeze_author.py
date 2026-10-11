"""Pure final author audit of actual source executions, full controls and canonical dependencies."""
from pathlib import Path
import collections,re,sys
sys.dont_write_bytecode=True
import prepare_native as p
from repair_base_v2 import prefixes

TOOLCHAIN=Path('C:/Users/anche/.elan/toolchains/leanprover--lean4---v4.33.1').resolve()
STD3={'propext','Classical.choice','Quot.sound'}

def check_binding(b):
    path=p.TASK/b['task_relative']
    assert path.exists() and path.stat().st_size==b['bytes'] and p.sha(path)==b['sha256'],str(path)

def records(row):
    return [__import__('json').loads(line[len('AP_RECORD|'):]) for line in
      (p.TASK/row['log']['task_relative']).read_text(encoding='utf-8').splitlines() if line.startswith('AP_RECORD|')]

def main():
    import run_native_v3 as r
    r.gate()
    receipt=p.load(p.OUT/'compile-receipt.json');rows=receipt['rows']
    bylabel={x['label']:x for x in rows}
    required=['runtime-version','native-base-v5','native-upper-v2','control-types-v2',
              'control-kernel-v4','control-boundary-v2','control-resolver-v1']
    assert all(bylabel[n]['exit_code']==0 for n in required)
    history=[]
    for row in rows:
        assert row['actual_environment']=={'LEAN_NUM_THREADS':'1','LAKE_JOBS':'1'}
        assert '-j1' in row['command'] and '--root='+str(p.PROJECT) in row['command']
        assert row['cwd']==str(p.PROJECT)
        assert row['command'][:4]==['lake','env',p.PYTHON,str(p.PROJECT/'leaf.py')]
        for field in ['stdout','stderr','log','exit_file','selected_paths']:check_binding(row[field])
        assert (p.TASK/row['log']['task_relative']).read_bytes()==(
          p.TASK/row['stdout']['task_relative']).read_bytes()+(p.TASK/row['stderr']['task_relative']).read_bytes()
        assert int((p.TASK/row['exit_file']['task_relative']).read_text())==row['exit_code']
        paths=p.load(p.TASK/row['selected_paths']['task_relative'])
        assert paths['actual_environment']==row['actual_environment']
        for key in ['LEAN_PATH','LEAN_SRC_PATH']:
            assert all(Path(v).is_absolute() and (Path(v).resolve().is_relative_to(p.PROJECT.resolve()) or
              Path(v).resolve().is_relative_to((p.ROOT/'.lake/packages').resolve())) for v in paths[key]['filtered'])
        for retained in row['retained_inputs']+row['retained_outputs']:
            b=retained['original_binding'];s=retained['snapshot_binding'];check_binding(s)
            assert b['sha256']==s['sha256'] and b['bytes']==s['bytes']
        assert len(row['retained_inputs'])==len(row['input_bindings'])
        assert len(row['retained_outputs'])==len(row['output_bindings'])
        if row['exit_code']==0:
            for b in row['input_bindings']+row['output_bindings']:check_binding(b)
        else:assert row['failed_attempt_retained']
        history.append(dict(label=row['label'],exit_code=row['exit_code'],
          every_original_input_byte_retained=True,every_actual_log_exit_byte_retained=True,
          current_success_inputs_outputs_rehashed=row['exit_code']==0))
    types=records(bylabel['control-types-v2']);kernel=records(bylabel['control-kernel-v4'])
    boundary=records(bylabel['control-boundary-v2']);resolver=records(bylabel['control-resolver-v1'])
    preparation=p.load(p.OUT/'controls-preparation-v1.json')
    expected_theorems={'ZetaNine.AnalyticPhase.'+n for n in preparation['theorems']}
    expected_definitions={'ZetaNine.AnalyticPhase.'+n for n in preparation['definitions']}
    actual_theorems={x['name'] for x in types if x['kind']=='theorem'}
    actual_definitions={x['name'] for x in types if x['kind']=='definition'}
    assert actual_theorems==expected_theorems and len(actual_theorems)==34
    assert actual_definitions==expected_definitions and len(actual_definitions)==7
    inventories=[x for x in types if x['kind']=='module_inventory']
    module_names={n for x in inventories for n in x['constant_names']+x['extra_names']}
    module_records={x['name']:x for x in types if x['kind'] in ['module_declaration','module_extra']}
    assert module_names==set(module_records) and len(inventories)==2
    auxiliary_names=sorted(module_names-expected_theorems-expected_definitions)
    assert len(auxiliary_names)==27
    assert all(x['value_raw'] is not None for x in module_records.values() if not x['isProp'])
    assert all(x['value_raw'] is not None for x in types if x['kind']=='definition')
    comparisons=[x for x in kernel if x['kind']=='theorem_compare']
    assert {x['actual'] for x in comparisons}==expected_theorems
    assert all(x['type_exprEqual'] and x['type_isDefEq'] for x in comparisons)
    definitions=[x for x in kernel if x['kind']=='definition_compare']
    assert {x['actual'] for x in definitions}==expected_definitions
    assert all(x['type_exprEqual'] and x['type_isDefEq'] and x['value_isDefEq'] and
      x['normalized_value_exprEqual'] and x['normalized_value_isDefEq'] for x in definitions)
    assert all(x['value_exprEqual'] is False for x in definitions), 'Never rewrite raw false as true'
    assert {x['name'] for x in kernel if x['kind']=='definition_rfl'}=={
      'original_value_'+n for n in preparation['definitions']}
    domain=[x for x in kernel if x['kind']=='exact_domain_compare']
    assert len(domain)==1 and domain[0]['type_exprEqual'] and domain[0]['type_isDefEq']
    helpers=[x for x in kernel if x['kind']=='definition_helper_compare']
    assert len(helpers)==14 and len({x['actual'] for x in helpers})==8
    assert all(x['type_exprEqual'] and x['value_exprEqual'] and x['type_isDefEq'] and x['value_isDefEq']
      and x['actual_value_typed'] and x['expected_value_typed'] for x in helpers)
    assert len(boundary)==15 and {x['name'] for x in boundary}=={
      'APBoundary.'+n for n in preparation['typed_boundary_names']}
    assert all(x['kind']=='typed_boundary' and x['isProp'] for x in boundary)
    axiom_sets=0;raw_count=0
    for item in types+kernel+boundary:
        for field,value in item.items():
            if field.endswith('axioms'):
                assert set(value)<=STD3;axiom_sets+=1
            if field.endswith('_raw') and value is not None:
                assert isinstance(value,str) and value and '...' not in value and '…' not in value
                raw_count+=1
    source_contracts=[];exports=[]
    for module in p.EXPECTED:
        original=p.TASK/'formalization'/(module+'.lean')
        private=p.PROJECT/'missions/zeta9/formalization'/(module+'.lean')
        text=original.read_text(encoding='utf-8-sig');actual=private.read_text(encoding='utf-8-sig')
        assert prefixes(text)==prefixes(actual)
        first=re.search(r'(?m)^theorem ',text).start()
        actual_first=re.search(r'(?m)^theorem ',actual).start()
        assert text[:first]==actual[:actual_first]
        assert not re.search(r'(?m)^\s*(?:axiom|opaque|constant)\s',actual)
        assert not re.search(r'\b(?:sorry|admit|native_decide)\b',actual)
        dst=p.OUT/'native-export'/(module+'.lean');p.write(dst,private.read_bytes());assert p.sha(dst)==p.sha(private)
        exports.append(p.binding(dst))
        source_contracts.append(dict(module=module,shared=p.binding(original),compiled_private=p.binding(private),
          exported_source=p.binding(dst),every_statement_prefix_through_assignment_exact=True,
          header_and_all_definition_source_bytes_exact=True,only_private_proof_body_repairs=True))
    assert prefixes((p.PROJECT/'missions/zeta9/formalization/AnalyticPhaseUpperBound.lean').read_text(encoding='utf-8'))[
      'phase_global_upper_bound']=='theorem phase_global_upper_bound :\n    ∀ x : ℝ, 1 < x → phase x ≤ (-2641 / 250 : ℝ) :='
    pure=p.TASK/'verification/formalization-analytic-phase-upper-bound-preparation-2026-10-07'
    assert p.sha(pure/'preparation-audit.json')=='4557b3900b3c9cd23d2d9a8543560f066c6ae85e856861a4c805da987b470fb7'
    for b in p.load(pure/'preparation-audit.json')['stable_inputs']:
        path=p.ROOT/b['root_relative']
        assert path.stat().st_size==b['bytes'] and p.sha(path)==b['sha256']
    resolved=[];dependency_paths=set();own_resolved=set();counts=collections.Counter()
    for item in resolver:
        assert item['kind']=='actual_module_resolver'
        file=Path(item['canonical_olean']).resolve();assert file.exists()
        if file.is_relative_to(p.PROJECT.resolve()):kind='own_SOURCE_compiled_phase';own_resolved.add(item['module'])
        elif file.is_relative_to((p.ROOT/'.lake/packages').resolve()):kind='pinned_package_dependency'
        elif file.is_relative_to(TOOLCHAIN):kind='intrinsic_pinned_Lean_toolchain'
        else:raise AssertionError('Foreign proof object in actual resolver: '+str(file))
        counts[kind]+=1
        companions=sorted(x.resolve() for x in file.parent.glob(file.name+'*') if x.is_file())
        dependency_paths.update(companions)
        resolved.append(dict(**item,origin_kind=kind,
          available_companions=[str(x) for x in companions],
          companion_note='All available companions are frozen; findOLean reports the actual primary module path'))
    assert own_resolved=={'missions.zeta9.formalization.AnalyticPhase','missions.zeta9.formalization.AnalyticPhaseUpperBound'}
    for name,value in [('actual-types-and-auxiliaries.json',types),('actual-kernel-and-definitions.json',kernel),
      ('actual-typed-boundaries.json',boundary),('actual-import-resolver.json',resolved)]:p.dump(p.OUT/name,value)
    p.dump(p.OUT/'source-contracts.json',source_contracts)
    p.dump(p.OUT/'source-dependency-linkage.json',dict(
      native_base_source_success='native-base-v5',native_upper_source_success='native-upper-v2',
      base_success_appears_before_upper=rows.index(bylabel['native-base-v5'])<rows.index(bylabel['native-upper-v2']),
      upper_compiled_against_own_preceding_SOURCE_object=bylabel['native-base-v5']['output_bindings'],
      current_base_object_hash_equals_source_success_and_every_later_control_input=True,
      each_control_preserves_own_base_and_upper_source_object_input_snapshots=True,
      actual_loader_finds_both_modules_only_in_aph1=True,
      limitation='Original source runner recorded primary source/config inputs; its own base dependency is linked from prior SOURCE receipt and all later control pre-call snapshots. No source call is rerun.'))
    readme='''Native actual phase AUTHOR PASS: private Base V5 + Upper V2 compiled from source in fresh aph1.

The actual theorem is `∀ x : ℝ, 1 < x → phase x ≤ (-2641 / 250 : ℝ)`.
The stronger certified bound is `< -10564011/1000000`.
Only the actual phase component is closed. Moment asymptotics, infinite-tail estimates and uniform o(1) remain outside this audit; complete Z9.A is not claimed.

`native-export/AnalyticPhase.lean` and `native-export/AnalyticPhaseUpperBound.lean` are the exact compiled sources for a future fresh independent audit. Their historical UNCOMPILED headers are deliberately byte-identical to the original source contracts. Original shared candidates and pure preparation remain frozen; the first original source attempts failed and are retained.

All 34 source-exact theorem types, all 7 full definition types/values, 7 genuine whole-function rfl proofs, 27 compiler auxiliaries and 15 typed boundaries pass. All actual axiom sets lie in propext/Classical.choice/Quot.sound.

All 7 raw definition value Expr.equal results are false due to compiler proof-helper names/reuse; the complete raw expressions and false results are preserved. Their full raw values pass actual isDefEq. Every related helper pair passes full raw type AND proof-value Expr.equal, actual isDefEq and value typing. Transparently expanding only those checked proposition-valued helpers makes all 7 complete values Expr.equal, without erasing binder names or metadata.

Actual Lean-loader resolution covers every imported module. Only own SOURCE-built aph1 phase objects, pinned Mathlib packages and the intrinsic pinned Lean 4.33.1 toolchain are allowed. No Root or other agent proof objects, API operations or credentials are used.

All failures retain every original input byte, full stdout/stderr/log, actual exit, selected paths and any outputs. This is an author audit, not an independent second audit. Scope registration/workspace check are delegated to Root by its explicit coordination message.
'''
    p.write(p.OUT/'README.md',readme)
    paths=set(dependency_paths)
    paths.update(x.resolve() for x in p.OUT.rglob('*') if x.is_file() and x.name!='author-audit.json')
    paths.update((p.TASK/'formalization'/(m+'.lean')).resolve() for m in p.EXPECTED)
    paths.update(x.resolve() for x in pure.iterdir() if x.is_file())
    for row in rows:
        if row['exit_code']==0:
            paths.update((p.TASK/b['task_relative']).resolve() for b in row['input_bindings']+row['output_bindings'])
    bindings=[]
    for path in sorted(paths,key=lambda x:str(x).casefold()):
        b=dict(absolute_path=str(path),bytes=path.stat().st_size,sha256=p.sha(path))
        if path.is_relative_to(p.TASK.resolve()):b['task_relative']=path.relative_to(p.TASK.resolve()).as_posix()
        elif path.is_relative_to(p.ROOT.resolve()):b['root_relative']=path.relative_to(p.ROOT.resolve()).as_posix()
        else:assert path.is_relative_to(TOOLCHAIN)
        bindings.append(b)
    for b in bindings:
        path=Path(b['absolute_path']);assert path.stat().st_size==b['bytes'] and p.sha(path)==b['sha256']
    audit=dict(status='NATIVE_ACTUAL_PHASE_AUTHOR_PASS',role='AUTHOR; fresh independent second audit still required',
      project_task_relative='.rt/aph1',Lean_executed=True,API_executed=False,foreign_proof_objects_borrowed=False,
      final_actual_terminal_session=34191,final_actual_terminal_exit=0,source_actual_terminal_sessions=[73366,97432],
      controls_actual_terminal_sessions=[17567,96386,34191],current_Lean_processes_owned_by_this_author=0,
      actual_theorem='forall x : Real, 1 < x -> ZetaNine.AnalyticPhase.phase x <= -2641/250',
      stronger_certified_bound='phase x < -10564011/1000000 for every real x > 1',
      complete_Z9_A_moments_asymptotics_uniform_error_PASS=False,
      exact_shared_candidates_and_original_pure_preparation_immutable=True,
      sources=source_contracts,exported_compiled_sources=exports,
      actual_calls=len(rows),actual_success_calls=sum(x['exit_code']==0 for x in rows),
      actual_failed_calls=sum(x['exit_code']!=0 for x in rows),every_failure_complete_and_unaccepted=True,
      successful_required_labels=required,actual_call_history=history,
      theorem_type_count=34,exact_source_expected_theorem_types_kernel_isDefEq=True,theorem_types_Expr_equal=True,
      exact_unrestricted_open_domain_checked=True,definition_count=7,full_definition_types_values_present=True,
      raw_full_value_Expr_equal_count_true=0,raw_full_value_Expr_equal_count_false=7,
      raw_false_values_preserved=True,raw_full_value_actual_isDefEq_all=True,whole_function_rfl_count=7,
      transparent_checked_helper_expansion_Expr_equal_count=7,
      no_binder_metadata_erasure=True,related_helper_pair_records=len(helpers),unique_canonical_definition_helpers=8,
      all_related_helper_full_type_value_Expr_equal_isDefEq_and_value_typing=True,
      actual_source_module_declarations=len(module_names),actual_auxiliary_count=len(auxiliary_names),
      actual_auxiliary_names=auxiliary_names,all_auxiliary_types_and_Std3_present=True,
      all_nonprop_module_declaration_full_values_present=True,typed_boundary_count=15,
      actual_Std3_axiom_set_checks=axiom_sets,raw_expression_fields_no_truncation=raw_count,
      actual_import_module_count=len(resolved),actual_import_origins=dict(counts),
      actual_primary_and_available_companion_dependency_files=len(dependency_paths),
      all_actual_paths_restricted_to_own_pinned_packages_intrinsic_Lean=True,
      single_serial_author_lane=1,LEAN_NUM_THREADS=1,LAKE_JOBS=1,lean_option='-j1',
      scope_and_workspace_check='Root explicitly owns final registration/check to prevent parallel writes; author does not modify scope',
      stable_binding_count=len(bindings),stable_bindings=bindings,
      independent_audit_required_before_platform_port=True)
    p.dump(p.OUT/'author-audit.json',audit)
    print('NATIVE_ACTUAL_PHASE_AUTHOR_PASS',flush=True)
    print('Actual calls/success/failure:',len(rows),sum(x['exit_code']==0 for x in rows),sum(x['exit_code']!=0 for x in rows),flush=True)
    print('Bindings:',len(bindings),'imports:',len(resolved),'dependency files:',len(dependency_paths),flush=True)
    print('Report SHA256:',p.sha(p.OUT/'author-audit.json'),flush=True)
    for b in exports:print('Export:',b['task_relative'],b['sha256'],flush=True)
if __name__=='__main__':main()
