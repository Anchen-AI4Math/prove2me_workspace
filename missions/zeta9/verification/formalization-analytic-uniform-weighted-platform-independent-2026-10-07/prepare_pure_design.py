from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re, sys

TASK=Path(__file__).resolve().parents[2]
ROOT=TASK.parent.parent
OUT=Path(__file__).resolve().parent
BATCH=TASK/'formalization/platform/analytic-uniform-weighted'
HANDOFF_SHA='6b65b8dbb343f41eed4520b382716055cad7aa4fae6154be27028eb6a02c9640'
PLAN_SHA='680c948ce299c30f48c07bb24b4d677f44a22bb33a0a14684cb080bcf2128297'
NATIVE=TASK/'verification/formalization-analytic-uniform-independent-2026-10-07/independent-audit.json'
NATIVE_SHA='0ca3c96c88a382fc245e47ce51ef6ddd9d56857206c280474406c04a6eb55baa'
ROOT_NATIVE=TASK/'verification/formalization-project-handoff-2026-10-07/root-analytic-uniform-independent-complete-binding-rehash.json'

def load(path):return json.loads(path.read_text(encoding='utf-8-sig'))
def sha(path):
    with path.open('rb') as handle:return hashlib.file_digest(handle,'sha256').hexdigest()
def resolve(row):
    return TASK/row['task_relative'] if 'task_relative' in row else ROOT/row['root_relative'] if 'root_relative' in row else Path(row['absolute_path'])
def bind(path):
    path=path.resolve();data=dict(bytes=path.stat().st_size,sha256=sha(path))
    try:data['task_relative']=path.relative_to(TASK.resolve()).as_posix()
    except ValueError:data['root_relative']=path.relative_to(ROOT.resolve()).as_posix()
    return data
def verify(row):
    path=resolve(row);assert path.stat().st_size==row['bytes'] and sha(path)==row['sha256'],str(path);return path
def proofs(text):
    result={}
    for match in re.finditer(r'(?m)^theorem (\w+)',text):
        end=re.search(r'(?m)^(?:theorem |def |end |#print )',text[match.end():])
        stop=len(text) if end is None else match.end()+end.start()
        result[match.group(1)]=text[match.start():stop].strip()
    return result
def headers(text):
    return {m.group(1):text[m.start():text.index(':=',m.end())+2] for m in re.finditer(r'(?m)^theorem (\w+)',text)}
def defs(text):return {m.group(1):m.group(0).strip() for m in re.finditer(r'(?ms)^def (\w+)\b.*?(?=\n\n)',text)}
def strip_comments(text):return re.sub(r'--[^\n]*','',re.sub(r'/-.*?-/','',text,flags=re.S))

def main():
    sys.stdout.reconfigure(encoding='utf-8')
    report_path=OUT/'pure-independent-review-design.json';assert not report_path.exists()
    assert sha(BATCH/'source-handoff-v1.json')==HANDOFF_SHA and sha(BATCH/'target-plan.json')==PLAN_SHA
    assert sha(NATIVE)==NATIVE_SHA
    native=load(NATIVE);root=load(ROOT_NATIVE)
    assert native['verdict']=='PASS' and root['independent_report_sha256']==NATIVE_SHA
    assert root['Root_personally_stream_rehashed_all'] and root['stable_bindings']==23028 and root['mismatches']==0
    prep=load(BATCH/'source-preparation-v1.json');plan=load(BATCH/'target-plan.json')
    assert len(prep['all_11_native_source_copies'])==11 and len(plan['payloads'])==7
    originals={r['full_name']:r['prefix'] for r in prep['all_original_complete_theorem_prefixes']}
    assert len(originals)==122
    source_rows=[];proof_rows=[];native_defs={}
    for row in prep['all_11_native_source_copies']:
        original=verify(row['author_export']);copy=verify(row['unchanged_source_copy'])
        assert original.read_bytes()==copy.read_bytes()
        text=copy.read_text(encoding='utf-8');namespace=re.search(r'(?m)^namespace (\S+)',text).group(1)
        for name,body in proofs(text).items():
            proof_rows.append(dict(full_name=namespace+'.'+name,name=name,source_module=row['module'],text=body,sha256_utf8=hashlib.sha256(body.encode('utf-8')).hexdigest(),utf8_bytes=len(body.encode('utf-8'))))
        for name,body in defs(text).items():native_defs[namespace+'.'+name]=body
        source_rows.append(dict(module=row['module'],author_export=bind(original),source_copy=bind(copy),byte_exact=True))
    assert len(proof_rows)==122 and len(native_defs)==29
    for row in prep['all_29_original_whole_definition_bodies']:assert native_defs[row['full_name']]==row['body']
    candidate_checks=[]
    for target in plan['targets']:
        sol=verify(target['solution_binding']);ref=verify(target['reference_binding'])
        text=sol.read_text(encoding='utf-8');hs=headers(text);assert len(hs)==123
        for row in proof_rows:
            assert text.count(row['text'])==1 and hs[row['name']]==originals[row['full_name']],row['full_name']
        wrapper=target['original_prefix'].replace('theorem '+target['theorem_name'].rsplit('.',1)[-1],'theorem solution',1)
        assert hs['solution']==wrapper
        code=strip_comments(text)
        assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|partial)\b',code)
        assert not re.search(r'(?m)^import (Theorems|Solutions|missions)\.',code)
        assert ref.read_text(encoding='utf-8').count('by sorry')==1
        candidate_checks.append(dict(target=target['theorem_name'],full_original_headers_and_body_texts_exact=122,wrapper_complete_header_exact=True,complete_Solution=bind(sol),statement_catalog=bind(ref),actual_compiler_calls=0))
    deps=[]
    for row in plan['canonical_dependencies']:
        a,b=verify(row['actual_shared_canonical_source']),verify(row['staged_exact_copy']);assert a.read_bytes()==b.read_bytes()
        deps.append(row)
    for row in plan['payloads']:verify(row['binding'])
    new_defs_source=resolve(next(row['binding'] for row in plan['payloads'] if row['kind']=='definition_new13_functions'))
    new_text=new_defs_source.read_text(encoding='utf-8');new_names=[]
    for row in prep['all_29_original_whole_definition_bodies']:
        if row['body'] in new_text:new_names.append(row['full_name'])
    assert len(new_names)==13 and set(new_names)<=set(native_defs)
    contracts_row=next(row for row in native['stable_files'] if row.get('task_relative')=='.rt/aui1/controls/AURawGoalContractsV2.lean')
    contract_source=verify(contracts_row).read_text(encoding='utf-8')
    raw_body=contract_source.split('namespace AUIndependentContract\n',1)[1].split('end AUIndependentContract',1)[0]
    raw_names=list(proofs(raw_body));assert len(raw_names)==4
    raw_templates=[]
    for target in plan['targets']:
        path=OUT/'source-only-contracts'/('RawGoalContracts_'+target['key']+'.lean')
        assert not path.exists();path.parent.mkdir(exist_ok=True)
        imports='import '+target['local_solution'][:-5].replace('/','.')+'\nset_option autoImplicit false\nset_option maxHeartbeats 16000000\nset_option maxRecDepth 200000\nnoncomputable section\nopen scoped BigOperators Topology\nopen Set Finset Filter Polynomial\nopen ZetaNine\nopen ZetaNine.AnalyticMomentBounds ZetaNine.AnalyticUniformMomentBound ZetaNine.AnalyticWeightedBound\n'
        path.write_text('-- UNCOMPILED INDEPENDENT SOURCE-ONLY CONTRACT: requires its own isolated context.\n'+imports+'namespace AUPIndependentRawContract\n'+raw_body+'end AUPIndependentRawContract\n',encoding='utf-8')
        raw_templates.append(dict(target=target['theorem_name'],binding=bind(path),raw_contract_names=raw_names,source_only_no_objects=True))
    requirements=dict(author_final_report_PASS_and_Root_full_bindings_then_new_explicit_lane_grant_required=True,
        personal_full_author_stream_rehash_before_any_Lean=True,project_initially_absent_no_foreign_objects=True,
        fresh_contexts=['native_full_11_math_Source_closure','standalone_canonical2_plus_new_Definition','isolated_reference_type_catalog','moment_complete_Solution','changing_complete_Solution','uniform_complete_Solution'],
        repeated_122_canonical_theorem_names_three_Solutions_never_imported_together=True,
        all122_original_complete_forall_types_and_full_proof_values=True,all3_wrappers_complete_types_and_values=True,
        all29_whole_definition_types_values_whole_function_rfl=True,all13_new_functions_explicitly_covered=True,
        distinct_whole_definition_count=29,new13_are_subset_of29_not42_distinct=True,
        independently_instantiate_full_original_headers_and_definition_bodies_from_pinned_SOURCE=True,
        all15_original_boundaries_and4_independent_raw_expanded_contracts=True,
        every_actual_visible_module_declaration_and_helper_complete_type_value_inferType_Std3=True,
        full_value_inferType_and_Std3_sets_equal_actual_complete_module_inventory=True,
        visible_compiler_private_match_eq_helpers_and_actual_non_environment_extras_explicit=True,
        strict_lossless_DAG_roundtrip_Expr_equal_inferType_and_isDefEq_all_fields=True,
        metadata_binderInfo_names_universe_levels_syntax_and_full_proof_values_never_erased=True,
        preserve_every_measured_raw_Expr_equal_false_even_when_kernel_true=True,
        only_full_expression_equal_proposition_valued_helpers_after_complete_typing_and_value_checks_may_expand=True,
        twenty_constructor_and_metadata_fixtures_and_three_own_actual_definition_fixtures=True,
        actual_own_canonical_import_paths_dependency_input_receipts_and_full_stock_binding_prepost=True,
        serial_lean_j1_LEAN_NUM_THREADS1_LAKE_JOBS1_only_after_grant=True,
        all_failed_calls_inputs_outputs_logs_snapshots_and_receipts_retained=True,
        no_planned_count_substituted_for_actual_calls=True,
        terminal_driver_OS_own_zero_full_freeze_and_postfreeze_rehash=True,
        only_intrinsic_Lean_and_pinned_Mathlib_package_objects_shared=True,
        native_PASS_never_used_as_platform_PASS=True,source_lexical_fidelity_never_used_as_compiler_PASS=True,
        no_API_credentials_shared_module_install_or_scope_writes=True,
        forbidden_math_object_projects=['afb1','aui1','api1','aph1','apfa1','apfi1','native or platform AUTHOR projects','Root proof objects','any other agent mathematical objects'])
    observations=dict(at=datetime.now(timezone.utc).isoformat(),role='Analytic uniform weighted platform INDEPENDENT pure SOURCE plan',
        status='WAIT_FINAL_PLATFORM_AUTHOR_AND_ROOT_BINDING_PINS_AND_NEW_EXPLICIT_LANE_GRANT',
        native_actual_A_independent_report=bind(NATIVE),native_Root_full_rehash=bind(ROOT_NATIVE),
        native_23028_binding_rehash_here_claimed=False,native_full_Root_rehash_observed=True,
        stage_handoff=bind(BATCH/'source-handoff-v1.json'),stage_target_plan=bind(BATCH/'target-plan.json'),stage_preparation=bind(BATCH/'source-preparation-v1.json'),
        old_frozen_stage_native_PASS_false_is_preparation_time_only_not_current_native_status=True,
        current_transplant_sources_uncompiled=True,platform_author_or_independent_PASS_claimed=False,uploaded=False,
        actual_Lean_calls=0,actual_API_calls=0,credential_reads=0,projects_created=0,objects_created_or_borrowed=0,shared_or_scope_writes=0,
        native_actual_source_modules=11,original_proof_declarations=122,original_proof_breakdown=dict(CoefficientMap=18,Phase=34,new_A=70),
        source_copy_personal_byte_hash_observations=source_rows,all_original_complete_headers=prep['all_original_complete_theorem_prefixes'],
        complete_original_proof_SOURCE_contracts=proof_rows,all29_original_whole_definitions=prep['all_29_original_whole_definition_bodies'],
        new13_subset_of29=new_names,canonical_definition_dependencies=deps,seven_candidate_payloads=plan['payloads'],
        three_solution_personal_lexical_observations=candidate_checks,independent_raw4_SOURCE_origin=contracts_row,raw4_by_target_source_only=raw_templates,
        actual_native_raw_diagnostics_preserved_as_prior_observation=dict(false_types=native['raw_Expr_equal_false_all_original_types'],false_definitions=native['raw_Expr_equal_false_definition_values'],normalization_policy=native['normalization_policy']),
        future_platform_raw_results_must_be_measured_not_predetermined=True,requirements=requirements,
        mathematical_scope=dict(actual_weighted_uniform_A=True,moment_n_ge1_r_le4=True,quartic_degree_le4=True,arbitrary_signs_and_arbitrary_changing_coefficients=True,
            epsilon_coefficient_independent_tends_zero=True,new_HasSum_or_Summable_input=False,new_moment_bound_input=False,new_coefficient_growth_input=False,new_parity_input=False,
            integer_preimage=False,integer_height=False,J_or_nonzero=False,exact_fstar_limit=False,irrationality=False),
        coexists_with_Outputs_platform_independent_design=True,Outputs_or_A_platform_compile_or_upload_PASS_claimed=False)
    report_path.write_text(json.dumps(observations,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status=observations['status'],design_sha256=sha(report_path),design_bytes=report_path.stat().st_size,source11_byte_exact=True,
        proof_declarations_each_solution=122,distinct_whole_definitions=29,new_definition_focus_subset=13,raw_goal_contracts_each_context=4,Lean_calls=0,API_calls=0),indent=2),flush=True)

if __name__=='__main__':main()
