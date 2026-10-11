"""Freeze actually terminal Outputs native AUTHOR evidence. No Lean/API calls."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,collections
import execute_native_author as e
OUT,TASK,PROJECT,PREP=e.OUT,e.TASK,e.PROJECT,e.PREP

def rows(name):
    return [json.loads(line) for line in (OUT/name).read_text(encoding='utf-8-sig').splitlines() if line.startswith('{')]

def binding(path):return e.p.binding(path)

def main():
    state=e.gate();receipt=e.load(OUT/'compile-receipt.json')
    checks=[]
    def require(name,predicate,details=None):
        assert predicate,name;checks.append(dict(name=name,passed=True,details=details))
    require('actual rows terminal',len(receipt['rows'])==30)
    failed=[row for row in receipt['rows'] if row['exit_code']!=0]
    require('one actual failed Outputs call retained and excluded',len(failed)==1 and
        failed[0]['label']=='source-CoefficientMapFormalTransportOutputs' and failed[0]['failure_retained'])
    require('29 actual successes',sum(row['exit_code']==0 for row in receipt['rows'])==29)
    latest={row['label']:row for row in receipt['rows']}
    require('27 planned and 2 additional final calls pass',len(latest)==29 and all(row['exit_code']==0 for row in latest.values()))
    full=rows('control-OutputsFullTypeAudit.log');bound=rows('control-OutputsBoundaryAudit.log')
    defs=rows('control-OutputsDefinitionsAudit.log');serializer=rows('control-IndependentExprDagValidationV3.log')
    require('16 complete source/expected original quantified types',len(full)==16 and all(
        row['kind']=='actual_complete_source_expected_type' and row['type_kernel_equal'] and
        row['all_fields_Expr_equal_roundtrip'] for row in full))
    expected_names=[e.p.NS+'.'+row['name'] for row in state['original_exact_headers']]
    require('all original16 theorem names exactly reached',[row['declaration'] for row in full]==expected_names)
    require('nine actual boundary proofs',len(bound)==9 and all(row['kind']=='actual_closed_boundary' and
        row['all_fields_Expr_equal_roundtrip'] for row in bound))
    require('eighteen complete native definitions type/value kernel equal',len(defs)==18 and all(
        row['kind']=='actual_complete_definition_kernel_value' and row['type_kernel_equal'] and
        row['value_kernel_equal'] and row['all_fields_Expr_equal_roundtrip'] for row in defs))
    fixtures=[row for row in serializer if row['kind']=='expr_dag_validation']
    small=[row for row in serializer if row['kind']=='expr_dag_small_source_validation']
    require('twenty serializer fields and three own small source controls',len(fixtures)==20 and len(small)==3 and
        all(row['all_fields_roundtrip'] and row['raw_repr_reconstruction_equal'] for row in serializer))
    allowed={'propext','Classical.choice','Quot.sound'}
    axioms=[]
    for row in full+bound+defs+small:
        for key in ['axioms','source_axioms','expected_axioms']:
            if key in row:
                require('Std3 '+row.get('declaration',row.get('source_name',''))+' '+key,
                        set(row[key])<=allowed)
                axioms.append(dict(declaration=row.get('declaration',row.get('source_name')),field=key,axioms=row[key]))
    require('80 actual axiom records',len(axioms)==80)
    own=e.load(OUT/'actual-own-object-resolution.json');extra=e.load(OUT/'additional-definition-audit-state.json')
    require('25 initial native/control paths all own objects',len(own)==25 and all(row['own_object_resolution_passed'] for row in own))
    require('additional whole-definition own object path',Path(extra['actual_own_object_resolution']['resolved_absolute']).resolve()==
        (PROJECT/'b/lib/lean/OutputsDefinitionsAudit.olean').resolve())
    source=PROJECT/'missions/zeta9/formalization/CoefficientMapFormalTransportOutputs.lean'
    original_headers=e.p.statement_headers(e.p.CANDIDATE.read_bytes())
    require('all16 original complete headers preserved',e.p.statement_headers(source.read_bytes())==original_headers)
    require('compiled private v2 exact hash',e.p.sha(source)=='8b2fc477c10a698f9b5bef004531861c392d93da0377a2874965c8ce470d2fa6')
    require('shared initial f16 source unchanged',e.p.sha(e.p.CANDIDATE)=='f16dc8be54bd58c09f240ed3404ba3810297e1a8e9d9ab9806893d410862f09d')
    require('verified ccef Jets exact native input',e.p.sha(PROJECT/'missions/zeta9/formalization/CoefficientMapFormalTransportJets.lean')==e.p.JETS_SHA)
    export=OUT/'OutputsVerifiedSource.lean'
    if export.exists():require('existing exact export immutable',export.read_bytes()==source.read_bytes())
    else:export.write_bytes(source.read_bytes())
    all_paths=set()
    def add(record):
        path=TASK/record['task_relative']
        require('rehash '+record['task_relative'],path.stat().st_size==record['bytes'] and e.p.sha(path)==record['sha256'])
        all_paths.add(path)
    for row in e.load(PREP/'preparation-verification.json')['files']:add(row)
    for row in e.load(PREP/'source-inputs.json')['prior_freeze_descriptors']:add(row)
    for row in state['source']:
        all_paths.add(PROJECT/row['project_relative']);add(row['immutable_initial_snapshot'])
    for row in state['controls']:
        all_paths.add(PROJECT/row['project_relative']);add(row['immutable_source'])
    for row in receipt['rows']:
        for key in ['stdout','stderr','log','exit_file','selected_paths']:add(row[key])
        for key in ['retained_input_bindings','retained_output_bindings']:
            require('actual '+key+' retained '+row['label']+' '+str(row['attempt']),key in row)
            for snap in row[key]:add(snap['snapshot_binding'])
        for record in row['output_bindings']:
            # Historical objects are retained separately; final own object hashes also bind here.
            path=TASK/record['task_relative']
            if path.is_file() and e.p.sha(path)==record['sha256']:all_paths.add(path)
        for key in ['LEAN_PATH','LEAN_SRC_PATH']:
            selected=e.load(TASK/row['selected_paths']['task_relative'])[key]['filtered']
            require('filtered own/package search paths '+row['label']+' '+key,all(
                Path(raw).resolve().is_relative_to(PROJECT.resolve()) or
                Path(raw).resolve().is_relative_to((e.p.ROOT/'.lake/packages').resolve()) for raw in selected))
    for row in latest.values():
        for record in row['input_bindings']+row['output_bindings']:add(record)
    for path in OUT.rglob('*'):
        if path.is_file() and '__pycache__' not in path.parts and path.name not in {'author-audit.json','AUTHOR_SHA256SUMS.txt'}:
            all_paths.add(path)
    for path in sorted(PROJECT.glob('b/lib/lean/**/*.olean*')):all_paths.add(path)
    stable=[binding(path) for path in sorted(all_paths)]
    require('all final stable paths rehashed',all(e.p.sha(TASK/row['task_relative'])==row['sha256'] and
        (TASK/row['task_relative']).stat().st_size==row['bytes'] for row in stable))
    summary=dict(actual_attempts=30,actual_successful_calls=29,actual_failed_Lean_calls=1,
        actual_successful_Lean_calls=28,actual_runtime_calls=1,planned_calls=27,
        planned_final_success_calls=27,additional_whole_definition_calls=2,
        fresh_native_sources=21,compiled_source_theorems=16,complete_expected_theorems=16,
        actual_whole_type_kernel_comparisons=16,actual_complete_definition_type_kernel_comparisons=18,
        actual_complete_definition_value_kernel_comparisons=18,actual_boundary_proofs=9,
        source_expected_and_boundary_and_small_Expr_reconstructions=160,
        serializer_field_fixtures=20,serializer_small_sources=3,Std3_reports=80,
        actual_own_object_resolutions=26,stable_files=len(stable),checks=len(checks))
    audit=dict(verdict='PASS',role='Outputs native AUTHOR; independent native review still required',
        frozen_at_utc=datetime.now(timezone.utc).isoformat(),checks=checks,counts=summary,
        original_shared_source=binding(e.p.CANDIDATE),compiled_private_source=binding(source),
        verified_export=binding(export),original_exact_headers=original_headers,
        original_preparation_and_snapshots_immutable=True,private_elaboration_repairs=e.load(OUT/'private-proof-repairs.json'),
        executor_provenance=e.load(OUT/'executor-provenance.json'),
        all_actual_complete_source_expected_records=full,all_actual_boundary_records=bound,
        all_actual_complete_definition_records=defs,actual_axiom_records=axioms,
        actual_own_object_resolutions=own+[extra['actual_own_object_resolution']],
        execution_receipt=receipt,stable_files=stable,retained_failed_calls_excluded=failed,
        author_expectation_and_serializer_SOURCE_reuse_disclosed=True,cache_objects_borrowed=False,
        Root_or_foreign_proof_fallback_permitted=False,API_Root_install_or_mission_operations=False,
        current_platform_target='19653cff-d481-498a-a717-10630d1ca1b7',
        five_finite_output_transport_proved=True,finite_constant_term_transport_proved=True,
        Gamma_left_matrix_transport_proved=True,HasSum_parameter_transport_proved=False,
        integer_multiplier_or_height_or_J_or_irrationality_proved=False,
        independent_review_claimed=False,platform_acceptance_claimed=False)
    e.save(OUT/'author-audit.json',audit)
    sums=[f"{row['sha256']}  {row['task_relative']}" for row in stable]
    sums.append(f"{e.p.sha(OUT/'author-audit.json')}  {(OUT/'author-audit.json').relative_to(TASK).as_posix()}")
    (OUT/'AUTHOR_SHA256SUMS.txt').write_text('\n'.join(sums)+'\n',encoding='utf-8')
    print(json.dumps(dict(verdict='PASS',counts=summary,author_audit_sha256=e.p.sha(OUT/'author-audit.json'),
        verified_export_sha256=e.p.sha(export),independent_review_still_required=True)))

if __name__=='__main__':main()
