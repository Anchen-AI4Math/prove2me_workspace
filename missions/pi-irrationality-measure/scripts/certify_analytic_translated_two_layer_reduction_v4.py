"""Exact observed closed-cache reference-domain successor; no Lean or proof changes."""
from __future__ import annotations
import argparse,json,inspect
from pathlib import Path
import certify_analytic_translated_two_layer_reduction_v3 as prior
import certify_analytic_translated_two_layer_reduction as mathematics
stage=prior.stage
SELF=Path(__file__).resolve()
VALIDATION=stage.V/'ap20/analytic-translated-two-layer-reduction-validation-v4'
CERTIFICATE=VALIDATION/'open-sketch-interface-validation-v4.json'
SOURCE_CACHE='OAI.PiExponent.LiteralAnalytic.norm_actual_summand_le._simp_1_1'
GENERATED_CACHE='solution._simp_1_1'
EXTERNAL_DELTAS={
 stage.NORM:{'source_only':['NormedCommRing.toNormedRing','NormedField.toNormedCommRing'],
             'generated_only':['CStarAlgebra.toNormedRing','CommCStarAlgebra.toCStarAlgebra','CommCStarAlgebra.toNormedCommRing','instCommCStarAlgebraComplex']},
 stage.ACTUAL:{'source_only':['IsStrictOrderedRing.toIsOrderedRing'],
               'generated_only':['Nat.instStarOrderedRing','Nat.instStarRing','StarOrderedRing.toIsOrderedRing']}}

def actual_domain_audit():
    read,need=stage.read,stage.need
    source=read(stage.STAGE/stage.SOURCE_JSON);left={r['name']:r for r in source}
    need(len(source)==14 and list(left)==stage.INTERFACE_NAMES,'Actual source14 full-CI domain differs')
    aux=read(stage.STAGE/stage.SOURCE_AUX_JSON)['actualAuxiliaryCIs'];by_aux={r['name']:r for r in aux}
    s=by_aux[SOURCE_CACHE]
    original_project=mathematics.project
    plan=read(stage.STAGE/'preparation.json');mapping={r['source_name']:r['generated_name'] for r in plan['boundary']['exact_observed_data_closed_Prop_pairs']}
    pair=plan['boundary']['CoreData_certified_closed_Prop_pair'];mapping[pair['source_name']]=pair['generated_name'];mapping[SOURCE_CACHE]=GENERATED_CACHE
    parents={};interface=[];owned={};json_hashes={}
    for parent in [stage.NORM,stage.ACTUAL]:
        file=stage.GENERATED_JSON[parent];doc=read(stage.STAGE/file);right={r['name']:r for r in doc}
        need(len(doc)==15 and list(right)==stage.INTERFACE_NAMES+['solution'],'Actual generated15 full-CI domain differs')
        inv=read(stage.STAGE/stage.OWNED_JSON[parent]);raw=inv['rawOwnedCIs'];actual={r['name']:r for r in raw}
        extras=sorted(set(actual)-set(right));need(extras==([GENERATED_CACHE] if parent==stage.NORM else []),'Unexpected actual extra CI domain: '+parent)
        owned[parent]={'raw_names':[r['name'] for r in raw],'extra_CIs':[actual[n] for n in extras]}
        if parent==stage.NORM:
            g=actual[GENERATED_CACHE]
            need(s['actualOwner']=='OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand' and g['actualOwner']==stage.SOLUTION_MODULES[parent]
              and s['kind']==g['kind']=='theorem' and s['closedType'] is True and s['closedValue'] is True and s['isProp'] is True
              and g['closedType'] is True and g['closedValue'] is True and g['isProp'] is True
              and s['value'] is None and g['value'] is None and set(s['axioms'])<=mathematics.STD3
              and all(s[k]==g[k] for k in ['levelParams','type','typeRefs','valueRefs','axioms'])
              and not original_project(s['typeRefs']+s['valueRefs']), 'Observed source/generated cache is not the exact actual closed Std3 Prop pair')
            cache={'source_name':SOURCE_CACHE,'generated_name':GENERATED_CACHE,'source_CI':s,'generated_CI':g,
              'full_type_and_direct_reference_domains_equal':True,'actual_kernel_closed_isProp':True,'Std3_only':True,
              'proof_values_exported':False,'basis':'Actual equal closed Prop types and identical direct refs/Std3; kernel proof irrelevance. Generated local name is an internal proof cache, not a platform interface.'}
        for n in stage.INTERFACE_NAMES:
            need(mathematics.normalized_type(left[n])==mathematics.normalized_type(right[n]) and left[n]['typeRefs']==right[n]['typeRefs'], 'Full14 actual type/reference domain differs: '+n)
            interface.append({'parent_snapshot':parent,'name':n,'full_type_equal':True,'typeRefs_equal':True,
              'source_typeRefs':left[n]['typeRefs'],'generated_typeRefs':right[n]['typeRefs'],
              'source_valueRefs':left[n]['valueRefs'],'generated_placeholder_valueRefs':right[n]['valueRefs'],
              'generated_role':'local typed Open comparator, not a closed proof','source_axioms':left[n]['axioms'],'generated_axioms':right[n]['axioms']})
        sp=original_project(left[parent]['valueRefs']);gp=sorted(set(original_project(right['solution']['valueRefs'])+[n for n in right['solution']['valueRefs'] if n==GENERATED_CACHE]))
        need(sorted(set(n if n in gp else mapping.get(n,n) for n in sp))==gp,'Observed finite actual cache mapping leaves a project reference delta')
        se=set(left[parent]['valueRefs'])-set(sp);ge=set(right['solution']['valueRefs'])-set(gp)
        delta={'source_only':sorted(se-ge),'generated_only':sorted(ge-se)}
        need(delta==EXTERNAL_DELTAS[parent],'Exact finite external instance reference delta changed')
        parents[parent]={'source_project_valueRefs':sp,'generated_project_and_exact_internal_cache_valueRefs':gp,
          'exact_actual_typed_mapping':mapping,'same_names_preserved_before_mapping':sorted(set(sp)&set(gp)),
          'actually_applied_closed_Prop_mapping':{n:mapping[n] for n in sp if n not in gp and n in mapping},
          'project_refs_exact_after_mapping':True,'external_instance_delta':delta,
          'full_type_equal':mathematics.normalized_type(left[parent])==mathematics.normalized_type(right['solution'])}
        need(parents[parent]['full_type_equal'],'Parent solution full type changed')
        for f in [file,stage.OWNED_JSON[parent]]:json_hashes[stage.rel(stage.STAGE/f)]=stage.sha(stage.STAGE/f)
    for f in [stage.SOURCE_JSON,stage.SOURCE_AUX_JSON]:json_hashes[stage.rel(stage.STAGE/f)]=stage.sha(stage.STAGE/f)
    return {'schema_version':1,'source14_and_two_generated15_full_CI_domains_audited':True,'interface_type_and_reference_rows':interface,
      'parent_actual_reference_audit':parents,'complete_actual_owned_extra_CI_audit':owned,'exact_observed_closed_Prop_cache_pair':cache,
      'source_auxiliary_names':[r['name'] for r in aux],'actual_json_sha256':json_hashes,'no_additional_Published_Definition_mapping_needed':True}

def validate():
    audit=actual_domain_audit();saved=mathematics.project;saved_validate=mathematics.validate
    failure=stage.STAGE/'certification-failure-v3.json';f=stage.read(failure)
    stage.need(f['consumer_sha256']==stage.sha(Path(prior.__file__)) and f['exit_code']==1 and f['inner_line']==119 and f['all18contexts_passed'] and f['proof_code_unchanged'] and f['no_API_started'],'Genuine prior strict failure evidence differs')
    original_source=inspect.getsource(saved_validate)
    before="need(sorted(set(mapping.get(n,n) for n in sp))==gp,'Parent project proof references differ beyond exact typed actual cache map')"
    after="need(sorted(set(n if n in gp else mapping.get(n,n) for n in sp))==gp,'Parent project proof references differ beyond exact typed actual cache map')"
    stage.need(original_source.count(before)==1,'Original strict comparison source differs')
    derived_source=original_source.replace('def validate():','def _v4_validate():',1).replace(before,after)
    exec(compile(derived_source,str(SELF)+':exact_original_validate_one_comparison_successor','exec'),mathematics.__dict__)
    def finite_project(refs):return sorted(set(saved(refs)+[n for n in refs if n==GENERATED_CACHE]))
    mathematics.project=finite_project;mathematics.validate=mathematics._v4_validate
    try:result=prior.validate()
    finally:mathematics.project=saved;mathematics.validate=saved_validate;del mathematics._v4_validate
    pair=[r for r in result['actual_typed_auxiliary_Prop_pairs'] if r['source_name']==SOURCE_CACHE and r['generated_name']==GENERATED_CACHE]
    stage.need(len(pair)==1 and pair[0]['parent']==stage.NORM and pair[0]['full_type_equal'] and pair[0]['actual_closed_Prop'],'Original complete strict validator did not pair the exact observed cache')
    result.update({'artifact_kind':'ap20-analytic-translated-two-layer-actual-Open-sketch-derived-validation-v4',
      'actual_full_CI_reference_domain_audit':audit,'finite_internal_closed_Prop_reference_names':[GENERATED_CACHE],
      'finite_reference_domain_basis':'One actual source/generated fully typed closed Prop pair; no prefix or suffix allowlist; all original type/Std3/project/import/budget/Open gates retained',
      'actual_external_instance_reference_differences':EXTERNAL_DELTAS,'compiler_inputs_unchanged':True,'new_Lean_contexts':0,
      'exact_original_strict_function_successor':{'original_function_sha256':stage.digest(original_source.encode()),'derived_function_sha256':stage.digest(derived_source.encode()),'old_comparison':before,'new_comparison':after,'all_other_original_function_bytes_unchanged':True},
      'same_name_project_references_preserved_before_only_genuine_typed_delta_mapping':True,
      'prior_actual_strict_failure':{'record':stage.rel(failure),'record_sha256':stage.sha(failure)},
      'prior_frozen_consumer':stage.rel(Path(prior.__file__)),'prior_frozen_consumer_sha256':stage.sha(Path(prior.__file__))})
    result['implementation_hashes'].update({stage.rel(SELF):stage.sha(SELF),stage.rel(Path(prior.__file__)):stage.sha(Path(prior.__file__)),stage.rel(failure):stage.sha(failure)})
    return result

def main():
    p=argparse.ArgumentParser(description=__doc__);g=p.add_mutually_exclusive_group(required=True);g.add_argument('--certify-existing',action='store_true');g.add_argument('--check-only',action='store_true');a=p.parse_args()
    report=validate();raw=stage.encode(report)
    if CERTIFICATE.exists():stage.need(CERTIFICATE.read_bytes()==raw,'Refusing changed actual derived certificate')
    elif a.certify_existing:CERTIFICATE.parent.mkdir(parents=True,exist_ok=True);CERTIFICATE.write_bytes(raw)
    else:stage.need(False,'Check-only requires genuine derived certificate')
    print(json.dumps({'certificate':stage.rel(CERTIFICATE),'certificate_sha256':stage.sha(CERTIFICATE),'validated':True,'Open_sketch_only':True,'closed_proof':False,'new_Lean_contexts':0,'actual_cache_pairs':1,'max_file_seconds':report['max_file_seconds']},indent=2))
if __name__=='__main__':main()
