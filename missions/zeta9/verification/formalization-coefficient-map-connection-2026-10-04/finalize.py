from pathlib import Path
import hashlib,json,re,sys
sys.stdout.reconfigure(encoding='utf-8')
OUT=Path(__file__).resolve().parent;TASK=OUT.parent.parent;ROOT=TASK.parent.parent
SOURCE=TASK/'formalization/CoefficientMapConnection.lean'
STD={'propext','Classical.choice','Quot.sound'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def write(p,s):p.write_bytes(s.encode('utf-8'))
def dump(p,d):write(p,json.dumps(d,ensure_ascii=False,indent=2)+'\n')
r=load(OUT/'compile-receipt.json');ar=load(OUT/'type-audit-receipt.json')
tr=load(OUT/'type-audit.json');br=load(OUT/'boundary-audit.json')
last=r['rows'][-1]
checks=[]
def check(name,yes,evidence):
 checks.append({'name':name,'pass':bool(yes),'evidence':evidence})
 assert yes,name
check('final_full_native_source_actual_exit_zero',r['complete'] and last['exit_code']==0,
      {'attempt':last['attempt'],'log':last['log'],'exit_file':last['exit_file']})
check('final_source_and_native_object_bound',last['source_sha256']==sha(SOURCE) and
      sha(OUT/last['source'])==sha(SOURCE) and sha(OUT/last['object'])==last['object_sha256'],last)
check('source_copy_exact',(OUT/'p/missions/zeta9/formalization/CoefficientMapConnection.lean').read_bytes()==SOURCE.read_bytes(),
      'The project uses the actual final native source bytes.')
imports=re.findall(r'^import (\S+)',SOURCE.read_text(encoding='utf-8'),re.M)
check('only_actual_Mathlib_imports',len(imports)==5 and all(x.startswith('Mathlib.') for x in imports),imports)
check('no_proof_placeholder_or_new_assumption',not re.search(r'\b(sorry|admit|axiom|unsafe)\b',SOURCE.read_text(encoding='utf-8')),
      'No proof placeholder, axiom declaration or unsafe declaration in final source.')
check('isolated_native_project_no_borrowed_native_objects',r['only_Mathlib_package_cache_shared'] and not r['native_objects_borrowed'],
      'The new p/b project shared only the pinned Mathlib package cache; its source/object was built here.')
decls=re.findall(r'^(def|theorem)\s+(\w+)',SOURCE.read_text(encoding='utf-8'),re.M)
check('every_actual_source_declaration_audited',len(tr['records'])==len(decls)==39 and
      [(x['kind'],x['declaration'].rsplit('.',1)[1]) for x in tr['records']]==decls,
      {'definitions':sum(k=='def' for k,n in decls),'theorems':sum(k=='theorem' for k,n in decls),'records':len(tr['records'])})
check('source_types_values_and_full_Expressions_actual',all(x['type'] and x['type_expression_repr'] for x in tr['records']) and
      all(x['value'] and x['definition_expression_repr'] for x in tr['records'] if x['kind']=='def'),
      'Native Lean getConstInfo/ppExpr/reprStr records, with pp.proofs=true for proof-bearing definition fields.')
check('all_native_source_axioms_standard_only',all(set(x['axioms'])<=STD for x in tr['records']),
      sorted(set(a for x in tr['records'] for a in x['axioms'])))
check('type_and_boundary_audits_actual_success',ar['complete'] and
      all(any(x['label']==label and x['exit_code']==0 and x['native_source_sha256']==sha(SOURCE)
        for x in ar['rows']) for label in ['type-audit','boundary-audit']),ar['rows'])
check('twelve_closed_boundary_records_standard_only',len(br['records'])==12 and
      all(set(x['axioms'])<=STD for x in br['records']),[x['declaration'] for x in br['records']])
types={x['declaration'].rsplit('.',1)[1]:x['type'] for x in tr['records']}
check('homogeneous_kernel_has_actual_inputs_only',all(s in types['connection_homogeneous_kernel_zero'] for s in
      ['1 ≤ n','q.natDegree ≤ 9','connectionD','connectionH','P = 0 ∧ q = 0']),types['connection_homogeneous_kernel_zero'])
check('simple_root_factor_and_multiplicity_proved',all(n in types for n in
      ['connectionV_simple_root','rootMultiplicity_simple_composition','first_factor_eval_one_ne_zero',
       'rootMultiplicity_le_natDegree_rat']),{n:types[n] for n in ['connectionV_simple_root','rootMultiplicity_simple_composition']})
check('actual_reflection_and_odd_highest_degree_exclusion_proved',all(n in types for n in
      ['connectionH_reflection','connectionOperator_reflection','reflected_natDegree_even',
       'reflected_even_coefficients_determine','connectionOperator_degree']),
      'The native proofs establish actual reflection, degree<=29 and even highest degree; fifteen even t coefficients then determine the entire polynomial.')
check('actual_fifteen_coordinate_linear_map_bijective','Fin 15' in types['connectionLinearMap_bijective'] or
      'Function.Bijective' in types['connectionLinearMap_bijective'],types['connectionLinearMap_bijective'])
check('projection_lifted_to_complete_polynomial_identity','connectionOperator' in types['connection_reflected_target_exists_unique'] and
      '∃!' in types['connection_reflected_target_exists_unique'],types['connection_reflected_target_exists_unique'])
check('original_degree_bounded_system_complete_unique','∃!' in types['connection_original_system_exists_unique'] and
      all(s in types['connection_original_system_exists_unique'] for s in ['≤ 14','≤ 4','≤ 9','connectionD','connectionH']),
      types['connection_original_system_exists_unique'])
check('five_actual_research_right_hand_sides','Fin 5' in types['connection_five_systems_unique'] and
      'connectionTarget' in types['connection_five_systems_unique'],types['connection_five_systems_unique'])
btypes={x['declaration'].rsplit('.',1)[1]:x['type'] for x in br['records']}
check('n_zero_truncation_and_written_counterexample_separate',all(n in btypes for n in
      ['n_zero_nat_coordinate_truncated','written_n_zero_nonzero_kernel']),
      {n:btypes[n] for n in ['n_zero_nat_coordinate_truncated','written_n_zero_nonzero_kernel']})
failed=[dict(x,used_for_final_success=False) for x in r['rows']+ar['rows'] if x['exit_code']!=0]
check('all_failed_attempts_retained_and_excluded',bool(failed) and all((OUT/x['source']).exists() and
      sha(OUT/x['log'])==x['log_sha256'] and sha(OUT/x['exit_file'])==x['exit_sha256'] for x in failed),failed)
gate_failure=load(OUT/'retained-author-gate-failure.json')
check('failed_UTF8_record_gate_excluded',gate_failure['used_for_final_PASS'] is False and
      gate_failure['mathematical_source_changed'] is False and gate_failure['actual_exit_codes']==[1,1],gate_failure)
for x in r['rows']+ar['rows']:
 assert sha(OUT/x['source'])==x['source_sha256']
 assert sha(OUT/x['log'])==x['log_sha256'] and sha(OUT/x['exit_file'])==x['exit_sha256']
 if x.get('retained_object'):assert sha(OUT/x['retained_object'])==x['retained_object_sha256']
check('retained_success_and_exit_artifacts_match',True,
      'All attempt source/log/exit artifacts match; successful attempt5 and final7 objects retained. The early attempt2 object was observed and subsequently overwritten, and is not used as a retained final object.')
check('no_R_F_transport_or_irrationality_imported',not any(x.startswith('missions.') for x in imports),
      'This batch proves only the connection polynomial kernel and finite system. Actual rational-function transport, F_(n+2)=C(n)F_n, determinant formula and asymptotics are not asserted.')
targets=[{ 'theorem':n,'actual_type':types[n],
 'axioms':next(x['axioms'] for x in tr['records'] if x['declaration'].endswith('.'+n))}
 for n in ['connection_homogeneous_kernel_zero','connectionLinearMap_bijective',
           'connection_original_system_exists_unique','connection_five_systems_unique']]
report={'schema_version':1,'review_role':'native mathematical source author audit; not independent review',
 'verdict':'PASS','source_sha256':sha(SOURCE),'source_root_relative':SOURCE.relative_to(ROOT).as_posix(),
 'checks':checks,'targets':targets,'native_definitions':12,'native_theorems':27,'native_type_records':39,
 'closed_boundary_records':12,'axioms':sorted(STD),'final_native_attempt':last['attempt'],
 'final_native_actual_exit_code':0,'type_audit_actual_exit_code':0,'boundary_audit_actual_exit_code':0,
 'failed_attempts_retained_excluded':failed,'failed_record_gate_excluded':gate_failure,'source_or_native_objects_borrowed':False,
 'only_Mathlib_package_cache_shared':True,'parameter_domain':'natural n>=1; original even n>=2 is a special case',
 'input_coordinates':'Fin15: P coefficients0..4 followed by q coefficients0..9',
 'output_coordinates':'even t coefficients0,2,...,28; equivalent to u coefficients0..14, not literally the same matrix entries',
 'projection_to_full_equation':'actual native reflection+degree theorem, then actual complete ∃! polynomial P,q theorem',
 'n_zero':'Nat(n-1) truncates to0; written n0 uses signed -1 and has the nonzero q=v^9, P=0 kernel, separately proved in the boundary audit',
 'actual_F_transport_closed':False,'determinant_formula_closed':False,'irrationality_claimed':False,
 'root_scope_API_credentials_modified':False,
 'environment':{'Lean':'4.33.1','Mathlib_revision':'0df444a360eaa60ab8c11dca51a86af692955474','project':'p','build_directory':'b'}}
dump(OUT/'author-audit.json',report)
text='''# Native connection polynomial kernel and finite system

The final source proves the genuine homogeneous equation `D*P.comp u+Hq=0`
forces `P=q=0` for every natural `n>=1` and `q.natDegree<=9`. No bound on P
is needed for this kernel theorem. The proof factors q at n and uses the actual
simple root `v-Cn=(X-C1)*(X+Cn)`, with nonzero first-factor value at1.

The source also defines the fifteen real input coefficients (P degree<=4,
q degree<=9) and proves its linear map bijective. Its output coordinates are
the fifteen even t coefficients, not the literal u-coefficient matrix in the
paper. Actual reflection and degree proofs show these coordinates determine
the complete polynomial. Surjectivity is lifted to the full original equation:
every f of degree<=14 has a unique degree-bounded pair P,q. This includes the
five actual c_n Z_n(u)(u-n-1)^r right-hand sides for r=0,...,4.

Final full native build: attempt7 actual exit0. All39 actual native declaration
records (12 definitions,27 theorems) and12 closed boundary records pass with
only propext, Classical.choice and Quot.sound. Earlier failed native and
boundary attempts are retained and excluded. The new short p/b project shared
only the pinned Mathlib package cache; it borrowed no native proof object.
The early attempt2 kernel object was observed at its successful build and later
overwritten; only the retained attempt5 and final7 objects are hash-bound here.

All principal results retain n>=1. At n0 the Nat subtraction definition of v
differs from the written signed formula. The written n0 system has the explicit
nonzero kernel P=0,q=v^9, proved separately in the boundary audit.

This is an author audit, awaiting independent review. It closes the polynomial
system only. It does not claim actual F transport, the connection determinant,
Smith bounds, asymptotics or zeta irrationality. No root/scope/API/credential
files or previous frozen sources were modified.
'''
write(OUT/'README.md',text)
files=[SOURCE]+[x for x in OUT.iterdir() if x.is_file() and x.name not in ['source-manifest.json','SHA256SUMS.txt']]
files += [x for x in OUT.glob('*attempt-*/*') if x.is_file()]
files += [OUT/'p'/n for n in ['lakefile.lean','lake-manifest.json','lean-toolchain','type-audit.lean','boundary-audit.lean']]
files += [OUT/'p/missions/zeta9/formalization/CoefficientMapConnection.lean',OUT/last['object']]
files=sorted(set(files),key=lambda x:x.relative_to(ROOT).as_posix())
records=[{'root_relative':x.relative_to(ROOT).as_posix(),'task_relative':x.relative_to(TASK).as_posix(),
          'verification_relative':x.relative_to(OUT).as_posix() if x.is_relative_to(OUT) else '../../formalization/CoefficientMapConnection.lean',
          'bytes':x.stat().st_size,'sha256':sha(x)} for x in files]
manifest={'schema_version':1,'source_sha256':sha(SOURCE),'files':records,'files_count':len(records),
 'author_audit_sha256':sha(OUT/'author-audit.json'),'native_compile_receipt_sha256':sha(OUT/'compile-receipt.json'),
 'type_audit_receipt_sha256':sha(OUT/'type-audit-receipt.json')}
dump(OUT/'source-manifest.json',manifest)
write(OUT/'SHA256SUMS.txt',''.join(x['sha256']+'  '+x['verification_relative']+'\n' for x in records)+
      sha(OUT/'source-manifest.json')+'  source-manifest.json\n')
print(json.dumps({'verdict':'PASS','checks':len(checks),'source_sha256':sha(SOURCE),
 'compile_receipt_sha256':sha(OUT/'compile-receipt.json'),'type_audit_receipt_sha256':sha(OUT/'type-audit-receipt.json'),
 'author_audit_sha256':sha(OUT/'author-audit.json'),'manifest_sha256':sha(OUT/'source-manifest.json'),
 'SHA256SUMS_sha256':sha(OUT/'SHA256SUMS.txt'),'stable_files':len(records)},indent=2))
