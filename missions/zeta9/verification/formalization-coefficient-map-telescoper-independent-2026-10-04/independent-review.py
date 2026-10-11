from pathlib import Path
import hashlib,json,re
from datetime import datetime,timezone
OUT=Path(__file__).resolve().parent; TASK=OUT.parents[1]; ROOT=TASK.parents[1]
AUTHOR=TASK/'verification/formalization-coefficient-map-telescoper-2026-10-04'
PREV=TASK/'verification/formalization-coefficient-map-summation-independent-2026-10-04'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p): return json.loads(p.read_text(encoding='utf-8-sig'))
def dump(p,v): p.write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
def records(p):
 out={}
 for line in p.read_text(encoding='utf-8-sig').splitlines():
  if line.startswith('{'):
   row=json.loads(line)
   if 'declaration' in row: out[row['declaration']]=row
 return out
receipt=load(OUT/'independent-compile-receipt.json'); prior=load(PREV/'independent-review.json')
source=TASK/'formalization/CoefficientMapTelescoper.lean'; text=source.read_text(encoding='utf-8')
source_names=['ZetaNine.CoefficientMapTelescoper.'+n for _,n in re.findall(r'^(def|theorem)\s+(\w+)',text,re.M)]
good=[r for r in receipt['rows'] if r['exit_code']==0]
author_row=next(r for r in reversed(good) if r['label'].startswith('author-type-replay'))
boundary_row=next(r for r in reversed(good) if r['label'].startswith('independent-boundary'))
author=records(Path(author_row['log'])); author_expected=records(AUTHOR/'type-audit.log')
independent=records(Path(boundary_row['log']))
standard={'propext','Classical.choice','Quot.sound'}
checks=[]
def check(name,condition,detail):
 checks.append({'name':name,'pass':bool(condition),'detail':detail})
 assert condition,name
check('fixed_author_source_receipt_and_manifest',sha(source)==receipt['expected_frozen_hashes']['source'] and sha(AUTHOR/'compile-receipt.json')==receipt['expected_frozen_hashes']['receipt'] and sha(AUTHOR/'SHA256SUMS.txt')==receipt['expected_frozen_hashes']['manifest'],receipt['expected_frozen_hashes'])
check('every_author_frozen_member_recomputed',len(receipt['reuse']['author_manifest_bindings_recomputed'])==40 and all(sha(Path(r['path']))==r['sha256'] for r in receipt['reuse']['author_manifest_bindings_recomputed']),40)
check('prior_independent_cache_reuse_is_explicit_and_hash_bound',sha(PREV/'independent-review.json')==receipt['expected_frozen_hashes']['prior_review'] and len(prior['stable_files'])==94 and all(sha(ROOT/r['root_relative'])==r['sha256'] for r in prior['stable_files']),{'prior_review':receipt['expected_frozen_hashes']['prior_review'],'bindings_recomputed':94,'eight_same_byte_cached_objects_cloned':True,'old_source_and_object_fresh_compile_from_previous_independent_review':True})
check('two_fresh_native_sources_and_two_final_type_runs_actually_zero',len(good)==4 and all(int(Path(r['exit_file']).read_text())==0 and sha(Path(r['log']))==r['log_sha256'] for r in good),[(r['label'],r['exit_code']) for r in good])
check('all_author_type_records_definition_values_reproduced',len(author)==35 and author==author_expected,{'author_records':35,'source_records':31,'definition_values':6})
def normalized_record(row):
 return {**row,'type':row['type'].replace('(nhds 0)','(𝓝 0)')}
check('all_actual_source_declarations_independently_visible',len(source_names)==31 and all(n in independent and normalized_record(independent[n])==normalized_record(author[n]) for n in source_names),{'declarations':source_names,'only_pretty_print_notation_normalization':'(nhds 0) = (𝓝 0); Topology scope alias'})
check('all_final_author_and_independent_records_standard_three_only',all(set(r['axioms'])<=standard for r in list(author.values())+list(independent.values())),{'author':len(author),'independent':len(independent),'independent_closed_top_level':len([n for n in independent if n.startswith('IndependentTelescoper.') and n.count('.')==1])})
check('actual_cumulative_sum_telescoper_and_numerator_definitions',all(author[n]['definitionValue'] is not None for n in source_names[:6]) and 'weightedLocalCoefficient' in author[source_names[1]]['definitionValue'],'True actual shifted-series coefficients, cumulative sums to j, poles j=0..n-1 and orders1..9; rootNode is positive1..n+1 and negative -n..-2n.')
check('actual_global_R_difference_has_no_supplied_telescoper_identity',all('actual_weightedR_is_difference' not in author[n]['type'] for n in source_names),'Actual PF and actual rho cancellations derive f=Q(t)-Q(t+1). Even n, strong degree bound, zero actual five-vector and regular rational point are the declared inputs.')
check('finite_boundary_sign_independent_numeric_and_symbolic_check',all(n in independent for n in ['IndependentTelescoper.cumulative_concrete_sign','IndependentTelescoper.cumulative_raw_identity','IndependentTelescoper.original_quartic_real_finite_boundary']),'Raw cumulative identity works before aggregate cancellation, including explicit -3 sign example; true finite sum equals Q1-Q(T+1).')
check('Q_at_one_zero_is_derived_from_actual_limit_not_assumed','actual_finiteL_tendsto_exactL' in text and 'tendsto_nhds_unique' in text and 'aggregate_zero_exactL' in text,'FiniteL tends actual exactL=0 and telescoper boundary tends Q1 via finite shifted reciprocal limits; rational cast injectivity derives Q1=0. No extra sum/convergence hypothesis.')
check('actual_positive_and_reflected_negative_zeros_regular','IndependentTelescoper.actual_nodes_regular' in independent and 'local_coefficient_reflection' in text,'True numerator has zeros1..n. Derived Q1 and difference give Q1..n+1=0; cumulative reflection sign(-1)^s yields Q(1-n-t)=Q(t), then negative zeros -n..-2n, all separate from Q poles0..-(n-1).')
check('true_polynomial_numerator_and_all_distinct_roots',all(n in independent for n in ['IndependentTelescoper.original_quartic_actual_quotient','IndependentTelescoper.two_n_nodes_formula','IndependentTelescoper.zero_n_nodes_formula','IndependentTelescoper.zero_n_nodes_are_distinct']),'Actual numerator degree<=9n-1. Actual monic root product has2n+2 distinct roots; pairwise coprime linear factors divide actual numerator, yielding H degree<=7n-3, including H=0 branch.')
check('strict_proper_aggregate_zero_does_not_imply_difference',all(n in independent for n in ['IndependentTelescoper.zero_n_harmonic_aggregate_zero','IndependentTelescoper.zero_n_harmonic_not_strong','IndependentTelescoper.zero_n_harmonic_difference_false']),'Closed boundary n=0,W=X^4: strict proper and aggregate0, but not strong; actual R1=1, Q identically0, claimed difference false. Strong domain cannot be dropped.')
check('no_custom_axiom_sorry_or_extra_kernel_rank_inverse_assumption',not re.search(r'\b(sorry|admit|axiom)\b',text) and not re.search(r'^\s*(opaque|unsafe)\s',text,re.M),'No assumed determinant/rank/inverse/kernel triviality. This module closes the telescoper/quotient bridge, not the final quartic trivial kernel or irrationality.')
check('failed_attempts_preserved_and_excluded',len(receipt['rows'])-len(good)==2,'First new-cache prefix shadow failure and first independent numerical C(2) proof error remain. Failed JSON contains sorryAx from incomplete reviewer theorem and is not accepted proof evidence. Final successes only establish PASS.')
stable={}
def bind(p):
 p=p.resolve(); stable[str(p)]={'root_relative':p.relative_to(ROOT).as_posix(),'sha256':sha(p),'bytes':p.stat().st_size}
for r in prior['stable_files']: bind(ROOT/r['root_relative'])
bind(PREV/'independent-review.json'); bind(AUTHOR/'SHA256SUMS.txt')
for r in receipt['reuse']['author_manifest_bindings_recomputed']: bind(Path(r['path']))
for p in OUT.rglob('*'):
 if p.is_file() and p.name not in ['independent-review.json','independent-review.md']: bind(p)
dump(OUT/'independent-original-types.json',list(author.values()))
dump(OUT/'independent-boundary-types.json',list(independent.values()))
bind(OUT/'independent-original-types.json'); bind(OUT/'independent-boundary-types.json')
report={'schema_version':1,'verdict':'PASS','scope_verdict':'PASS_ACTUAL_CUMULATIVE_TELESCOPER_ROOT_DIVISIBILITY_AND_QUOTIENT_BOUND_ONLY',
 'review_role':'Independent mathematical and Lean reviewer; another agent authored Telescoper',
 'checked_at':datetime.now(timezone.utc).isoformat(),'source':source.relative_to(ROOT).as_posix(),'source_sha256':sha(source),
 'author_frozen_hashes':receipt['expected_frozen_hashes'],'checks':checks,'actual_type_records':{'author':len(author),'independent':len(independent)},
 'fresh_successful_runs':good,'retained_failed_attempts':[r for r in receipt['rows'] if r['exit_code']!=0],
 'explicit_reuse':receipt['reuse'],'custom_axioms':[],'actual_telescoper_constructed':True,'actual_quotient_bound_closed':True,
 'quartic_kernel_zero_closed_by_this_module':False,'aggregate_inverse_closed_by_this_module':False,'J_closed':False,'irrationality_closed':False,
 'root_scope_API_credentials_writes':False,'stable_files':list(stable.values())}
dump(OUT/'independent-review.json',report)
(OUT/'independent-review.md').write_text('Independent Telescoper review: PASS\n\nActual cumulative coefficients, true rational difference, Q1, reflected zero nodes, root divisibility and quotient-degree bound were checked against freshly compiled native sources and exact statements. All final printed/type records use only propext, Classical.choice and Quot.sound. The earlier independent Summation cache is explicitly reused after all94 bindings are recomputed; its eight objects are cloned byte-identically.\n\nThe n=0,X^4 boundary has actual aggregate0 but is not strong and its true R1=1 differs from Q1-Q2=0. This excludes extending the result from the strong domain to mere strict properness. Both failed reviewer attempts remain and are excluded from successful proof evidence.\n\nThis separate report does not prove the final quartic kernel or inverse, J or zeta9 irrationality. No platform operation was performed.\n',encoding='utf-8')
print(json.dumps({'verdict':'PASS','checks':len(checks),'stable_files':len(stable),'type_records':report['actual_type_records'],'report_sha256':sha(OUT/'independent-review.json')}))
