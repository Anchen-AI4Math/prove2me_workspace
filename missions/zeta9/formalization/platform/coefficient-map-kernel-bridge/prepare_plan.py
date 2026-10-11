"""KernelBridge mechanical preparation only: no Lean execution or root writes."""
from pathlib import Path
import hashlib,json,sys
sys.stdout.reconfigure(encoding='utf-8')
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[2];ROOT=TASK.parents[1]
PROJECT=OUT/'p';BUILD=TASK/'.rt/k1/b';TEL=TASK/'formalization/platform/coefficient-map-telescoper'
NS='ZetaNine.CoefficientMapKernelBridge'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,b):p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b if isinstance(b,bytes) else b.encode('utf-8'))
def dump(p,j):write(p,json.dumps(j,ensure_ascii=False,indent=2)+'\n')
def load(p):return json.loads(p.read_text(encoding='utf-8-sig'))
expected=load(TEL/'preparation-state.json')['sources_sha256']
expected['CoefficientMapShiftDegree']='96efe64f218c07a9d941136af1b4a0874bca9627c01be262c53e4445e0876953'
expected['CoefficientMapKernelBridge']='1ec15a46ae656bb0be0de0eb44afeca3144a7223a84eecf161693be25205bedb'
review_path=TASK/'verification/formalization-coefficient-map-kernel-bridge-independent-2026-10-04/independent-review.json'
assert sha(review_path)=='7a325b3866719750c31e66469399ab85f7c73d8c5c1376356ee1951b320d78b1'
review=load(review_path);assert review['verdict']=='PASS' and len(review['checks'])==22 and len(review['stable_files'])==296
for r in review['stable_files']:assert sha(ROOT/r['root_relative'])==r['sha256']
author=TASK/'verification/formalization-coefficient-map-kernel-2026-10-04'
assert sha(author/'compile-receipt.json')=='07ed208d0eef9d16632320ee1710c4c62919cc948f5fe770eba5dcc315656aa7'
assert sha(author/'SHA256SUMS.txt')=='5e6481b76038db693c73f3bc13f582019ff5ce06c3f5361dadf88d218f69a498'
bindings=[]
for line in (author/'SHA256SUMS.txt').read_text(encoding='utf-8-sig').splitlines():
 h,rel=line.split('  ',1);assert sha(TASK/rel)==h;bindings.append({'task_relative':rel,'sha256':h})
assert len(bindings)==46
for name,h in expected.items():
 src=TASK/'formalization'/(name+'.lean');assert sha(src)==h
 write(PROJECT/'missions/zeta9/formalization'/(name+'.lean'),src.read_bytes())
revision='0df444a360eaa60ab8c11dca51a86af692955474'
write(PROJECT/'lakefile.lean',f'''import Lake
open Lake DSL
package zeta9KernelBridgeOfflineAuthor where
  buildDir := "{BUILD.as_posix()}"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "{revision}"
lean_lib Native where
  roots := #[`missions.zeta9.formalization.CoefficientMapKernelBridge]
  globs := #[{', '.join('.one `missions.zeta9.formalization.'+n for n in expected)}]
lean_lib NativeControls where
  roots := #[`NativeKernelAuthorControl, `NativeKernelIndependentControl]
  globs := #[.one `NativeKernelAuthorControl, .one `NativeKernelIndependentControl]
lean_lib Definitions
lean_lib Solutions
lean_lib Theorems
''')
for name in ['lake-manifest.json','lean-toolchain']:write(PROJECT/name,(ROOT/name).read_bytes())
definitions=['positiveProduct','negativeProduct','aValue','bValue','actualAggregateEquiv','inverseMultiplier','prescribedL']
target_names=['original_quartic_aggregate_kernel_zero','original_five_dimensional_map_bijective','inverseMultiplier_actual_HasSum_and_absolute']
args=['n hn2 hn W hW hzero','n hn2 hn','n hn2 hn b']
types=load(author/'type-report.json');assert len(types)==37
selected=[next(r for r in types if r['declaration']==NS+'.'+n) for n in target_names]
controls=[]
for module,p in [('NativeKernelAuthorControl',author/'type-audit.lean'),('NativeKernelIndependentControl',review_path.parent/'independent-boundary.lean')]:
 h=next(r['sha256'] for r in review['stable_files'] if r['root_relative']==p.relative_to(ROOT).as_posix())
 assert sha(p)==h;write(PROJECT/(module+'.lean'),p.read_bytes())
 controls.append({'module':module,'source_task_relative':p.relative_to(TASK).as_posix(),'sha256':h})
parents=[];missing=[]
for name in list(expected)[:-1]:
 slug={'CoefficientMap':'coefficient-map','CoefficientMapJet':'coefficient-map-jet','CoefficientMapInjectivity':'coefficient-map-injectivity','CoefficientMapPartialFractions':'coefficient-map-partial-fractions','CoefficientMapReflection':'coefficient-map-reflection','CoefficientMapFiniteSum':'coefficient-map-finite-sum','CoefficientMapSummation':'coefficient-map-summation','CoefficientMapAggregate':'coefficient-map-aggregate','CoefficientMapTelescoper':'coefficient-map-telescoper','CoefficientMapShiftDegree':'coefficient-map-shift-degree'}[name]
 batch=TASK/'formalization/platform'/slug;rel='Definitions/Def_ZetaNine_'+name+'.lean';src=batch/'staged'/rel
 if not (batch/'SHA256SUMS.txt').exists():
  missing.append({'definition':rel,'reason':'await fixed parent author freeze; no placeholder generated'});continue
 for line in (batch/'SHA256SUMS.txt').read_text(encoding='utf-8-sig').splitlines():
  h,p=line.split('  ',1);assert sha(batch/p)==h
 assert src.exists();write(PROJECT/rel,src.read_bytes())
 parents.append({'root_relative':rel,'task_relative':src.relative_to(TASK).as_posix(),'sha256':sha(src)})
pure=ROOT/'Definitions/Def_ZetaNine_HarmonicStability.lean'
assert sha(pure)=='5ff9d83ca177893db1eb149da985ff29b85dbe83614650a995e28066f9bd3e92'
write(OUT/'dependencies/Definitions'/pure.name,pure.read_bytes());write(PROJECT/'Definitions'/pure.name,pure.read_bytes())
parents.append({'root_relative':'Definitions/'+pure.name,'task_relative':(OUT/'dependencies/Definitions'/pure.name).relative_to(TASK).as_posix(),'sha256':sha(pure)})
g=(TEL/'extract_decl_graph.lean').read_text(encoding='utf-8-sig')
g=g.replace('CoefficientMapTelescoper','CoefficientMapKernelBridge').replace('NativeTelescoperAuthorControl','NativeKernelAuthorControl').replace('NativeTelescoperIndependentControl','NativeKernelIndependentControl')
write(OUT/'extract_decl_graph.lean',g);write(PROJECT/'extract_decl_graph.lean',g)
parser=(TASK/'formalization/platform/coefficient-map-jet/extract_sketch_info.lean').read_text(encoding='utf-8-sig')
original='missions/zeta9/formalization/platform/coefficient-map-jet/oracle-input.lean';assert parser.count(original)==1
for name in list(expected)+['Def_ZetaNine_HarmonicStability']:
 snapshot='oracle-input.lean' if name.endswith('PartialFractions') else name+'-oracle-input.lean'
 code=parser.replace(original,'../'+snapshot)
 write(OUT/('extract_'+name+'_sketch.lean'),code);write(PROJECT/('extract_'+name+'_sketch.lean'),code)
header=(TEL/'extract_header.lean').read_bytes();write(OUT/'extract_header.lean',header);write(PROJECT/'extract_header.lean',header)
plan={'sources_sha256':expected,'actual_native_sources':11,'pure_Harmonic_definition_byte_preserved':True,
 'source_project_task_relative':PROJECT.relative_to(TASK).as_posix(),'fresh_build_task_relative':BUILD.relative_to(TASK).as_posix(),'cache_objects_reused':False,
 'new_actual_definitions':definitions,'new_definition_count':7,'source_proof_count':23,'source_declaration_count':30,'source_axiom_diagnostics':17,
 'selected_actual_endpoints':[{'name':NS+'.'+n,'arguments':a,'frozen_native_type':r['type'],'axioms':r['axioms']} for n,a,r in zip(target_names,args,selected)],
 'native_controls':controls,'native_author_frozen_bindings':bindings,'native_review_sha256':sha(review_path),
 'required_parent_definitions':parents,'missing_parent_definitions':missing,
 'expected_all_actual_definitions':65,'expected_definition_context_comparisons':455,'old_controls_expected':[37,56],
 'proof_bearing_definition':'actualAggregateEquiv','proof_field_seed':NS+'.original_five_dimensional_map_bijective',
 'proof_field_closure_strategy':'True fresh native Stage1 transitive closure and Stage2 proof/ref spans become dependency-ordered local have terms. Resolved source proof references are renamed to those local bindings; true data references remain fixed genuine Definitions. The exact original bijection type annotates the closed term. No new global helper theorem, kernel/bijection/inverse/output/HasSum hypothesis, or substitute map is added.',
 'proof_field_builder_requires_actual_graph_and_parser_receipts':True,
 'whole_value_protocol':'Seven true KernelBridge Definitions get full isDefEq type/value with pp.proofs=true and full Expr repr in separate fresh native/staged environments. Their alias program differs only by native-versus-genuine-Def import. Existing three Aggregate proof maps retain the same separate full-value protocol. Seven context propagation is not seven native direct calls.',
 'original_domain':'Even n and 2<=n, rational polynomial quartic domain; output b:Fin5->Rat; actual inverseMultiplier, prescribedL, weightedR, HasSum and norm Summable remain unchanged.',
 'excluded_claims':['integer inverse multiplier','height or denominator bounds','small nonzero integer forms','irrationality'],
 'Lean_executed':False,'Stage1_Stage2_results_claimed':False,'root_scope_API_credential_writes':False,'author_PASS_claimed':False,'separate_independent_platform_review_required':True}
dump(OUT/'preparation-state.json',plan)
print(json.dumps({'native_sources_copied':11,'parent_Definitions_copied':len(parents),'missing_parent_Definitions':missing,'controls_copied':2,'official_graph_parser_header_templates_prepared':True,'Lean_executed':False},ensure_ascii=False))
