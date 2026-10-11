"""Independent KernelBridge platform preparation. No Lean/Lake/API invocation."""
from pathlib import Path
import hashlib,json,subprocess,sys
sys.stdout.reconfigure(encoding='utf-8')
OUT=Path(__file__).resolve().parent; TASK=OUT.parents[3]; ROOT=TASK.parents[1]
PROJECT=TASK/'.rt/ki1'
REVIEW=TASK/'verification/formalization-coefficient-map-kernel-bridge-independent-2026-10-04'
NATIVE_AUTHOR=TASK/'verification/formalization-coefficient-map-kernel-2026-10-04'
SOURCE='missions/zeta9/formalization/CoefficientMapKernelBridge.lean'
NS='ZetaNine.CoefficientMapKernelBridge'
REVIEW_SHA='7a325b3866719750c31e66469399ab85f7c73d8c5c1376356ee1951b320d78b1'
SOURCE_SHA='1ec15a46ae656bb0be0de0eb44afeca3144a7223a84eecf161693be25205bedb'
REV='0df444a360eaa60ab8c11dca51a86af692955474'
NAMES=['CoefficientMap','CoefficientMapJet','CoefficientMapInjectivity','CoefficientMapPartialFractions',
 'CoefficientMapReflection','CoefficientMapFiniteSum','CoefficientMapSummation','CoefficientMapAggregate',
 'CoefficientMapShiftDegree','CoefficientMapTelescoper','CoefficientMapKernelBridge']
BATCHES=['coefficient-map','coefficient-map-jet','coefficient-map-injectivity','coefficient-map-partial-fractions',
 'coefficient-map-reflection','coefficient-map-finite-sum','coefficient-map-summation','coefficient-map-aggregate',
 'coefficient-map-shift-degree','coefficient-map-telescoper']
TARGETS=['original_quartic_aggregate_kernel_zero','original_five_dimensional_map_bijective',
 'inverseMultiplier_actual_HasSum_and_absolute']
MODULES=['missions.zeta9.formalization.'+n for n in NAMES]

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,s):
 p.parent.mkdir(parents=True,exist_ok=True)
 p.write_bytes(s if isinstance(s,bytes) else s.encode('utf-8'))
def dump(p,d):write(p,json.dumps(d,ensure_ascii=False,indent=2)+'\n')
def binding(p):
 return {'root_relative':p.relative_to(ROOT).as_posix(),'task_relative':p.relative_to(TASK).as_posix() if p.is_relative_to(TASK) else None,
         'sha256':sha(p),'bytes':p.stat().st_size}

def main():
 assert sha(REVIEW/'independent-review.json')==REVIEW_SHA
 review=json.loads((REVIEW/'independent-review.json').read_text(encoding='utf-8'))
 assert review['verdict']=='PASS' and review['source_sha256']==SOURCE_SHA
 assert len(review['checks'])==22 and all(x['pass'] for x in review['checks'])
 fixed={x['root_relative']:x for x in review['stable_files']}
 sources=[]
 for name in NAMES:
  rel='missions/zeta9/formalization/'+name+'.lean';p=ROOT/rel
  assert rel in fixed and sha(p)==fixed[rel]['sha256'] and p.stat().st_size==fixed[rel]['bytes']
  sources.append(binding(p))
 # Existing pure source bytes are bound to their own frozen previous batch copyplans.
 # No KernelBridge author-control or proof object is read here.
 deps=[];previous_controls=[]
 for name,batch in zip(NAMES[:-1],BATCHES):
  cp=TASK/'formalization/platform'/batch/'root-copy-plan.json'
  plan=json.loads(cp.read_text(encoding='utf-8'));rel='Definitions/Def_ZetaNine_'+name+'.lean'
  rows=[x for x in plan['files'] if x['root_relative_destination']==rel];assert len(rows)==1
  x=rows[0];p=ROOT/rel;staged=TASK/x['staged_task_relative']
  assert sha(p)==sha(staged)==x['sha256'] and p.stat().st_size==x['bytes']
  deps.append(binding(p));previous_controls.append(binding(cp))
 hs=ROOT/'Definitions/Def_ZetaNine_HarmonicStability.lean'
 assert sha(hs)==fixed['Definitions/Def_ZetaNine_HarmonicStability.lean']['sha256']
 deps.insert(0,binding(hs))
 assert len(sources)==11 and len(deps)==11
 originals=json.loads((REVIEW/'independent-original-types.json').read_text(encoding='utf-8'))
 boundaries=json.loads((REVIEW/'independent-boundary-types.json').read_text(encoding='utf-8'))
 assert len(originals)==37 and len(boundaries)==56
 for rel in ['independent-original-types.json','independent-boundary-types.json','independent-boundary.lean']:
  p=REVIEW/rel;x=fixed[p.relative_to(ROOT).as_posix()];assert sha(p)==x['sha256']
 assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in originals+boundaries)
 source_records=[x for x in originals if x['declaration'].startswith(NS+'.')]
 source_defs=[x for x in source_records if x['definitionValue'] is not None]
 source_proofs=[x for x in source_records if x['definitionValue'] is None]
 assert len(source_defs)==7 and len(source_proofs)==23
 assert all(NS+'.'+n in [x['declaration'] for x in source_proofs] for n in TARGETS)
 assert not (PROJECT/'b').exists() and not (PROJECT/'.lake/build').exists(), 'Requires fresh-empty cache.'
 native_lib='\n'.join('  roots := #['+', '.join('`'+m for m in MODULES)+']' for _ in [0])
 code='import Lake\nopen Lake DSL\npackage zeta9KernelIndependent where\n  buildDir := "b"\n'
 code+='require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "'+REV+'"\n'
 code+='lean_lib Native where\n'+native_lib+'\n  globs := #['+', '.join('.one `'+m for m in MODULES)+']\n'
 code+='lean_lib Definitions\nlean_lib Solutions\nlean_lib Theorems\n'
 write(PROJECT/'lakefile.lean',code)
 for name in ['lean-toolchain','lake-manifest.json']:write(PROJECT/name,(ROOT/name).read_bytes())
 for x in sources+deps:write(PROJECT/x['root_relative'],(ROOT/x['root_relative']).read_bytes())
 (PROJECT/'.lake').mkdir(exist_ok=True)
 if not (PROJECT/'.lake/packages').exists():
  r=subprocess.run(['cmd','/c','mklink','/J',str(PROJECT/'.lake/packages'),str(ROOT/'.lake/packages')],capture_output=True)
  write(OUT/'package-junction-preparation.log',r.stdout+r.stderr);assert r.returncode==0
 kit=TASK/'formalization/platform/coefficient-map-connection'
 graph=(kit/'extract_decl_graph.lean').read_text(encoding='utf-8')
 graph=graph.replace('import missions.zeta9.formalization.CoefficientMapConnection',
       '\n'.join('import '+m for m in MODULES)+'\nimport Definitions.Def_ZetaNine_HarmonicStability')
 graph=graph.replace('let isProj : Name → Bool := fun m => projPrefix.isPrefixOf m',
       'let isProj : Name → Bool := fun m => projPrefix.isPrefixOf m || m == `Definitions.Def_ZetaNine_HarmonicStability')
 graph=graph.replace((kit/'decl_graph.jsonl').as_posix(),(OUT/'actual-decl-graph.jsonl').as_posix())
 for p in [OUT/'extract_decl_graph.lean',PROJECT/'extract_decl_graph.lean']:write(p,graph)
 parser=(kit/'parse-source.lean').read_text(encoding='utf-8')
 old=(kit/'CoefficientMapConnection-oracle-input.lean').as_posix();assert parser.count(old)==1
 parser_inputs=[]
 for name,x in zip(NAMES,sources):parser_inputs.append((name,x['root_relative']))
 parser_inputs+=[('HarmonicStability',deps[0]['root_relative']),
   ('NativeKernelAuthorControl','native-control-author.lean'),('NativeKernelIndependentControl','native-control-independent.lean')]
 for name,path in parser_inputs:
  script='parse-'+name+'.lean'
  code=parser.replace(old,(OUT/(name+'-oracle-input.lean')).as_posix())
  for p in [OUT/script,PROJECT/script]:write(p,code)
 for p in [OUT/'extract_header.lean',PROJECT/'extract_header.lean']:write(p,(kit/'extract_header.lean').read_bytes())
 write(OUT/'native-control-author.lean',(NATIVE_AUTHOR/'type-audit.lean').read_bytes())
 write(OUT/'native-control-independent.lean',(REVIEW/'independent-boundary.lean').read_bytes())
 for name in ['native-control-author.lean','native-control-independent.lean']:write(PROJECT/name,(OUT/name).read_bytes())
 roots=['Definitions/Def_ZetaNine_CoefficientMapKernelBridge.lean']
 for name in TARGETS:
  roots+=['Solutions/Sol_ZetaNine_CoefficientMapKernelBridge_'+name+'.lean',
          'Theorems/Thm_ZetaNine_CoefficientMapKernelBridge_'+name+'.lean']
 modules=MODULES+[x['root_relative'].removesuffix('.lean').replace('/','.') for x in deps]+[
   p.removesuffix('.lean').replace('/','.') for p in roots]
 guards=[]
 for m in modules:
  path=PROJECT/'b/lib/lean'/(m.replace('.','/')+'.olean');s=str(path)
  guards.append({'module':m,'absolute_object_path':s,'characters':len(s),'temporary_suffix_margin':64,
   'path_plus_64':len(s)+64,'pass':len(s)+64<=259})
 assert all(x['pass'] for x in guards)
 dump(OUT/'preparation-state.json',{'status':'PREPARATION_ONLY','Lean_Lake_invocations':0,
  'native_SOURCE_sha256':SOURCE_SHA,'native_mathematics_review':binding(REVIEW/'independent-review.json'),
  'native_review_verdict_is_not_platform_verdict':True,'independent_platform_review_role':True,
  'native_or_author_proof_objects_borrowed':False,'only_Mathlib_package_cache_shared':True,
  'source_and_pure_Definition_bindings':sources+deps,'previous_frozen_copyplans':previous_controls,
  'original_type_control_bindings':[binding(REVIEW/'independent-original-types.json'),binding(REVIEW/'independent-boundary-types.json'),
                                  binding(NATIVE_AUTHOR/'type-audit.lean'),binding(REVIEW/'independent-boundary.lean')],
  'fresh_project':str(PROJECT),'cache_empty':True,'object_path_guards':guards,
  'pending_Kernel_author_freeze':True,'pending_Root_7_and_11_source_install_and_5_record_build_freeze':True,
  'Root_scope_API_credentials_modified':False,'Connection_preparation_and_Matrix_candidate_modified':False})
 dump(OUT/'review-plan.preparation.json',{'status':'NOT_EXECUTED','no_platform_verdict':True,
  'targets':[NS+'.'+n for n in TARGETS],'actual_official_Stage1_Stage2_header_required':True,
  'native_sources':11,'required_existing_true_Definitions':11,'original_type_controls':37,
  'independent_native_boundary_controls':56,'native_source_Definitions':7,'native_source_proofs':23,
  'expected_actual_Definitions':65,'expected_counts_are_not_final_graph_evidence':True,
  'additional_closed_controls':['original n>=2 and Even domains retained','n0 quartic X4 actual F=0 while W nonzero',
   'original first output B and rho3/rho5/rho7/rho9 order','zero target gives zero inverse',
   'nonzero output gives nonzero actual rational quartic','rational inverse not asserted integral',
   'actual Nat k+1 HasSum endpoints and norm summability','pure rho9 target and prescribedL value'],
  'full_value_protocol':{'ordinary_Definitions':'fresh exact type and value records; full Expr/PP distinction',
   'existing_Aggregate_maps':'replay inherited native6 kernel +9rfl and propagate complete staged values',
   'actualAggregateEquiv':'all seven new native-alias type/value isDefEq plus seven wholevalue rfl; genuine proof field closure and inverse data',
   'staged_contexts':'canonical full-value propagation separately labeled; never claim seven direct native comparisons from PP'},
  'proof_checks':['actual required closures reconstructed from fresh graph and exact parser spans',
   'actualAggregateEquiv local proof closure has no Equiv/inverse/prescribed cycle','no original mission or Theorems imports in proof stages',
   'all complete Solution helpers and wrapper collectAxioms subset standard3','references are statement mirrors containing sorryAx'],
  'root_byte_bindings':{'new_Root_modules':7,'required_existing_Definitions':11,
   'stable_records':['root-install-receipt.json','task-build.log','task-build-exit.txt','task-check.log','task-check-exit.txt'],
   'dynamic_scope_API_receipts_not_hashed':True},
  'final_gate':'author four controls frozen and all stable bindings verified; all own fresh replay steps actual0; parent Root7+11 byte/build evidence frozen'})
 dump(OUT/'frozen-input-gates.preparation.json',{'status':'PENDING_FREEZE','author_controls':{
  'author-audit.json':None,'root-copy-plan.json':None,'source-manifest.json':None,'SHA256SUMS.txt':None},
  'root_records':{x:None for x in ['root-install-receipt.json','task-build.log','task-build-exit.txt','task-check.log','task-check-exit.txt']},
  'read_live_author_objects_as_evidence':False,'final_verdict':None,'serial_Lean_lane_allocated':False})
 print(json.dumps({'status':'PREPARATION_ONLY','Lean_Lake_invocations':0,'fresh_project':str(PROJECT),
  'native_sources':len(sources),'true_Definition_sources':len(deps),'Root_future_modules':len(roots),
  'max_object_path':max(x['characters'] for x in guards),'max_path_plus_64':max(x['path_plus_64'] for x in guards),
  'native_controls':[len(originals),len(boundaries)]},ensure_ascii=False,indent=2))

if __name__=='__main__':main()
