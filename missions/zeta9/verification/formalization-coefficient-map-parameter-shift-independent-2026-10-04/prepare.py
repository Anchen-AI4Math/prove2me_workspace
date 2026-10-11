"""Pure setup for independent ParameterShift native review. Never executes Lean."""
from pathlib import Path
import json,hashlib,sys,subprocess
sys.stdout.reconfigure(encoding='utf-8')
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[1];ROOT=TASK.parents[1]
PROJECT=TASK/'.rt/pi1'
OBSERVED='dc629940878fd365e1cb995fe3e4ca6b75b38aee6938eeca37a9fa493e7156b0'
KERNEL=TASK/'verification/formalization-coefficient-map-kernel-bridge-independent-2026-10-04/independent-review.json'
CONNECTION=TASK/'verification/formalization-coefficient-map-connection-independent-2026-10-04/independent-review.json'
REV='0df444a360eaa60ab8c11dca51a86af692955474'
NAMES=['CoefficientMap','CoefficientMapJet','CoefficientMapInjectivity','CoefficientMapPartialFractions',
 'CoefficientMapReflection','CoefficientMapFiniteSum','CoefficientMapSummation','CoefficientMapAggregate',
 'CoefficientMapShiftDegree','CoefficientMapTelescoper','CoefficientMapKernelBridge']

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,s):p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(s if isinstance(s,bytes) else s.encode('utf-8'))
def dump(p,d):write(p,json.dumps(d,ensure_ascii=False,indent=2)+'\n')
def binding(p):return {'root_relative':p.relative_to(ROOT).as_posix(),'sha256':sha(p),'bytes':p.stat().st_size}

def main():
 assert sha(KERNEL)=='7a325b3866719750c31e66469399ab85f7c73d8c5c1376356ee1951b320d78b1'
 assert sha(CONNECTION)=='92940f9b02161210e55af39c625e0cd233eaf7a5bf9d5c1aa2238f0506e28d82'
 kd=json.loads(KERNEL.read_text(encoding='utf-8'));cd=json.loads(CONNECTION.read_text(encoding='utf-8'))
 assert kd['verdict']==cd['verdict']=='PASS'
 frozen={x['root_relative']:x for x in kd['stable_files']}
 sources=[]
 for name in NAMES:
  rel='missions/zeta9/formalization/'+name+'.lean';f=ROOT/rel
  assert sha(f)==frozen[rel]['sha256'];sources.append(binding(f))
 hs=ROOT/'Definitions/Def_ZetaNine_HarmonicStability.lean'
 assert sha(hs)==frozen['Definitions/Def_ZetaNine_HarmonicStability.lean']['sha256'];sources.append(binding(hs))
 cs=TASK/'formalization/CoefficientMapConnection.lean'
 assert sha(cs)==cd['source_sha256']=='098d82f606b5b6fda1e1d08524ef23db3ed3943a90ae109439f5046c031337e8';sources.append(binding(cs))
 candidate=TASK/'formalization/CoefficientMapParameterShift.lean'
 assert sha(candidate)==OBSERVED,'Candidate changed; snapshot/gates must be explicitly refreshed.'
 sources.append(binding(candidate));assert len(sources)==14
 assert not(PROJECT/'b').exists() and not(PROJECT/'.lake/build').exists()
 write(OUT/'candidate-observed-dc6299.lean',candidate.read_bytes())
 native='missions.zeta9.formalization.CoefficientMapParameterShift'
 lake='import Lake\nopen Lake DSL\npackage zeta9ParameterShiftIndependent where\n  buildDir := "b"\n'
 lake+='require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "'+REV+'"\n'
 lake+='lean_lib Native where\n  roots := #[`'+native+']\n  globs := #[.one `'+native+']\nlean_lib Definitions\n'
 write(PROJECT/'lakefile.lean',lake)
 for name in ['lean-toolchain','lake-manifest.json']:write(PROJECT/name,(ROOT/name).read_bytes())
 for x in sources:write(PROJECT/x['root_relative'],(ROOT/x['root_relative']).read_bytes())
 for name in ['expected-types.lean','independent-boundary.lean']:write(PROJECT/name,(OUT/name).read_bytes())
 (PROJECT/'.lake').mkdir(exist_ok=True)
 if not(PROJECT/'.lake/packages').exists():
  r=subprocess.run(['cmd','/c','mklink','/J',str(PROJECT/'.lake/packages'),str(ROOT/'.lake/packages')],capture_output=True)
  write(OUT/'package-junction-preparation.log',r.stdout+r.stderr);assert r.returncode==0
 guards=[]
 for x in sources:
  m=x['root_relative'].removesuffix('.lean').replace('/','.')
  f=PROJECT/'b/lib/lean'/(m.replace('.','/')+'.olean');s=str(f)
  guards.append({'module':m,'object_path':s,'characters':len(s),'suffix_margin':64,'path_plus_64':len(s)+64,'pass':len(s)+64<=259})
 assert all(x['pass'] for x in guards)
 dump(OUT/'preparation-state.json',{'status':'PURE_PREPARATION_ONLY','Lean_Lake_invocations':0,
  'candidate_observed_sha256':OBSERVED,'final_frozen_source_sha256':None,'candidate_is_uncompiled_snapshot':True,
  'native_dep_reviews':[binding(KERNEL),binding(CONNECTION)],'source_bindings':sources,
  'fresh_project':str(PROJECT),'cache_absent':True,'object_path_guards':guards,
  'author_proof_objects_borrowed':False,'only_Mathlib_package_cache_shared':True,
  'expected_type_controls_prepared':17,'own_boundary_controls_prepared':27,
  'these_prepared_counts_are_not_actual_compiled_records':True,
  'Kernel_platform_independent_preparation_or_Connection_Matrix_modified':False,
  'Root_scope_API_credentials_modified':False})
 dump(OUT/'review-plan.preparation.json',{'status':'NOT_EXECUTED','verdict':None,
  'serial_Lean_lane_allocated':False,'candidate_hash_pending_author_freeze':True,
  'source_count':14,'dependencies_actual_native_modules':12,'dependency_pure_HarmonicStability_Definitions':1,
  'fresh_source_compile':None,'source_actual_type_record_count':None,'expected_types':[17,'two whole Definition rfl values plus fifteen independently spelled theorem types'],
  'independent_boundaries':[27,'n0 clipped V counterexample, derived regularity, zero Rold legitimate point, zero q and five true original systems'],
  'final_gate':['wait explicit Root Lean lane release','receive fixed final source and actual author compile/type receipts',
   'verify all frozen source/control/manifest bytes and dependencies','fresh compile every real dependency/source in own empty cache',
   'fresh native full type/value/sourceproof report','compile independently spelled expected types and real boundaries',
   'compare full actual source type expressions and collectAxioms standard3','retain failures and distinguish candidate from final freeze',
   'freeze separate independent-review.json after actual checks pass'],
  'scope':'finite true R parameter transport at regular rational points only; no formal F coordinate transport or infinite sum',
  'Kernel_platform_review_has_priority':True})
 print(json.dumps({'status':'PURE_PREPARATION_ONLY','Lean_Lake_invocations':0,'candidate_snapshot_sha256':OBSERVED,
  'fresh_project':str(PROJECT),'sources':len(sources),'expected_type_controls_prepared':17,'boundary_controls_prepared':27,
  'max_object_path_plus_64':max(x['path_plus_64'] for x in guards)},ensure_ascii=False,indent=2))

if __name__=='__main__':main()
