"""Fresh native/staged full KernelBridge definition-value comparison, no borrowed objects."""
from pathlib import Path
import hashlib,json,os,subprocess,sys
sys.stdout.reconfigure(encoding='utf-8')
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[2];PROJECT=OUT/'p';BUILD=TASK/'.rt/k1/b'
NS='ZetaNine.CoefficientMapKernelBridge';ALIAS=NS+'ValueComparison'
NAMES=['positiveProduct','negativeProduct','aValue','bValue','actualAggregateEquiv','inverseMultiplier','prescribedL']
STD={'propext','Classical.choice','Quot.sound'}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
def write(p,s):p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(s if isinstance(s,bytes) else s.encode('utf-8'))
def dump(p,d):write(p,json.dumps(d,ensure_ascii=False,indent=2)+'\n')
def rows(p):return [json.loads(l) for l in p.read_text(encoding='utf-8-sig').splitlines() if l.startswith('{')]
definition=(OUT/'staged/Definitions/Def_ZetaNine_CoefficientMapKernelBridge.lean').read_bytes()
assert definition== (PROJECT/'Definitions/Def_ZetaNine_CoefficientMapKernelBridge.lean').read_bytes()
fp=load(OUT/'embedded-bijection-provenance.json');assert fp['definition_sha256']==hashlib.sha256(definition).hexdigest() and fp['closure_has_no_Equiv_inverse_or_prescribed_output_cycle'] and fp['extra_hypotheses']==[]
prefix=b'import Definitions.Def_ZetaNine_CoefficientMapTelescoper\nimport Definitions.Def_ZetaNine_CoefficientMapShiftDegree\n'
assert definition.startswith(prefix)
nativeimport=b'import missions.zeta9.formalization.CoefficientMapKernelBridge'
stagedimport=b'import Definitions.Def_ZetaNine_CoefficientMapKernelBridge'
native=definition.replace(prefix,nativeimport+b'\n',1)
for old,new in [('namespace '+NS+'\n','namespace '+ALIAS+'\n'),('end '+NS+'\n','end '+ALIAS+'\n')]:
 assert native.count(old.encode())==1;native=native.replace(old.encode(),new.encode())
staged=native.replace(nativeimport,stagedimport,1)
# Use the full isDefEq/Expr repr emitter from the frozen actual Aggregate protocol.
aggregate=(TASK/'formalization/platform/coefficient-map-aggregate/native-value-details.lean').read_text(encoding='utf-8-sig')
start=aggregate.index('    let ci ← getConstInfo name');end=aggregate.index('  for name in [`native_value_',start)
emitter=aggregate[start:end]
pairs=', '.join('(`'+NS+'.'+n+', `'+ALIAS+'.'+n+')' for n in NAMES)
proofnames=['native_kernel_value_'+n+'_eq' for n in NAMES]
details='import NativeKernelValueComparisonDefinition\nimport Lean\n\nopen Lean Meta\nset_option autoImplicit false\nset_option maxHeartbeats 4000000\nset_option pp.fullNames true\nset_option pp.universes false\nset_option pp.proofs true\n\n'
for n,p in zip(NAMES,proofnames):details+='theorem '+p+' : '+ALIAS+'.'+n+' = '+NS+'.'+n+' := rfl\n\n'
details+='run_meta do\n  for (name, aliasName) in ['+pairs+'] do\n'+emitter
last=aggregate[aggregate.index('    let ci ← getConstInfo name',end):]
details+='  for name in ['+', '.join('`'+p for p in proofnames)+'] do\n'+last
details+='\nrun_meta do\n  let env ← getEnv\n  let modules := env.header.moduleNames\n  let mut records : Array Json := #[]\n  for (n, ci) in env.constants.toList do\n    if n.isInternal then continue\n    let some idx := env.getModuleIdxFor? n | continue\n    let some m := modules[idx.toNat]? | continue\n    unless m == `missions.zeta9.formalization.CoefficientMapKernelBridge || m == `Definitions.Def_ZetaNine_CoefficientMapKernelBridge do continue\n    let kind := match ci with\n      | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .axiomInfo _ => "axiom"\n      | _ => "other"\n    let range ← findDeclarationRanges? n\n    let line := match range with | some r => r.range.pos.line | none => 0\n    records := records.push (Json.mkObj [("name", toJson n.toString),("module", toJson m.toString),("kind", toJson kind),("startLine", toJson line)])\n  let context := if (env.find? `ZetaNine.CoefficientMapKernelBridge.original_five_dimensional_map_bijective).isSome then "native" else "staged"\n  IO.FS.writeFile ("../kernel-" ++ context ++ "-global-declarations.json") ((toJson records).compress)\n'
stage_details=details.replace('import NativeKernelValueComparisonDefinition','import StagedKernelValueComparisonDefinition',1)
variants=[('NativeKernelValueComparisonDefinition.lean',native),('StagedKernelValueComparisonDefinition.lean',staged),('kernel-native-value-details.lean',details.encode()),('kernel-staged-value-details.lean',stage_details.encode())]
for f,data in variants:write(OUT/'dependencies'/f,data);write(PROJECT/f,data)
programs=[{'file':f,'sha256':sha(PROJECT/f),'task_relative':(OUT/'dependencies'/f).relative_to(TASK).as_posix()} for f,_ in variants]
dump(OUT/'kernel-data-equivalence-provenance.json',{'original_genuine_Definition_sha256':sha(OUT/'staged/Definitions/Def_ZetaNine_CoefficientMapKernelBridge.lean'),'embedded_bijection_provenance_sha256':sha(OUT/'embedded-bijection-provenance.json'),'actual_definition_names':NAMES,'alias_namespace':ALIAS,'programs':programs,'native_alias_genuine_Definition_changes':'Only import prefix and comparison namespace; seven actual closed data bodies retained.','native_staged_alias_only_change':'One import native KernelBridge -> genuine Definition KernelBridge','native_staged_details_only_change':'One alias module import','full_kernel_comparisons_each_environment':7,'closed_whole_value_rfl_equalities_each_environment':7,'extra_hypotheses':[],'borrowed_objects':False,'whole_values_include_constructor_bijection_proof_field':True})
env=os.environ.copy();env.pop('LEAN_PATH',None);obj=BUILD/'lib/lean';runs=[]
steps=[('kernel-native-alias',['lake','env','lean','-o',(obj/'NativeKernelValueComparisonDefinition.olean').as_posix(),'NativeKernelValueComparisonDefinition.lean']),('kernel-native-value-details',['lake','env','lean','kernel-native-value-details.lean']),('kernel-staged-alias',['lake','env','lean','-o',(obj/'StagedKernelValueComparisonDefinition.olean').as_posix(),'StagedKernelValueComparisonDefinition.lean']),('kernel-staged-value-details',['lake','env','lean','kernel-staged-value-details.lean'])]
for label,args in steps:
 p=subprocess.run(args,cwd=PROJECT,env=env,capture_output=True);log=OUT/(label+'.log');write(log,p.stdout+p.stderr);write(OUT/(label+'-exit.txt'),str(p.returncode)+'\n')
 runs.append({'label':label,'command':args,'working_directory':str(PROJECT),'exit_code':p.returncode,'log_sha256':sha(log)})
 dump(OUT/'kernel-data-equivalence-receipt.json',{'runs':runs,'complete':False,'borrowed_objects':False});print(label+': exit '+str(p.returncode),flush=True)
 if p.returncode:print((p.stdout+p.stderr).decode('utf-8-sig'),flush=True)
 assert p.returncode==0
environments=[]
for context in ['native','staged']:
 rs=rows(OUT/('kernel-'+context+'-value-details.log'))
 assert len(rs)==14 and [r['declaration'] for r in rs[:7]]==[NS+'.'+n for n in NAMES]
 assert all(r['kind']=='kernel_definition_value' and r['alias_declaration']==ALIAS+'.'+n and r['type_kernel_equal'] and r['full_value_kernel_equal'] and r['pp_proofs_enabled'] and r['original_expression_repr'] and r['comparison_expression_repr'] and set(r['axioms'])<=STD for n,r in zip(NAMES,rs[:7]))
 assert [r['declaration'] for r in rs[7:]]==proofnames and all(r['kind']=='rfl_or_data_equality' and set(r['axioms'])<=STD for r in rs[7:])
 o=obj/('NativeKernelValueComparisonDefinition.olean' if context=='native' else 'StagedKernelValueComparisonDefinition.olean')
 environments.append({'context':context,'records':rs,'object_task_relative':o.relative_to(TASK).as_posix(),'object_sha256':sha(o)})
dump(OUT/'kernel-data-equivalence-report.json',{'environments':environments,'native_direct_full_value_kernel_comparisons':7,'staged_direct_full_value_kernel_comparisons':7,'closed_whole_value_rfl_equalities':14,'all_standard_axioms':True,'extra_hypotheses':[],'single_import_program_substitution_verified':native.replace(nativeimport,stagedimport,1)==staged and details.replace('import NativeKernelValueComparisonDefinition','import StagedKernelValueComparisonDefinition',1)==stage_details})
dump(OUT/'kernel-data-equivalence-receipt.json',{'runs':runs,'complete':True,'borrowed_objects':False})