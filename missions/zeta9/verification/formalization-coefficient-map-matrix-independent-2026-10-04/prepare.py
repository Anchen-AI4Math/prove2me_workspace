"""Pure independent Matrix setup; never starts Lean or claims PASS."""
from pathlib import Path
import hashlib,json,re,subprocess,sys,ast
sys.stdout.reconfigure(encoding='utf-8')
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[1];ROOT=TASK.parents[1];PROJECT=TASK/'.rt/mi1'
AUTHOR=TASK/'verification/formalization-coefficient-map-matrix-2026-10-04'
KERNEL=TASK/'verification/formalization-coefficient-map-kernel-bridge-independent-2026-10-04/independent-review.json'
KERNEL_SHA='7a325b3866719750c31e66469399ab85f7c73d8c5c1376356ee1951b320d78b1'
REV='0df444a360eaa60ab8c11dca51a86af692955474'
NAMES=['CoefficientMap','CoefficientMapJet','CoefficientMapInjectivity','CoefficientMapPartialFractions','CoefficientMapReflection',
 'CoefficientMapFiniteSum','CoefficientMapSummation','CoefficientMapAggregate','CoefficientMapShiftDegree','CoefficientMapTelescoper','CoefficientMapKernelBridge']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,s):p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(s if isinstance(s,bytes) else s.encode('utf-8'))
def dump(p,d):write(p,json.dumps(d,ensure_ascii=False,indent=2)+'\n')
def binding(p):return {'root_relative':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p)}
def main():
 assert sha(KERNEL)==KERNEL_SHA
 kd=json.loads(KERNEL.read_text(encoding='utf-8'));assert kd['verdict']=='PASS' and len(kd['checks'])==22 and len(kd['stable_files'])==296
 frozen={r['root_relative']:r for r in kd['stable_files']}
 for r in frozen.values():
  p=ROOT/r['root_relative'];assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
 assert not PROJECT.exists(),'Do not reset or reuse any earlier Matrix project/cache'
 sources=[]
 for n in NAMES:
  p=TASK/'formalization'/(n+'.lean');r=frozen[p.relative_to(ROOT).as_posix()];assert sha(p)==r['sha256'];sources.append(binding(p))
 hs=ROOT/'Definitions/Def_ZetaNine_HarmonicStability.lean';assert sha(hs)==frozen[hs.relative_to(ROOT).as_posix()]['sha256'];sources.append(binding(hs))
 matrix=TASK/'formalization/CoefficientMapMatrix.lean';sources.append(binding(matrix));assert len(sources)==13
 observed=sha(matrix);write(OUT/'candidate-observed.lean',matrix.read_bytes())
 names={x['root_relative'].removesuffix('.lean').replace('/','.') for x in sources}
 for r in sources:
  p=ROOT/r['root_relative'];imports=re.findall(r'^import (\S+)',p.read_text(encoding='utf-8-sig'),re.M)
  assert all(m.startswith('Mathlib.') or m in names for m in imports)
  write(PROJECT/r['root_relative'],p.read_bytes())
 lake='import Lake\nopen Lake DSL\npackage zeta9MatrixIndependent where\n  buildDir := "b"\n'
 lake+='require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "'+REV+'"\n'
 lake+='lean_lib Native where\n  roots := #[`missions.zeta9.formalization.CoefficientMapMatrix]\n  globs := #[.submodules `missions.zeta9.formalization]\nlean_lib Definitions\n'
 write(PROJECT/'lakefile.lean',lake)
 for n in ['lean-toolchain','lake-manifest.json']:write(PROJECT/n,(ROOT/n).read_bytes())
 (PROJECT/'.lake').mkdir()
 result=subprocess.run(['cmd','/c','mklink','/J',str(PROJECT/'.lake/packages'),str(ROOT/'.lake/packages')],capture_output=True)
 write(OUT/'package-junction-preparation.log',result.stdout+result.stderr);assert result.returncode==0
 assert (PROJECT/'.lake/packages').is_junction() and (PROJECT/'.lake/packages').resolve()==(ROOT/'.lake/packages').resolve()
 controls=[]
 for n in ['expected-types.lean','independent-boundary.lean']:
  write(PROJECT/n,(OUT/n).read_bytes());controls.append(binding(OUT/n))
 for original,dest in [('type-audit.lean','author-type-audit.lean'),('endpoint-audit.lean','author-endpoint-audit.lean')]:
  write(PROJECT/dest,(AUTHOR/original).read_bytes());controls.append(binding(AUTHOR/original))
 text=matrix.read_text(encoding='utf-8-sig');decl=re.findall(r'^(def|theorem)\s+(\w+)',text,re.M);assert len(decl)==22 and sum(k=='def' for k,n in decl)==5
 # This textual inventory only prepares the actual environment audit. Future Lean
 # outputs, kinds, full values, type expressions and axioms govern the verdict.
 code='import missions.zeta9.formalization.CoefficientMapMatrix\nimport Lean\nopen Lean Meta\nset_option pp.fullNames true\nset_option pp.proofs true\nrun_meta do\n  for name in ['+', '.join('`ZetaNine.CoefficientMapMatrix.'+n for k,n in decl)+'] do\n'
 code+='''    let ci ← getConstInfo name
    let typ ← ppExpr ci.type
    let axs ← collectAxioms name
    let value := match ci with | .defnInfo d => some d.value | _ => none
    let kind := match ci with | .defnInfo _ => "def" | .thmInfo _ => "theorem" | _ => "other"
    IO.println (Json.mkObj [("declaration",Json.str name.toString),("kind",Json.str kind),
      ("full_type_expression_repr",Json.str (reprStr ci.type)),("type_pp_diagnostic",Json.str typ.pretty),
      ("full_definition_value_expression_repr",value.map (fun x => Json.str (reprStr x)) |>.getD Json.null),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
'''
 write(OUT/'source-full-audit.lean',code);write(PROJECT/'source-full-audit.lean',code)
 expected=(OUT/'expected-types.lean').read_text(encoding='utf-8');bound=(OUT/'independent-boundary.lean').read_text(encoding='utf-8')
 assert len(re.findall(r'^theorem ',expected,re.M))==22 and len(re.findall(r'^theorem ',bound,re.M))==26
 code=expected+'\nrun_meta do\n  for (original, expectedName) in ['+', '.join('(`ZetaNine.CoefficientMapMatrix.'+n+', `IndependentMatrixExpected.expected_'+n+')' for k,n in decl if k=='theorem')+'] do\n'
 code+='''    let a ← getConstInfo original
    let b ← getConstInfo expectedName
    let equal ← isDefEq a.type b.type
    unless equal do throwError "Actual Matrix and independent expected complete type differ: {original}"
    IO.println (Json.mkObj [("kind",Json.str "actual_whole_type_kernel_comparison"),
      ("source",Json.str original.toString),("expected",Json.str expectedName.toString),
      ("type_kernel_equal",toJson equal),("actual_full_type_expression",Json.str (reprStr a.type)),
      ("expected_full_type_expression",Json.str (reprStr b.type))]).compress
'''
 write(OUT/'kernel-types.lean',code);write(PROJECT/'kernel-types.lean',code)
 modules=['Definitions.Def_ZetaNine_HarmonicStability']+['missions.zeta9.formalization.'+n for n in NAMES]+['missions.zeta9.formalization.CoefficientMapMatrix']
 code='import Lean\nopen Lean\ndef main : IO Unit := do\n  let path ← IO.getEnv "LEAN_PATH"\n  IO.println ((Json.mkObj [("kind",Json.str "actual_search_path"),("LEAN_PATH",Json.str (path.getD ""))]).compress)\n  for m in (['+','.join(json.dumps(m) for m in modules)+'] : List String) do\n    let p ← Lean.findOLean ((m.splitOn ".").foldl Name.str Name.anonymous)\n    IO.println ((Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str m),("resolved_olean",Json.str p.toString)]).compress)\n'
 write(OUT/'resolver.lean',code);write(PROJECT/'resolver.lean',code)
 guards=[]
 for m in modules:
  obj=PROJECT/'b/lib/lean'/(m.replace('.','/')+'.olean');guards.append({'module':m,'path_plus64':len(str(obj))+64,'pass':len(str(obj))+64<=259})
 assert all(r['pass'] for r in guards) and not(PROJECT/'b').exists()
 for p in OUT.glob('*.py'):ast.parse(p.read_text(encoding='utf-8'))
 dump(OUT/'preparation-state.json',{'status':'PURE_PREPARATION_WAIT_FINAL_AUTHOR_FREEZE_AND_LANE','Lean_Lake_invocations':0,'verdict':None,
  'observed_candidate_sha256':observed,'final_source_hash_pending_author_freeze':True,'source_bindings':sources,'dependency_review':binding(KERNEL),
  'fresh_project':str(PROJECT),'cache_absent':True,'path_guards':guards,'only_pinned_Mathlib_package_cache_shared':True,
  'author_or_independent_native_objects_borrowed':False,'Root_API_credentials_scope_writes':False,
  'controls':controls,'source_records_prepared':22,'definition_full_values_prepared':5,'source_theorem_records_prepared':17,
  'expected_closed_type_and_whole_value_proofs_prepared':22,'actual_kernel_type_comparisons_prepared':17,'own_boundaries_prepared':26,
  'author_endpoint_replay_records_prepared':12,'actual_module_resolutions_prepared':13,'counts_are_prepared_only':True,
  'scope':'Original rational quartic F, monomial rows/output columns, Even n>=2 determinant and inverse; rational multiplier for integer outputs; genuine exactL/HasSum/norm summability. No integral W, height/content or irrationality proof.',
  'Lean_execution_gate':['explicit parent frozen final author source0/audits0/report hash','verify all stable current author and actual source bytes','explicit parent lane release','initial independent b absent; fresh all13 real sources','only exact allowed package/runtime/cache search paths; actual13 own module objects','22 actual source kind/type/value/axiom records;22 expected/17kernel/26own/12author controls actual0','retain whole failed runs before repairs; only Std3; no assumptions added','final exact stable byte freeze']})
 print('Matrix pure preparation only;13 sources,22 expected,26 own,17 kernel,12 author endpoint,13 resolver; sourceSHA',observed,'max path+64',max(r['path_plus64'] for r in guards),'no Lean')
if __name__=='__main__':main()
