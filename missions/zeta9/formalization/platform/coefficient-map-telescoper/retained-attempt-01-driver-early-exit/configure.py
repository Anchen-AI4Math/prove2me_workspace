"""Configure actual Telescoper transplantation; preparation runs no Lean."""
from pathlib import Path
import hashlib,json
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[2];SUM=TASK/'formalization/platform/coefficient-map-summation'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for line in (SUM/'SHA256SUMS.txt').read_text(encoding='utf-8').splitlines():
 h,p=line.split('  ',1);assert sha(SUM/p)==h
s=(SUM/'prepare_batch.py').read_text(encoding='utf-8')
s=s.replace('PROJECT=OUT / "project"','PROJECT=OUT / "p"\nBUILD=TASK / ".rt" / "t1" / "b"')
s=s.replace('receipt={"role":"author offline batch",','receipt={"source_project_task_relative":PROJECT.relative_to(TASK).as_posix(),"fresh_build_task_relative":BUILD.relative_to(TASK).as_posix(),"native_and_staged_objects_borrowed":False,"role":"author offline batch",')
a=s.index('PF=TASK /');b=s.index('\n\ndef sha',a)
s=s[:a]+'''PF=TASK / "formalization/platform/coefficient-map-partial-fractions"
REFLECT=TASK / "formalization/platform/coefficient-map-reflection"
FS=TASK / "formalization/platform/coefficient-map-finite-sum"
SUM=TASK / "formalization/platform/coefficient-map-summation"
AGG=TASK / "formalization/platform/coefficient-map-aggregate"
REV="0df444a360eaa60ab8c11dca51a86af692955474"
NS="ZetaNine.CoefficientMapTelescoper"
EXPECTED={"CoefficientMap":"e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03","CoefficientMapJet":"e50e11c0afd2eaac1d5c58c412e5e59bc5c2068c9826063eacee8dc88fc1735a","CoefficientMapInjectivity":"ebe9b9c275a34fac348837e377e2e26246e9a762889c462420b43535e9055095","CoefficientMapPartialFractions":"eb0b8d54cd29ddaaa9404ee26a704bb6a47e8306741c49a6bba9b7232231f61a","CoefficientMapReflection":"8fbc53b9d9c33a61e1cf8208f89cd30dd3c6793fc32aad1cad1c51286747f707","CoefficientMapFiniteSum":"b3ede123541d6c0eb306915d93f743979b1090c34bc4df332ab6e9da07033f97","CoefficientMapSummation":"c207e8fec1358e86afd61d39853a498c9758555286b7774e5f5d7809495e876d","CoefficientMapAggregate":"e538a7310f81ce9ab6c5e07d4b8bd64bb70be7a899e28f085a2c8506a4ff2299","CoefficientMapTelescoper":"8792e8ba5c6abcbdbe83b0aa4ffa1ab716fd05fac10da7275b86ab2f780fd121"}
DEFS=["prefixSum","cumulativeCoefficient","telescoper","telescoperNumerator","rootNode","rootPolynomial"]
TARGETS=["actual_weightedR_is_difference","telescoper_actual_rational_representation","actual_polynomial_quotient_degree_bound"]
ARGS=["n hn W hstrong hzero t hregular","n hn1 W t hregular","n hn1 hn W hstrong hzero"]
MATHLIB=[]
PURE_NAME="Def_ZetaNine_HarmonicStability"
PURE_HASH="5ff9d83ca177893db1eb149da985ff29b85dbe83614650a995e28066f9bd3e92"
CONTROL_MODULES=["NativeTelescoperAuthorControl","NativeTelescoperIndependentControl"]
CONTROL_FILES=["verification/formalization-coefficient-map-telescoper-2026-10-04/type-audit.lean","verification/formalization-coefficient-map-telescoper-independent-2026-10-04/independent-boundary.lean"]
import argparse
ap=argparse.ArgumentParser();ap.add_argument("--prepare-only",action="store_true")
ap.add_argument("--aggregate-definition-sha256")
options=ap.parse_args()
'''+s[b:]
# Switch only the current-module occurrences, retaining the genuine Summation parent.
current='CoefficientMapSummation'
for old,new in [('NS="ZetaNine.CoefficientMapSummation"','NS="ZetaNine.CoefficientMapTelescoper"'),
 ('formalization/CoefficientMapSummation','formalization/CoefficientMapTelescoper'),
 ('source=sources["CoefficientMapSummation"]','source=sources["CoefficientMapTelescoper"]'),
 ('facts["CoefficientMapSummation"]','facts["CoefficientMapTelescoper"]'),
 ('endswith(".CoefficientMapSummation")','endswith(".CoefficientMapTelescoper")'),
 ('Def_ZetaNine_CoefficientMapSummation','Def_ZetaNine_CoefficientMapTelescoper')]:s=s.replace(old,new)
a=s.index('math_review=');b=s.index('PROJECT.mkdir(',a)
s=s[:a]+'''math_review=TASK/"verification/formalization-coefficient-map-telescoper-independent-2026-10-04/independent-review.json"
assert sha(math_review)=="cac46e0ea0674bcd4b2dca543326ab2d9bdd3cd8a409cba8988bfea0130a556a"
math=json.loads(math_review.read_text(encoding="utf-8-sig"));assert math["verdict"]=="PASS" and len(math["checks"])==16 and len(math["stable_files"])==150
for row in math["stable_files"]:assert sha(ROOT/row["root_relative"])==row["sha256"]
author=TASK/"verification/formalization-coefficient-map-telescoper-2026-10-04"
assert sha(author/"compile-receipt.json")=="7deebfee272c749261e85381cf51262ac4c1692457e908c749bc20596884b8e4"
assert sha(author/"SHA256SUMS.txt")=="c5b4984a10080e914929f9c81073a162eced7ec6c1aecae9d777aad222055de8"
for line in (author/"SHA256SUMS.txt").read_text(encoding="utf-8").splitlines():
 h,path=line.split("  ",1);assert sha(TASK/path)==h
'''+s[b:]
a=s.index('write(PROJECT / "lakefile.lean"');b=s.index('for name in ["lake-manifest.json"',a)
s=s[:a]+'''write(PROJECT / "lakefile.lean",f\'''import Lake
open Lake DSL
package zeta9TelescoperOfflineAuthor where
  buildDir := "{BUILD.as_posix()}"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "{REV}"
lean_lib Native where
  roots := #[`missions.zeta9.formalization.CoefficientMapTelescoper]
  globs := #[{', '.join('.one `missions.zeta9.formalization.'+n for n in EXPECTED)}]
lean_lib NativeControls where
  roots := #[`NativeTelescoperAuthorControl, `NativeTelescoperIndependentControl]
  globs := #[.one `NativeTelescoperAuthorControl, .one `NativeTelescoperIndependentControl]
lean_lib Definitions
lean_lib Solutions
lean_lib Theorems
\''')
'''+s[b:]
a=s.index('existing_defs=[]');b=s.index('\npure=ROOT/',a)
s=s[:a]+'''existing_defs=[]
for batch,name in [(BASE,"CoefficientMap"),(JET,"CoefficientMapJet"),(INJ,"CoefficientMapInjectivity"),(PF,"CoefficientMapPartialFractions"),(REFLECT,"CoefficientMapReflection"),(FS,"CoefficientMapFiniteSum"),(SUM,"CoefficientMapSummation"),(AGG,"CoefficientMapAggregate")]:
 rel="Definitions/Def_ZetaNine_"+name+".lean";staged=batch/"staged"/rel
 if name=="CoefficientMapAggregate" and not options.aggregate_definition_sha256:
  assert options.prepare_only,"Await Aggregate author's exact fixed Definition before Lean."
  continue
 assert staged.exists(),"Exact genuine parent Definition missing: "+str(staged)
 if name=="CoefficientMapAggregate":assert sha(staged)==options.aggregate_definition_sha256
 if (ROOT/rel).exists():assert sha(ROOT/rel)==sha(staged),"Root differs from fixed parent staged Definition."
 write(PROJECT/rel,staged.read_bytes())
 existing_defs.append({"root_relative":rel,"sha256":sha(staged),"task_relative":staged.relative_to(TASK).as_posix(),"root_exists_at_prepare":(ROOT/rel).exists()})
control_bindings=[]
for module,rel in zip(CONTROL_MODULES,CONTROL_FILES):
 original=TASK/rel
 assert sha(original)==next(r["sha256"] for r in math["stable_files"] if r["root_relative"]==original.relative_to(ROOT).as_posix())
 write(PROJECT/(module+".lean"),original.read_bytes())
 control_bindings.append({"module":module,"task_relative":rel,"sha256":sha(original)})
'''+s[b:]
s=s.replace('import missions.zeta9.formalization.CoefficientMapSummation','import missions.zeta9.formalization.CoefficientMapTelescoper')
s=s.replace('g=g.replace("missions/zeta9/formalization/platform/coefficient-map-jet/decl_graph.jsonl","../decl_graph.jsonl")','g=g.replace("import missions.zeta9.formalization.CoefficientMapTelescoper","import missions.zeta9.formalization.CoefficientMapTelescoper\\n"+"\\n".join("import "+m for m in CONTROL_MODULES))\ng=g.replace("missions/zeta9/formalization/platform/coefficient-map-jet/decl_graph.jsonl","../decl_graph.jsonl")')
s=s.replace('m == `Definitions.Def_ZetaNine_HarmonicStability")','m == `Definitions.Def_ZetaNine_HarmonicStability || m == `NativeTelescoperAuthorControl || m == `NativeTelescoperIndependentControl")')
s=s.replace('write(OUT / "extract_decl_graph.lean",g);','g=g.replace("run_meta do\\n", "run_meta do\\n  let selectedLeanPath ← IO.getEnv \\\"LEAN_PATH\\\"\\n  IO.FS.writeFile \\\"../lean-path-selected.json\\\" ((Json.mkObj [(\\\"LEAN_PATH\\\", toJson selectedLeanPath)]).compress)\\n",1)\nwrite(OUT / "extract_decl_graph.lean",g);')
a=s.index('if options.prepare_only:');b=s.index('\nrun("toolchain"',a)
s=s[:a]+'''if options.prepare_only:
 dump(OUT/"preparation-state.json",{"sources_sha256":EXPECTED,"native_sources_copied":9,"source_project_task_relative":PROJECT.relative_to(TASK).as_posix(),"fresh_build_task_relative":BUILD.relative_to(TASK).as_posix(),"pure_HarmonicDef_sha256":PURE_HASH,"selected_actual_endpoints":TARGETS,"new_genuine_Definitions":DEFS,"fixed_control_sources":control_bindings,"await_aggregate_definition_hash":not bool(options.aggregate_definition_sha256),"Lean_executed":False,"root_scope_API_credential_writes":False,"separate_independent_transplantation_review_required":True})
 print("Mechanical Telescoper preparation complete; no Lean run; await parent Lean slot.")
sys.exit(0)
'''+s[b:]
s=s.replace('run("toolchain",','assert not BUILD.exists() or not any(BUILD.rglob("*")),"Fresh cache already populated; retain previous attempt and select a new cache."\nsubprocess.run([sys.executable,str(OUT / "check_output_paths.py")],check=True)\nrun("toolchain",',1)
s=s.replace('run("build-native",["lake","--no-cache","build","missions.zeta9.formalization.CoefficientMapSummation"])','run("build-native",["lake","--no-cache","build","missions.zeta9.formalization.CoefficientMapTelescoper"])')
s=s.replace('run("stage1-extract",','for m in CONTROL_MODULES:run("native-control-"+m,["lake","--no-cache","build",m])\nrun("stage1-extract",')
s=s.replace('assert len(core)==24 and sum(g["kind"]=="def" for g in core)==3 and sum(g["kind"]=="theorem" for g in core)==21','assert len(core)==31 and sum(g["kind"]=="def" for g in core)==6 and sum(g["kind"]=="theorem" for g in core)==25')
s=s.replace('reached=closure([g["name"] for g in core]+[g["name"] for g in graph if g["isInstance"]])','control_roots=[g["name"] for g in graph if g["module"] in CONTROL_MODULES and g["startLine"]>0]\nreached=closure([g["name"] for g in core]+control_roots+[g["name"] for g in graph if g["isInstance"]])')
s=s.replace('"CoefficientMapReflection","CoefficientMapFiniteSum"]:','"CoefficientMapReflection","CoefficientMapFiniteSum","CoefficientMapSummation","CoefficientMapAggregate"]:')
a=s.index('definition="import Definitions.');b=s.index('\nfirst_def=',a)
s=s[:a]+'definition="import Definitions.Def_ZetaNine_CoefficientMapAggregate\\n\\nset_option autoImplicit false\\nnoncomputable section\\nopen scoped BigOperators Topology\\nopen Finset Polynomial Filter\\n\\nnamespace "+NS+"\\n\\n"\n'+s[b:]
a=s.index('assert header["start"]');b=s.index('\nfs=facts[',a)
s=s[:a]+'assert header["start"]["offset"]==0 and source[:he].decode().strip().splitlines()==["import missions.zeta9.formalization.CoefficientMapAggregate"]\n'+s[b:]
a=s.index('preamble=');b=s.index('\ntargets=[];',a)
s=s[:a]+'''preamble="import Definitions.Def_ZetaNine_CoefficientMapTelescoper\\n\\nset_option autoImplicit false\\nopen scoped BigOperators Topology\\nopen Finset Polynomial Filter\\nopen ZetaNine "+NS+" ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapAggregate\\n"
solheader="import Definitions.Def_ZetaNine_CoefficientMapTelescoper\\nimport Mathlib.Tactic\\n\\nset_option autoImplicit false\\nset_option maxHeartbeats 2000000\\nnoncomputable section\\n"+bridge
origin="Zeta(9) actual cumulative telescoper and numerator root factor: missions/zeta9/research/coefficient-map-telescoper-2026-10-04.md. Frozen actual source SHA256 "+EXPECTED["CoefficientMapTelescoper"]+". Q is constructed from the genuine local coefficients. No rational-function difference or polynomial factorization is supplied as a premise."
definition_nl=r"""Define actual prefix sums of the genuine local coefficients, the cumulative coefficients, and the rational function $Q_{n,W}(t)=\\sum_{j=0}^{n-1}\\sum_{s=1}^9a_{j,s}/(t+j)^s$. Define its actual numerator $P_{n,W}$ using the genuine partial-fraction basis over $M_n(t)^9=\\prod_{k=0}^{n-1}(t+k)^9$. Define root nodes $1,\\ldots,n+1,-n,\\ldots,-2n$ and their monic product $P_{0,n}$. These are six true data definitions; no difference, root, divisibility, quotient or inverse conclusion is assumed."""
dump(OUT/"definitions-request.json",[{"definition_name":"ZetaNine_CoefficientMapTelescoper","definition_title":"Actual cumulative rational telescoper, numerator and kernel root polynomial","definition":definition,"natural_language_statement":definition_nl,"source":origin,"tags":["number-theory","polynomials","finite-differences","formalization"],"env":REV,"private":False}])
titles=["The actual weighted rational function is the cumulative telescoper difference","The actual telescoper equals its genuine numerator over the pole product","The actual zero-aggregate numerator has the full root factor and bounded quotient"]
naturals=[r"""Let natural $n$ be even and let $W\\in\\mathbb Q[X]$ satisfy the actual strong bound $2n+2\\operatorname{natdeg}W\\le9(n+1)-2$ and the genuine aggregate $F_n(W)=0$. At every rational regular point $t$ with $t+k\\ne0$ for $0\\le k\\le n$, the actual weighted rational function equals $Q_{n,W}(t)-Q_{n,W}(t+1)$. Q is the actual cumulative local-coefficient function, not an assumed telescoper. These original domain conditions are retained. Without the strong bound, $n=0,W=X^4$ has zero aggregate and empty Q but the actual weighted value at1 is1, so the difference identity fails.""",r"""For every $n\\ge1$, rational polynomial $W$ and rational $t$ regular at every $t+k$, $0\\le k<n$, the actual cumulative rational function equals $P_{n,W}(t)/M_n(t)^9$. Both the numerator and denominator are defined from the actual local coefficients and pole products. No Even n, strong bound, zero aggregate or preassigned rational identity is needed for this original endpoint.""",r"""Let $n\\ge1$ be even, and let rational $W$ satisfy the actual strong bound and genuine $F_n(W)=0$. There exists rational polynomial $H$ such that the actual numerator $P_{n,W}=P_{0,n}H$ and $\\operatorname{natdeg}H\\le7n-3$. The actual $P_{0,n}$ has $2n+2$ distinct nodes $1,\\ldots,n+1,-n,\\ldots,-2n$. Their vanishing and divisibility are proved from the actual telescoper, regular nodes and finite/infinite sum identities; they are not extra assumptions. The zero-numerator case is included. Kernel triviality, inverse bounds and irrationality are separate results.""" ]
'''+s[b:]
s=s.replace('ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapFiniteSum ZetaNine.HarmonicStability\\n','ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapFiniteSum ZetaNine.CoefficientMapSummation ZetaNine.CoefficientMapAggregate ZetaNine.HarmonicStability\\n')
s=s.replace('"source_defs":3,"source_proofs":21','"source_defs":6,"source_proofs":25').replace('"source_declarations":24,"actual_defs":3,"original_proofs":21','"source_declarations":31,"actual_defs":6,"original_proofs":25')
s=s.replace('assert len(all_defs)==43','assert len(all_defs)==55')
s=s.replace('report("types_original.lean","missions.zeta9.formalization.CoefficientMapSummation",','report("types_original.lean","missions.zeta9.formalization.CoefficientMapTelescoper",')
s=s.replace('"definition":"ZetaNine_CoefficientMapSummation"','"definition":"ZetaNine_CoefficientMapTelescoper"')
s=s.replace('Sol_ZetaNine_CoefficientMapSummation_','Sol_ZetaNine_CoefficientMapTelescoper_').replace('Thm_ZetaNine_CoefficientMapSummation_','Thm_ZetaNine_CoefficientMapTelescoper_')
s=s.replace('all seven actual Lean source parser/ref oracles plus the actual pure Harmonic definition oracle','all nine actual native source parser/ref oracles plus the genuine pure Harmonic definition oracle')
s=s.replace('"cross_module_core_closure":sorted(reached),','"cross_module_core_closure":sorted(reached),"native_closed_control_bindings":control_bindings,"native_closed_control_roots":control_roots,')
s=s.replace('receipt["complete"]=True;','receipt["fresh_main_cache_bindings"]=[{"task_relative":p.relative_to(TASK).as_posix(),"sha256":sha(p),"bytes":p.stat().st_size} for p in sorted(BUILD.rglob("*")) if p.is_file()]\nreceipt["complete"]=True;')
s=s.replace('["number-theory","polynomials","partial-fractions","formalization"]','["number-theory","polynomials","finite-differences","formalization"]')
(OUT/'prepare_batch.py').write_text(s,encoding='utf-8',newline='\n');compile(s,str(OUT/'prepare_batch.py'),'exec')
b=(TASK/'formalization/platform/coefficient-map-shift-degree/prepare_boundaries.py').read_text(encoding='utf-8')
b=b.replace('22 native author and 17 independent','35 native author and 54 independent').replace('coefficient-map-shift-degree','coefficient-map-telescoper')
b=b.replace('d38de9f7991fedbd716bd2b1824cda09f979c1da91191bff43e8f0ea3922e5df','cac46e0ea0674bcd4b2dca543326ab2d9bdd3cd8a409cba8988bfea0130a556a')
b=b.replace('CoefficientMapShiftDegree','CoefficientMapTelescoper').replace('actual_shift_difference_small_degree_implies_zero','actual_polynomial_quotient_degree_bound')
b=b.replace("PROJECT=OUT/'project'","PROJECT=OUT/'p'")
b=b.replace("type-audit.lean',22","type-audit.lean',35").replace("independent-boundary-audit.lean',17","independent-boundary.lean',54")
b=b.replace('selected low-degree theorem name','selected quotient-degree theorem name').replace("'records':39","'records':89")
(OUT/'prepare_boundaries.py').write_text(b,encoding='utf-8',newline='\n');compile(b,str(OUT/'prepare_boundaries.py'),'exec')
print('Telescoper driver configured; no Lean executed.')
