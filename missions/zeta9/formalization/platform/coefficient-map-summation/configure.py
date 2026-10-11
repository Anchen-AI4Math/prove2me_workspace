"""Prepare the new author batch mechanically; no Lean/API/credential operation."""
from pathlib import Path
import hashlib,json
OUT=Path(__file__).resolve().parent; TASK=OUT.parents[2]
OLD=TASK/'formalization/platform/coefficient-map-reflection'
s=(OLD/'prepare_batch.py').read_text(encoding='utf-8-sig')
start=s.index('PF=TASK /'); end=s.index('\n\ndef sha',start)
s=s[:start]+'''PF=TASK / "formalization/platform/coefficient-map-partial-fractions"
REFLECT=TASK / "formalization/platform/coefficient-map-reflection"
FS=TASK / "formalization/platform/coefficient-map-finite-sum"
REV="0df444a360eaa60ab8c11dca51a86af692955474"
NS="ZetaNine.CoefficientMapSummation"
EXPECTED={"CoefficientMap":"e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03","CoefficientMapJet":"e50e11c0afd2eaac1d5c58c412e5e59bc5c2068c9826063eacee8dc88fc1735a","CoefficientMapInjectivity":"ebe9b9c275a34fac348837e377e2e26246e9a762889c462420b43535e9055095","CoefficientMapPartialFractions":"eb0b8d54cd29ddaaa9404ee26a704bb6a47e8306741c49a6bba9b7232231f61a","CoefficientMapReflection":"8fbc53b9d9c33a61e1cf8208f89cd30dd3c6793fc32aad1cad1c51286747f707","CoefficientMapFiniteSum":"b3ede123541d6c0eb306915d93f743979b1090c34bc4df332ab6e9da07033f97","CoefficientMapSummation":"c207e8fec1358e86afd61d39853a498c9758555286b7774e5f5d7809495e876d"}
DEFS=["zetaReal","exactL","actualSeries"]
TARGETS=["actualSeries_norm_summable","actualSeries_hasSum_exactL","original_integer_quartic_exact_infinite_L"]
ARGS=["n W hstrong","n hn W hstrong","n hn2 hn W hW"]
MATHLIB=["Mathlib.NumberTheory.LSeries.RiemannZeta","Mathlib.Analysis.PSeries","Mathlib.Analysis.Normed.Group.InfiniteSum","Mathlib.Analysis.Normed.Module.FiniteDimension"]
PURE_NAME="Def_ZetaNine_HarmonicStability"
PURE_HASH="5ff9d83ca177893db1eb149da985ff29b85dbe83614650a995e28066f9bd3e92"
import argparse
ap=argparse.ArgumentParser();ap.add_argument("--prepare-only",action="store_true")
ap.add_argument("--finite-sum-definition-sha256")
options=ap.parse_args()
''' + s[end:]
s=s.replace('CoefficientMapReflection','CoefficientMapSummation')
# Restore actual Reflection module keys/dependencies altered by the namespace switch.
s=s.replace('"CoefficientMapSummation":"8fbc53b9d9c33a61e1cf8208f89cd30dd3c6793fc32aad1cad1c51286747f707"','"CoefficientMapReflection":"8fbc53b9d9c33a61e1cf8208f89cd30dd3c6793fc32aad1cad1c51286747f707"')
s=s.replace('package zeta9ReflectionOfflineAuthor','package zeta9SummationOfflineAuthor')
s=s.replace('.one `missions.zeta9.formalization.CoefficientMapSummation]','.one `missions.zeta9.formalization.CoefficientMapReflection, .one `missions.zeta9.formalization.CoefficientMapFiniteSum, .one `missions.zeta9.formalization.CoefficientMapSummation]')
a=s.index('existing_defs=[]'); b=s.index('\ng=(JET /',a)
s=s[:a]+'''existing_defs=[]
for batch,name in [(BASE,"CoefficientMap"),(JET,"CoefficientMapJet"),(INJ,"CoefficientMapInjectivity"),(PF,"CoefficientMapPartialFractions"),(REFLECT,"CoefficientMapReflection"),(FS,"CoefficientMapFiniteSum")]:
    rel="Definitions/Def_ZetaNine_"+name+".lean"; staged=batch/"staged"/rel
    if name=="CoefficientMapFiniteSum" and not options.finite_sum_definition_sha256:
        assert options.prepare_only,"Await the FS author's exact frozen Def hash before any Lean or splice."
        continue
    assert staged.exists(),"Exact parent staged Def missing: "+str(staged)
    if name=="CoefficientMapFiniteSum":assert sha(staged)==options.finite_sum_definition_sha256
    if (ROOT/rel).exists():assert sha(ROOT/rel)==sha(staged),"Existing root differs from fixed parent stage."
    write(PROJECT/rel,staged.read_bytes())
    existing_defs.append({"root_relative":rel,"sha256":sha(staged),"task_relative":staged.relative_to(TASK).as_posix(),"root_exists_at_prepare":(ROOT/rel).exists()})
pure=ROOT/("Definitions/"+PURE_NAME+".lean");assert sha(pure)==PURE_HASH
snapshot=OUT/"dependencies/Definitions"/(PURE_NAME+".lean")
write(snapshot,pure.read_bytes());write(PROJECT/("Definitions/"+PURE_NAME+".lean"),pure.read_bytes())
existing_defs.append({"root_relative":"Definitions/"+PURE_NAME+".lean","sha256":PURE_HASH,"task_relative":snapshot.relative_to(TASK).as_posix(),"root_exists_at_prepare":True})
''' +s[b:]
s=s.replace('g=g.replace("missions/zeta9/formalization/platform/coefficient-map-jet/decl_graph.jsonl","../decl_graph.jsonl")','g=g.replace("missions/zeta9/formalization/platform/coefficient-map-jet/decl_graph.jsonl","../decl_graph.jsonl")\ng=g.replace("let isProj : Name → Bool := fun m => projPrefix.isPrefixOf m","let isProj : Name → Bool := fun m => projPrefix.isPrefixOf m || m == `Definitions.Def_ZetaNine_HarmonicStability")')
s=s.replace('for name in EXPECTED:\n    snapshot=','for name in list(EXPECTED)+[PURE_NAME]:\n    snapshot=')
s=s.replace('run("toolchain",','if options.prepare_only:\n    dump(OUT / "preparation-state.json",{"source_hashes":EXPECTED,"selected_actual_endpoints":TARGETS,"pending_finite_sum_Def_hash":not bool(options.finite_sum_definition_sha256),"native_sources_copied":7,"actual_pure_HarmonicDef_hash":PURE_HASH,"oracle_scripts_prepared":8,"Lean_executed":False,"API_calls":False,"credentials_accessed":False,"root_scope_writes":False})\n    print("Mechanical preparation complete; no Lean run; await FS Def freeze and parent Lean slot.")\n    sys.exit(0)\n\nrun("toolchain",')
s=s.replace('for name in EXPECTED:\n    facts=', 'for name in list(EXPECTED)+[PURE_NAME]:\n    facts=')
s=s.replace('"missions/zeta9/formalization/"+name+".lean","ZetaNine"','("Definitions/"+name+".lean" if name==PURE_NAME else "missions/zeta9/formalization/"+name+".lean"),"ZetaNine"')
s=s.replace('facts={n:rows(OUT / ("sketch_info.jsonl" if n.endswith("PartialFractions") else n+"-sketch_info.jsonl")) for n in EXPECTED}','facts={n:rows(OUT / ("sketch_info.jsonl" if n.endswith("PartialFractions") else n+"-sketch_info.jsonl")) for n in list(EXPECTED)+[PURE_NAME]}')
s=s.replace('sources={n:(OUT / ("oracle-input.lean" if n.endswith("PartialFractions") else n+"-oracle-input.lean")).read_bytes() for n in EXPECTED}','sources={n:(OUT / ("oracle-input.lean" if n.endswith("PartialFractions") else n+"-oracle-input.lean")).read_bytes() for n in list(EXPECTED)+[PURE_NAME]}')
s=s.replace('assert len(core)==34 and sum(g["kind"]=="def" for g in core)==4 and sum(g["kind"]=="theorem" for g in core)==30','assert len(core)==24 and sum(g["kind"]=="def" for g in core)==3 and sum(g["kind"]=="theorem" for g in core)==21')
s=s.replace('for module in ["CoefficientMap","CoefficientMapJet","CoefficientMapInjectivity","CoefficientMapPartialFractions"]:','for module in ["CoefficientMap","CoefficientMapJet","CoefficientMapInjectivity","CoefficientMapPartialFractions","CoefficientMapReflection","CoefficientMapFiniteSum"]:')
s=s.replace('"import Definitions.Def_ZetaNine_CoefficientMapPartialFractions\\n"','"import Definitions.Def_ZetaNine_CoefficientMapReflection\\nimport Definitions.Def_ZetaNine_CoefficientMapFiniteSum\\n"')
s=s.replace('==["import missions.zeta9.formalization.CoefficientMapPartialFractions"]+["import "+m for m in MATHLIB]','==["import missions.zeta9.formalization.CoefficientMapReflection","import missions.zeta9.formalization.CoefficientMapFiniteSum"]+["import "+m for m in MATHLIB]')
s=s.replace('"source_defs":4,"source_proofs":30','"source_defs":3,"source_proofs":21')
s=s.replace('assert len(all_defs)==34','assert len(all_defs)==43')
s=s.replace('ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions\\n','ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapFiniteSum ZetaNine.HarmonicStability\\n')
s=s.replace('all five actual Lean parser/ref oracles','all seven actual Lean source parser/ref oracles plus the actual pure Harmonic definition oracle')
s=s.replace('"\\n\\n"+bridge\norigin=', '"\\n\\nset_option autoImplicit false\\nset_option maxHeartbeats 2000000\\nnoncomputable section\\n"+bridge\norigin=')
s=s.replace('"source_declarations":34,"actual_defs":4,"original_proofs":30','"source_declarations":24,"actual_defs":3,"original_proofs":21')
s=s.replace('PROJECT.mkdir(parents=True,exist_ok=True)', '''math_review=TASK/"verification/formalization-coefficient-map-summation-independent-2026-10-04/independent-review.json"
assert sha(math_review)=="fb0d4a09e3273fe430688521771ea582463d31cd98caf50764a7498293c040fa"
math=json.loads(math_review.read_text(encoding="utf-8-sig"));assert math["verdict"]=="PASS"
for row in math["stable_files"]:assert sha(ROOT/row["root_relative"])==row["sha256"]
author=TASK/"verification/formalization-coefficient-map-summation-2026-10-04"
assert sha(author/"compile-receipt.json")=="1fefb593daf7d350b202e3a1429c6f58c150c89e34fd985d6fc51c2f4f1c89b4"
assert sha(author/"SHA256SUMS.txt")=="3f6ba8dfe3a23dfc794ffda01a533935f6982e0a2842ee2239713fb52f66fdc8"
for line in (author/"SHA256SUMS.txt").read_text(encoding="utf-8").splitlines():
    h,path=line.split("  ",1);assert sha(TASK/path)==h
PROJECT.mkdir(parents=True,exist_ok=True)''')
a=s.index('origin=');b=s.index('\ntargets=[];',a)
s=s[:a]+'''origin="Zeta(9) actual p9,q1,m=n,d0 infinite summation: missions/zeta9/research/coefficient-map-summation-2026-10-04.md. Frozen actual source SHA256 "+EXPECTED["CoefficientMapSummation"]+". Actual numerator/pole products, shifted unit-denominator coefficient array, finite harmonic B/rho and actual strong-domain cancellation prove absolute convergence and the actual infinite L."
definition_nl=r"""Define $z_s=\\Re(\\zeta(s))$ using the actual Mathlib Riemann zeta function. For the genuine weighted rational function $f_{n,W}(t)=R_n(t)W(t(t+n))$, define the actual positive sequence $a_k=f_{n,W}(k+1)$, as a real cast of its rational value. Define $L_n(W)=B_n(W)+\\rho_{n,3}(W)z_3+\\rho_{n,5}(W)z_5+\\rho_{n,7}(W)z_7+\\rho_{n,9}(W)z_9$, where $B$ and $\\rho$ are the genuine finite harmonic constant and actual local coefficient totals from the finite-sum definition chain. These are three actual definitions; no convergence, summability, coefficient cancellation or zeta-series identity is assumed by defining them."""
dump(OUT / "definitions-request.json",[{"definition_name":"ZetaNine_CoefficientMapSummation","definition_title":"Actual positive weighted rational sequence and odd-zeta linear sum","definition":definition,"natural_language_statement":definition_nl,"source":origin,"tags":["number-theory","riemann-zeta","infinite-series","formalization"],"env":REV,"private":False}])
titles=["The actual positive weighted rational series is absolutely summable","The actual even-n strong-domain series has the exact odd-zeta sum","The original even-n integer-quartic weighted series has its exact infinite sum"]
naturals=[r"""For every natural $n$ and $W\\in\\mathbb Q[X]$ with $2n+2\\operatorname{natdeg}W\\le9(n+1)-2$, the genuine positive weighted sequence is absolutely summable: $\\sum_{k\\ge0}|f_{n,W}(k+1)|<\\infty$. No Even n premise is required. The actual simple-pole coefficient total is proved zero from the stronger degree gap; its simple-pole terms are grouped into convergent differences. There is no supplied summability or cancellation hypothesis. Strict properness alone is insufficient: $n=0,W=X^4$ gives the divergent harmonic sequence.""",r"""Let $n$ be even and $W\\in\\mathbb Q[X]$ satisfy $2n+2\\operatorname{natdeg}W\\le9(n+1)-2$. Then the actual positive rational sequence has genuine HasSum to $B_n(W)+\\rho_{n,3}(W)\\Re\\zeta(3)+\\rho_{n,5}(W)\\Re\\zeta(5)+\\rho_{n,7}(W)\\Re\\zeta(7)+\\rho_{n,9}(W)\\Re\\zeta(9)$. Both summability and actual rho cancellations are proved, without additional rho/summability/zeta inputs. The specialization $n=0,W=X^3$ gives the actual zeta3 series. In contrast, $n=0,W=X^4$ is outside the strong domain: its totalized Lean tsum is0 but it has no HasSum to any real number.""",r"""For every even integer $n\\ge2$ and integer polynomial $W\\in\\mathbb Z[X]$ with degree at most4, cast its coefficients to $\\mathbb Q$ and form the original actual p9,q1,m=n,d0 weighted rational function. The genuine positive sequence has HasSum to its exact $B+\\rho_3\\Re\\zeta(3)+\\rho_5\\Re\\zeta(5)+\\rho_7\\Re\\zeta(7)+\\rho_9\\Re\\zeta(9)$ linear form. The stronger degree bound is proved from the stated quartic/even-n domain. Integer W is not a claim that every rational local coefficient or full linear form is an integer. General parameters, inverse denominator heights, a small nonzero integer-form sequence, J and irrationality are separate obligations.""" ]
''' +s[b:]
(OUT/'prepare_batch.py').write_text(s,encoding='utf-8',newline='\n')
prep={'source_sha256':'c207e8fec1358e86afd61d39853a498c9758555286b7774e5f5d7809495e876d',
 'author_receipt_sha256':'1fefb593daf7d350b202e3a1429c6f58c150c89e34fd985d6fc51c2f4f1c89b4',
 'independent_math_review_sha256':'fb0d4a09e3273fe430688521771ea582463d31cd98caf50764a7498293c040fa',
 'native_sources':7,'pure_Harmonic_definition':'5ff9d83ca177893db1eb149da985ff29b85dbe83614650a995e28066f9bd3e92',
 'selected_actual_endpoints':['actualSeries_norm_summable','actualSeries_hasSum_exactL','original_integer_quartic_exact_infinite_L'],
 'new_definitions':['zetaReal','exactL','actualSeries'],'planned_existing_Definitions':7,
 'author_writes_only_new_batch':True,'Lean_started':False,'API_calls':False,'credentials_accessed':False}
(OUT/'planned-batch.json').write_text(json.dumps(prep,indent=2)+'\n',encoding='utf-8')
print('Summation configuration written; prepare-only is available, no Lean executed.')
