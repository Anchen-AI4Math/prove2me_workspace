"""Actual Lean oracle-driven offline author batch; writes only under this batch."""
from pathlib import Path
import hashlib,json,os,subprocess,sys
sys.stdout.reconfigure(encoding="utf-8")
OUT=Path(__file__).resolve().parent
TASK=OUT.parents[2]
ROOT=TASK.parents[1]
PROJECT=OUT / "project"
BASE=TASK / "formalization/platform/coefficient-map"
JET=TASK / "formalization/platform/coefficient-map-jet"
INJ=TASK / "formalization/platform/coefficient-map-injectivity"
PF=TASK / "formalization/platform/coefficient-map-partial-fractions"
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


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def digest(b):return hashlib.sha256(b).hexdigest()
def write(p,s):
    p.parent.mkdir(parents=True,exist_ok=True)
    p.write_bytes(s if isinstance(s,bytes) else s.encode("utf-8"))
def dump(p,d):write(p,json.dumps(d,ensure_ascii=False,indent=2)+"\n")
def rows(p):return [json.loads(s) for s in p.read_text(encoding="utf-8-sig").splitlines() if s.startswith("{")]
def edit(data,edits):
    edge=len(data)
    for a,b,v in sorted(set(edits),reverse=True):
        assert 0<=a<=b<=edge
        data=data[:a]+v+data[b:];edge=a
    return data
env=os.environ.copy();env.pop("LEAN_PATH",None)
receipt={"role":"author offline batch","source_sha256":EXPECTED,"root_writes":False,"API_calls":False,"rows":[]}
def run(label,args,stdout_file=None):
    p=subprocess.run(args,cwd=PROJECT,env=env,capture_output=True)
    log=OUT / (label+".log");write(log,p.stdout+p.stderr);write(OUT / (label+"-exit.txt"),str(p.returncode)+"\n")
    if stdout_file:write(OUT / stdout_file,p.stdout);write(OUT / (label+"-stderr.log"),p.stderr)
    receipt["rows"].append({"label":label,"command":args,"working_directory":str(PROJECT),"exit_code":p.returncode,"log":log.name,"log_sha256":sha(log)})
    dump(OUT / "compile-receipt.json",receipt)
    print(label+": exit "+str(p.returncode),flush=True)
    for n,h in EXPECTED.items():assert sha(TASK / ("formalization/"+n+".lean"))==h
    if p.returncode:print(log.read_text(encoding="utf-8-sig"),flush=True)
    assert p.returncode==0

math_review=TASK/"verification/formalization-coefficient-map-summation-independent-2026-10-04/independent-review.json"
assert sha(math_review)=="fb0d4a09e3273fe430688521771ea582463d31cd98caf50764a7498293c040fa"
math=json.loads(math_review.read_text(encoding="utf-8-sig"));assert math["verdict"]=="PASS"
for row in math["stable_files"]:assert sha(ROOT/row["root_relative"])==row["sha256"]
author=TASK/"verification/formalization-coefficient-map-summation-2026-10-04"
assert sha(author/"compile-receipt.json")=="1fefb593daf7d350b202e3a1429c6f58c150c89e34fd985d6fc51c2f4f1c89b4"
assert sha(author/"SHA256SUMS.txt")=="3f6ba8dfe3a23dfc794ffda01a533935f6982e0a2842ee2239713fb52f66fdc8"
for line in (author/"SHA256SUMS.txt").read_text(encoding="utf-8").splitlines():
    h,path=line.split("  ",1);assert sha(TASK/path)==h
PROJECT.mkdir(parents=True,exist_ok=True)
write(PROJECT / "lakefile.lean",f'''import Lake
open Lake DSL
package zeta9SummationOfflineAuthor
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "{REV}"
lean_lib Native where
  roots := #[`missions.zeta9.formalization.CoefficientMapSummation]
  globs := #[.one `missions.zeta9.formalization.CoefficientMap, .one `missions.zeta9.formalization.CoefficientMapJet, .one `missions.zeta9.formalization.CoefficientMapInjectivity, .one `missions.zeta9.formalization.CoefficientMapPartialFractions, .one `missions.zeta9.formalization.CoefficientMapReflection, .one `missions.zeta9.formalization.CoefficientMapFiniteSum, .one `missions.zeta9.formalization.CoefficientMapSummation]
lean_lib Definitions
lean_lib Solutions
lean_lib Theorems
''')
for name in ["lake-manifest.json","lean-toolchain"]:write(PROJECT / name,(ROOT / name).read_bytes())
(PROJECT / ".lake").mkdir(exist_ok=True)
if not (PROJECT / ".lake/packages").exists():
    p=subprocess.run(["cmd","/c","mklink","/J",str(PROJECT / ".lake/packages"),str(ROOT / ".lake/packages")],capture_output=True)
    assert p.returncode==0,(p.stdout+p.stderr).decode(errors="replace")
for n,h in EXPECTED.items():
    assert sha(TASK / ("formalization/"+n+".lean"))==h
    write(PROJECT / ("missions/zeta9/formalization/"+n+".lean"),(TASK / ("formalization/"+n+".lean")).read_bytes())
existing_defs=[]
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

g=(JET / "extract_decl_graph.lean").read_text(encoding="utf-8-sig")
g=g.replace("import missions.zeta9.formalization.CoefficientMapJet","import missions.zeta9.formalization.CoefficientMapSummation")
g=g.replace("missions/zeta9/formalization/platform/coefficient-map-jet/decl_graph.jsonl","../decl_graph.jsonl")
g=g.replace("let isProj : Name → Bool := fun m => projPrefix.isPrefixOf m","let isProj : Name → Bool := fun m => projPrefix.isPrefixOf m || m == `Definitions.Def_ZetaNine_HarmonicStability")
write(OUT / "extract_decl_graph.lean",g);write(PROJECT / "extract_decl_graph.lean",g)
s=(JET / "extract_sketch_info.lean").read_text(encoding="utf-8-sig")
old="missions/zeta9/formalization/platform/coefficient-map-jet/oracle-input.lean"
assert s.count(old)==1
for name in list(EXPECTED)+[PURE_NAME]:
    snapshot="oracle-input.lean" if name.endswith("PartialFractions") else name+"-oracle-input.lean"
    code=s.replace(old,"../"+snapshot)
    write(OUT / ("extract_"+name+"_sketch.lean"),code);write(PROJECT / ("extract_"+name+"_sketch.lean"),code)
write(OUT / "extract_header.lean",(JET / "extract_header.lean").read_bytes());write(PROJECT / "extract_header.lean",(JET / "extract_header.lean").read_bytes())
if options.prepare_only:
    dump(OUT / "preparation-state.json",{"source_hashes":EXPECTED,"selected_actual_endpoints":TARGETS,"pending_finite_sum_Def_hash":not bool(options.finite_sum_definition_sha256),"native_sources_copied":7,"actual_pure_HarmonicDef_hash":PURE_HASH,"oracle_scripts_prepared":8,"Lean_executed":False,"API_calls":False,"credentials_accessed":False,"root_scope_writes":False})
    print("Mechanical preparation complete; no Lean run; await FS Def freeze and parent Lean slot.")
    sys.exit(0)

run("toolchain",["lake","env","lean","--version"])
run("build-native",["lake","--no-cache","build","missions.zeta9.formalization.CoefficientMapSummation"])
run("stage1-extract",["lake","env","lean","extract_decl_graph.lean"])
for name in list(EXPECTED)+[PURE_NAME]:
    facts="sketch_info.jsonl" if name.endswith("PartialFractions") else name+"-sketch_info.jsonl"
    run("stage2-"+name,["lake","env","lean","--run","extract_"+name+"_sketch.lean",("Definitions/"+name+".lean" if name==PURE_NAME else "missions/zeta9/formalization/"+name+".lean"),"ZetaNine"],facts)
run("stage2-header",["lake","env","lean","--run","extract_header.lean","missions/zeta9/formalization/CoefficientMapSummation.lean"],"header_info.jsonl")

sources={n:(OUT / ("oracle-input.lean" if n.endswith("PartialFractions") else n+"-oracle-input.lean")).read_bytes() for n in list(EXPECTED)+[PURE_NAME]}
for n in EXPECTED:assert sources[n]==(TASK / ("formalization/"+n+".lean")).read_bytes()
source=sources["CoefficientMapSummation"]
graph=rows(OUT / "decl_graph.jsonl");byname={g["name"]:g for g in graph}
facts={n:rows(OUT / ("sketch_info.jsonl" if n.endswith("PartialFractions") else n+"-sketch_info.jsonl")) for n in list(EXPECTED)+[PURE_NAME]}
assert not any(g["kind"]=="axiom" for g in graph)
def declaration(full):
    g=byname[full];module=g["module"].split(".")[-1]
    ds=[f for f in facts[module] if f["kind"]=="decl" and f["declStart"]["line"]<=g["startLine"]<=f["declEnd"]["line"]]
    assert g["startLine"]>0 and len(ds)==1 and ds[0]["valStart"] is not None
    return ds[0]
def closure(seed):
    reached=set();work=list(seed)
    while work:
        name=work.pop()
        if name in reached:continue
        reached.add(name);work.extend(byname[name]["typeDeps"]+byname[name]["valueDeps"])
    return reached
core=[g for g in graph if g["module"].endswith(".CoefficientMapSummation") and g["startLine"]>0]
assert len(core)==24 and sum(g["kind"]=="def" for g in core)==3 and sum(g["kind"]=="theorem" for g in core)==21
reached=closure([g["name"] for g in core]+[g["name"] for g in graph if g["isInstance"]])
bridge="";bridge_facts=[];helper_names=[];bridge_open_context=[]
for module in ["CoefficientMap","CoefficientMapJet","CoefficientMapInjectivity","CoefficientMapPartialFractions","CoefficientMapReflection","CoefficientMapFiniteSum"]:
    hs=sorted([byname[n] for n in reached if byname[n]["module"].endswith("."+module) and byname[n]["kind"]=="theorem" and byname[n]["startLine"]>0],key=lambda g:g["startLine"])
    if not hs:continue
    bridge+="open scoped BigOperators\nopen Finset Polynomial\n\nnamespace ZetaNine."+module+"\n\n"
    first=min(g["startLine"] for g in graph if g["module"].endswith("."+module) and g["startLine"]>0)
    opens=[f for f in facts[module] if f["kind"]=="command" and f["syntaxKind"]=="Lean.Parser.Command.open" and f["span"]["end"]["line"]<first]
    # Exact parser-owned open spans restore each source's namespace resolution.
    for f in opens:
        bridge+=sources[module][f["span"]["start"]["offset"]:f["span"]["end"]["offset"]].decode()+"\n"
        bridge_open_context.append({"module":module,"fact":f})
    if opens:bridge+="\n"
    for g in hs:
        f=declaration(g["name"]);bridge_facts.append({"module":module,"name":g["name"],"fact":f});helper_names.append(g["name"])
        bridge+=sources[module][f["declStart"]["offset"]:f["declEnd"]["offset"]].decode()+"\n\n"
    bridge+="end ZetaNine."+module+"\n\n"
write(OUT / "actual-proof-bridge.lean.inc",bridge)
def_facts=[declaration(NS+"."+n) for n in DEFS]
defpath="Definitions/Def_ZetaNine_CoefficientMapSummation.lean"
definition="import Definitions.Def_ZetaNine_CoefficientMapReflection\nimport Definitions.Def_ZetaNine_CoefficientMapFiniteSum\n"+"\n".join("import "+m for m in MATHLIB)+"\n\nset_option autoImplicit false\nnoncomputable section\nopen scoped BigOperators\nopen Finset Polynomial\n\nnamespace "+NS+"\n\n"
first_def=min(f["declStart"]["offset"] for f in def_facts)
definition_open_context=[f for f in facts["CoefficientMapSummation"] if f["kind"]=="command" and f["syntaxKind"]=="Lean.Parser.Command.open" and f["span"]["end"]["offset"]<first_def]
definition+="\n".join(source[f["span"]["start"]["offset"]:f["span"]["end"]["offset"]].decode() for f in definition_open_context)+"\n\n"
definition+="\n\n".join(source[f["declStart"]["offset"]:f["declEnd"]["offset"]].decode() for f in def_facts)+"\n\nend "+NS+"\n"
write(OUT / "staged" / defpath,definition);write(PROJECT / defpath,definition)
header=rows(OUT / "header_info.jsonl")[0];he=header["end"]["offset"]
assert header["start"]["offset"]==0 and source[:he].decode().strip().splitlines()==["import missions.zeta9.formalization.CoefficientMapReflection","import missions.zeta9.formalization.CoefficientMapFiniteSum"]+["import "+m for m in MATHLIB]
fs=facts["CoefficientMapSummation"];refs=[f for f in fs if f["kind"]=="ref"]
diagnostics=[f for f in fs if f["kind"]=="command" and f["syntaxKind"]=="Lean.Parser.Command.printAxioms"]
cuts=[(f["declStart"]["offset"],f["declEnd"]["offset"],b"") for f in def_facts]+[(f["span"]["start"]["offset"],f["span"]["end"]["offset"],b"") for f in diagnostics]+[(0,he,b"")]
preamble="import Definitions.Def_ZetaNine_CoefficientMapSummation\n\nset_option autoImplicit false\nopen scoped BigOperators\nopen Finset Polynomial\nopen ZetaNine "+NS+" ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapFiniteSum ZetaNine.HarmonicStability\n"
solheader="import Definitions.Def_ZetaNine_CoefficientMapSummation\nimport Mathlib.Tactic\n"+"\n".join("import "+m for m in MATHLIB)+"\n\nset_option autoImplicit false\nset_option maxHeartbeats 2000000\nnoncomputable section\n"+bridge
origin="Zeta(9) actual p9,q1,m=n,d0 infinite summation: missions/zeta9/research/coefficient-map-summation-2026-10-04.md. Frozen actual source SHA256 "+EXPECTED["CoefficientMapSummation"]+". Actual numerator/pole products, shifted unit-denominator coefficient array, finite harmonic B/rho and actual strong-domain cancellation prove absolute convergence and the actual infinite L."
definition_nl=r"""Define $z_s=\Re(\zeta(s))$ using the actual Mathlib Riemann zeta function. For the genuine weighted rational function $f_{n,W}(t)=R_n(t)W(t(t+n))$, define the actual positive sequence $a_k=f_{n,W}(k+1)$, as a real cast of its rational value. Define $L_n(W)=B_n(W)+\rho_{n,3}(W)z_3+\rho_{n,5}(W)z_5+\rho_{n,7}(W)z_7+\rho_{n,9}(W)z_9$, where $B$ and $\rho$ are the genuine finite harmonic constant and actual local coefficient totals from the finite-sum definition chain. These are three actual definitions; no convergence, summability, coefficient cancellation or zeta-series identity is assumed by defining them."""
dump(OUT / "definitions-request.json",[{"definition_name":"ZetaNine_CoefficientMapSummation","definition_title":"Actual positive weighted rational sequence and odd-zeta linear sum","definition":definition,"natural_language_statement":definition_nl,"source":origin,"tags":["number-theory","riemann-zeta","infinite-series","formalization"],"env":REV,"private":False}])
titles=["The actual positive weighted rational series is absolutely summable","The actual even-n strong-domain series has the exact odd-zeta sum","The original even-n integer-quartic weighted series has its exact infinite sum"]
naturals=[r"""For every natural $n$ and $W\in\mathbb Q[X]$ with $2n+2\operatorname{natdeg}W\le9(n+1)-2$, the genuine positive weighted sequence is absolutely summable: $\sum_{k\ge0}|f_{n,W}(k+1)|<\infty$. No Even n premise is required. The actual simple-pole coefficient total is proved zero from the stronger degree gap; its simple-pole terms are grouped into convergent differences. There is no supplied summability or cancellation hypothesis. Strict properness alone is insufficient: $n=0,W=X^4$ gives the divergent harmonic sequence.""",r"""Let $n$ be even and $W\in\mathbb Q[X]$ satisfy $2n+2\operatorname{natdeg}W\le9(n+1)-2$. Then the actual positive rational sequence has genuine HasSum to $B_n(W)+\rho_{n,3}(W)\Re\zeta(3)+\rho_{n,5}(W)\Re\zeta(5)+\rho_{n,7}(W)\Re\zeta(7)+\rho_{n,9}(W)\Re\zeta(9)$. Both summability and actual rho cancellations are proved, without additional rho/summability/zeta inputs. The specialization $n=0,W=X^3$ gives the actual zeta3 series. In contrast, $n=0,W=X^4$ is outside the strong domain: its totalized Lean tsum is0 but it has no HasSum to any real number.""",r"""For every even integer $n\ge2$ and integer polynomial $W\in\mathbb Z[X]$ with degree at most4, cast its coefficients to $\mathbb Q$ and form the original actual p9,q1,m=n,d0 weighted rational function. The genuine positive sequence has HasSum to its exact $B+\rho_3\Re\zeta(3)+\rho_5\Re\zeta(5)+\rho_7\Re\zeta(7)+\rho_9\Re\zeta(9)$ linear form. The stronger degree bound is proved from the stated quartic/even-n domain. Integer W is not a claim that every rational local coefficient or full linear form is an integer. General parameters, inverse denominator heights, a small nonzero integer-form sequence, J and irrationality are separate obligations.""" ]

targets=[];problems=[];provtargets={}
for i,n in enumerate(TARGETS):
    full=NS+"."+n;d=declaration(full);a,v=d["declStart"]["offset"],d["valStart"]["offset"]
    rs=[r for r in refs if r["const"]==full];bindings=[r for r in rs if a<=r["start"]["offset"]<v];assert len(bindings)==1
    bs,be=bindings[0]["start"]["offset"],bindings[0]["end"]["offset"];assert source[bs:be].decode()==n
    sig=source[be:v].decode();renames=[]
    for r in rs:
        x,y=r["start"]["offset"],r["end"]["offset"]
        if any(ca<=x and y<=cb for ca,cb,_ in cuts):continue
        old=source[x:y].decode();assert old in [n,full]
        renames.append((x,y,("checked_"+n if old==n else NS+".checked_"+n).encode()))
    solution=solheader+"\n"+edit(source,cuts+renames).decode()+"\n\nopen ZetaNine "+NS+" ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapFiniteSum ZetaNine.HarmonicStability\n\ntheorem solution"+sig+":= by\n  exact "+NS+".checked_"+n+" "+ARGS[i]+"\n\n#print axioms solution\n"
    fe=[(bs-a,be-a,full.encode())]
    if d["docstring"]:
        ds=d["docstring"];fe.append((ds["start"]["offset"]-a,ds["end"]["offset"]-a,b""))
    formal=edit(source[a:v],fe).decode().strip()+":= by sorry"
    solpath="Solutions/Sol_ZetaNine_CoefficientMapSummation_"+n+".lean";refpath="Theorems/Thm_ZetaNine_CoefficientMapSummation_"+n+".lean"
    reference=preamble+"\n"+formal+"\n"
    for rel,text in [(solpath,solution),(refpath,reference)]:write(OUT / "staged" / rel,text);write(PROJECT / rel,text)
    problems.append({"theorem_name":full,"theorem_title":titles[i],"formal_statement":formal,"natural_language_statement":naturals[i],"preamble":preamble,"source":origin+f" Original declaration lines {d['declStart']['line']}–{d['declEnd']['line']}.","tags":["number-theory","polynomials","partial-fractions","formalization"]})
    targets.append({"theorem_name":full,"local_solution":solpath,"local_reference":refpath,"wrapper_arguments":ARGS[i]})
    provtargets[full]={"declaration_fact":d,"binding_fact":bindings[0],"target_refs":rs,"rename_spans":[[x,y] for x,y,_ in renames],"original_signature":sig,"extra_hypotheses":[],"solution_sha256":digest(solution.encode()),"reference_sha256":digest(reference.encode())}
dump(OUT / "problems-request.json",{"env":REV,"private":False,"problems":problems})
dump(OUT / "target-plan.json",{"definition":"ZetaNine_CoefficientMapSummation","local_definition":defpath,"targets":targets,"existing_definitions":existing_defs})
dump(OUT / "integration-provenance.json",{"sources_sha256":EXPECTED,"actual_source_position_authority":"Actually executed official cross-module declaration metaprogram, all seven actual Lean source parser/ref oracles plus the actual pure Harmonic definition oracle and Parser.parseHeader; no regex mathematical source-position queries.","graph_records":len(graph),"source_declarations":len(core),"source_defs":3,"source_proofs":21,"generated_records":[g for g in graph if g["module"].endswith(".CoefficientMapSummation") and g["startLine"]==0],"source_fact_counts":{k:sum(f["kind"]==k for f in fs) for k in ["decl","ref","command"]},"header":header,"definition_facts":def_facts,"cross_module_core_closure":sorted(reached),"inline_helper_names":helper_names,"inline_helper_facts":bridge_facts,"bridge_open_context_facts":bridge_open_context,"definition_open_context_facts":definition_open_context,"bridge_sha256":digest(bridge.encode()),"deleted_diagnostic_facts":diagnostics,"targets":provtargets,"new_external_theorem_boundaries":[]})

template=(JET / "types_original.lean").read_text(encoding="utf-8-sig").split('  emit "')[0]
all_defs=[g["name"] for g in graph if g["kind"]=="def" and g["startLine"]>0]
assert len(all_defs)==43
def report(filename,module,names):
    code=template.replace("import missions.zeta9.formalization.CoefficientMapJet","import "+module)+"".join(f'  emit "{label}" `{name}\n' for label,name in names)
    write(OUT / filename,code);write(PROJECT / filename,code)
report("types_original.lean","missions.zeta9.formalization.CoefficientMapSummation",[(n,n) for n in all_defs+[NS+"."+t for t in TARGETS]])
report("types_definition.lean",defpath.removesuffix(".lean").replace("/","."),[(n,n) for n in all_defs])
for i,t in enumerate(targets):
    for kind,key,name in [("solution","local_solution","solution"),("reference","local_reference",t["theorem_name"])]:
        report(f"types_{i}_{kind}.lean",t[key].removesuffix(".lean").replace("/","."),[(n,n) for n in all_defs]+[(t["theorem_name"],name)])
    proofnames=[g["name"] for g in core if g["kind"]=="theorem"]+helper_names+["solution"]
    proofnames=[NS+".checked_"+TARGETS[i] if n==t["theorem_name"] else n for n in proofnames]
    report(f"helpers_{i}.lean",t["local_solution"].removesuffix(".lean").replace("/","."),[(n,n) for n in proofnames])
for d in existing_defs:run("build-"+d["root_relative"].split("Def_ZetaNine_")[1].removesuffix(".lean"),["lake","--no-cache","build",d["root_relative"].removesuffix(".lean").replace("/",".")])
run("build-definition",["lake","--no-cache","build",defpath.removesuffix(".lean").replace("/",".")])
for i,t in enumerate(targets):
    for kind in ["solution","reference"]:run(f"build-{i}-{kind}",["lake","--no-cache","build",t["local_"+kind].removesuffix(".lean").replace("/",".")])
for filename in ["types_original.lean","types_definition.lean"]+[f"types_{i}_{k}.lean" for i in range(3) for k in ["solution","reference"]]+[f"helpers_{i}.lean" for i in range(3)]:run(filename.removesuffix(".lean"),["lake","env","lean",filename])
receipt["complete"]=True;receipt["native_and_staged_objects_borrowed"]=False;dump(OUT / "compile-receipt.json",receipt)
print(json.dumps({"complete":True,"observed_runs":len(receipt['rows']),"source_declarations":24,"actual_defs":3,"original_proofs":21,"cross_module_helpers":helper_names},ensure_ascii=False),flush=True)
