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
REV="0df444a360eaa60ab8c11dca51a86af692955474"
NS="ZetaNine.CoefficientMapInjectivity"
EXPECTED={"CoefficientMap":"e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03","CoefficientMapJet":"e50e11c0afd2eaac1d5c58c412e5e59bc5c2068c9826063eacee8dc88fc1735a","CoefficientMapInjectivity":"ebe9b9c275a34fac348837e377e2e26246e9a762889c462420b43535e9055095"}
DEFS=["baseNumerator","baseU","weightedNumerator","polePolynomial","AllLocalCoefficientsZero","ProperMultiplier","fullLocalCoefficientMap"]
TARGETS=["all_local_coefficients_zero_implies_zero","fullLocalCoefficientMap_injective","quartic_is_proper"]
ARGS=["n W hproper hzero","n","n W hW"]
MATHLIB=["Mathlib.Algebra.Polynomial.BigOperators","Mathlib.Algebra.Polynomial.RingDivision","Mathlib.Algebra.Polynomial.Degree.Lemmas","Mathlib.RingTheory.Coprime.Lemmas"]
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

PROJECT.mkdir(parents=True,exist_ok=True)
write(PROJECT / "lakefile.lean",f'''import Lake
open Lake DSL
package zeta9InjectivityOfflineAuthor
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "{REV}"
lean_lib Native where
  roots := #[`missions.zeta9.formalization.CoefficientMapInjectivity]
  globs := #[.one `missions.zeta9.formalization.CoefficientMap, .one `missions.zeta9.formalization.CoefficientMapJet, .one `missions.zeta9.formalization.CoefficientMapInjectivity]
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
for batch,name in [(BASE,"CoefficientMap"),(JET,"CoefficientMapJet")]:
    rel="Definitions/Def_ZetaNine_"+name+".lean"
    write(PROJECT / rel,(batch / "staged" / rel).read_bytes())
    existing_defs.append({"root_relative":rel,"sha256":sha(batch / "staged" / rel),"task_relative":(batch / "staged" / rel).relative_to(TASK).as_posix()})

g=(JET / "extract_decl_graph.lean").read_text(encoding="utf-8-sig")
g=g.replace("import missions.zeta9.formalization.CoefficientMapJet","import missions.zeta9.formalization.CoefficientMapInjectivity")
g=g.replace("missions/zeta9/formalization/platform/coefficient-map-jet/decl_graph.jsonl","../decl_graph.jsonl")
write(OUT / "extract_decl_graph.lean",g);write(PROJECT / "extract_decl_graph.lean",g)
s=(JET / "extract_sketch_info.lean").read_text(encoding="utf-8-sig")
old="missions/zeta9/formalization/platform/coefficient-map-jet/oracle-input.lean"
assert s.count(old)==1
for name in EXPECTED:
    snapshot="oracle-input.lean" if name.endswith("Injectivity") else name+"-oracle-input.lean"
    code=s.replace(old,"../"+snapshot)
    write(OUT / ("extract_"+name+"_sketch.lean"),code);write(PROJECT / ("extract_"+name+"_sketch.lean"),code)
write(OUT / "extract_header.lean",(JET / "extract_header.lean").read_bytes());write(PROJECT / "extract_header.lean",(JET / "extract_header.lean").read_bytes())
run("toolchain",["lake","env","lean","--version"])
run("build-native",["lake","--no-cache","build","missions.zeta9.formalization.CoefficientMapInjectivity"])
run("stage1-extract",["lake","env","lean","extract_decl_graph.lean"])
for name in EXPECTED:
    facts="sketch_info.jsonl" if name.endswith("Injectivity") else name+"-sketch_info.jsonl"
    run("stage2-"+name,["lake","env","lean","--run","extract_"+name+"_sketch.lean","missions/zeta9/formalization/"+name+".lean","ZetaNine"],facts)
run("stage2-header",["lake","env","lean","--run","extract_header.lean","missions/zeta9/formalization/CoefficientMapInjectivity.lean"],"header_info.jsonl")

sources={n:(OUT / ("oracle-input.lean" if n.endswith("Injectivity") else n+"-oracle-input.lean")).read_bytes() for n in EXPECTED}
for n in EXPECTED:assert sources[n]==(TASK / ("formalization/"+n+".lean")).read_bytes()
source=sources["CoefficientMapInjectivity"]
graph=rows(OUT / "decl_graph.jsonl");byname={g["name"]:g for g in graph}
facts={n:rows(OUT / ("sketch_info.jsonl" if n.endswith("Injectivity") else n+"-sketch_info.jsonl")) for n in EXPECTED}
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
core=[g for g in graph if g["module"].endswith(".CoefficientMapInjectivity") and g["startLine"]>0]
assert len(core)==25 and sum(g["kind"]=="def" for g in core)==7 and sum(g["kind"]=="theorem" for g in core)==18
reached=closure([g["name"] for g in core]+[g["name"] for g in graph if g["isInstance"]])
bridge="";bridge_facts=[];helper_names=[]
for module in ["CoefficientMap","CoefficientMapJet"]:
    hs=sorted([byname[n] for n in reached if byname[n]["module"].endswith("."+module) and byname[n]["kind"]=="theorem" and byname[n]["startLine"]>0],key=lambda g:g["startLine"])
    if not hs:continue
    bridge+="open scoped BigOperators\nopen Finset Polynomial\n\nnamespace ZetaNine."+module+"\n\n"
    for g in hs:
        f=declaration(g["name"]);bridge_facts.append({"module":module,"name":g["name"],"fact":f});helper_names.append(g["name"])
        bridge+=sources[module][f["declStart"]["offset"]:f["declEnd"]["offset"]].decode()+"\n\n"
    bridge+="end ZetaNine."+module+"\n\n"
write(OUT / "actual-proof-bridge.lean.inc",bridge)
def_facts=[declaration(NS+"."+n) for n in DEFS]
defpath="Definitions/Def_ZetaNine_CoefficientMapInjectivity.lean"
definition="import Definitions.Def_ZetaNine_CoefficientMapJet\n"+"\n".join("import "+m for m in MATHLIB)+"\n\nset_option autoImplicit false\nnoncomputable section\nopen scoped BigOperators\nopen Finset Polynomial\n\nnamespace "+NS+"\n\n"
definition+="\n\n".join(source[f["declStart"]["offset"]:f["declEnd"]["offset"]].decode() for f in def_facts)+"\n\nend "+NS+"\n"
write(OUT / "staged" / defpath,definition);write(PROJECT / defpath,definition)
header=rows(OUT / "header_info.jsonl")[0];he=header["end"]["offset"]
assert header["start"]["offset"]==0 and source[:he].decode().strip().splitlines()==["import missions.zeta9.formalization.CoefficientMapJet"]+["import "+m for m in MATHLIB]
fs=facts["CoefficientMapInjectivity"];refs=[f for f in fs if f["kind"]=="ref"]
diagnostics=[f for f in fs if f["kind"]=="command" and f["syntaxKind"]=="Lean.Parser.Command.printAxioms"]
cuts=[(f["declStart"]["offset"],f["declEnd"]["offset"],b"") for f in def_facts]+[(f["span"]["start"]["offset"],f["span"]["end"]["offset"],b"") for f in diagnostics]+[(0,he,b"")]
preamble="import Definitions.Def_ZetaNine_CoefficientMapInjectivity\n\nset_option autoImplicit false\nopen scoped BigOperators\nopen Finset Polynomial\nopen "+NS+"\n"
solheader="import Definitions.Def_ZetaNine_CoefficientMapInjectivity\nimport Mathlib.Tactic\n"+"\n".join("import "+m for m in MATHLIB)+"\n\n"+bridge
origin="Zeta(9) finite proper-domain local coefficient-array research: missions/zeta9/research/coefficient-map-injectivity-2026-10-03.md. Frozen actual Lean source missions/zeta9/formalization/CoefficientMapInjectivity.lean, SHA256 "+EXPECTED["CoefficientMapInjectivity"]+"; uses genuine Base/Jet products and formal local jets. This concerns the complete (n+1) by 9 array, not the original five aggregated F outputs."
definition_nl=r"""For natural $n$ and $W\in\mathbb Q[X]$, set $N_n(t)=n!^7\prod_{i=1}^{n}(t-i)(t+n+i)$, $U_n(t)=t(t+n)$, $P^W_n=N_n\,W(U_n)$ and $Q_n=\prod_{j=0}^{n}(X+j)$. Let $c^W_{n,j,s}$ be the actual formal-jet coefficients imported from the genuine shifted-product quotient. Define the all-zero condition by $c^W_{n,j,s}=0$ for every $0\le j\le n$ and $1\le s\le9$. Define the strict proper domain by $2n+2\deg W<9(n+1)$, using natural degree (degree zero for the zero polynomial). The full local coefficient map sends $W$ to all $(n+1)\cdot9$ such rational coefficients, indexed by these poles and orders. These seven definitions use the actual numerator and formal coefficients, never an assumed array. The strict degree domain gives at most order $1/t$ decay; it does not impose stronger decay or the vanishing of a simple pole at $n=0$."""
dump(OUT / "definitions-request.json",[{"definition_name":"ZetaNine_CoefficientMapInjectivity","definition_title":"Actual proper-domain full local coefficient array","definition":definition,"natural_language_statement":definition_nl,"source":origin,"tags":["number-theory","polynomials","formal-power-series","injectivity"],"env":REV,"private":False}])
titles=["Zero actual local coefficients force a proper multiplier to vanish","Injectivity of the full actual local coefficient array on the proper domain","Every rational quartic multiplier lies in the strict proper domain"]
naturals=[r"""Let $n\ge0$ be natural and $W\in\mathbb Q[X]$. Assume $2n+2\deg W<9(n+1)$. Take the actual coefficients $c^W_{n,j,s}=[z^{9-s}](N_{n,j}(D_{n,j}^{9})^{-1}W((z-j)(z-j+n)))$ in $\mathbb Q[[z]]$, where $N_{n,j}$ and $D_{n,j}$ are the genuine shifted numerator and erased pole-factor denominator. If $c^W_{n,j,s}=0$ for every $0\le j\le n$ and $1\le s\le9$, then $$W=0.$$ This is the zero-kernel criterion for the complete actual local array in the strict proper domain. It does not concern only five aggregated zeta/constant outputs or assert their injectivity.""",r"""For every natural $n$, restrict rational polynomials $W$ to $2n+2\deg W<9(n+1)$ and send them to the complete array of actual formal-jet coefficients $$(c^W_{n,j,s})_{0\le j\le n,\ 1\le s\le9}.$$ This map is injective: two multipliers in that domain with identical complete arrays are equal. Every coefficient is taken from the genuine shifted-product formal quotient, not abstract data. No surjectivity, inverse of the original five-dimensional aggregate F, or exact infinite L-sum is claimed.""",r"""For every natural $n$, including zero, and every $W\in\mathbb Q[X]$ with natural degree at most four, $$2n+2\deg W<9(n+1).$$ Thus every rational quartic multiplier satisfies the strict proper-degree condition for the complete local-array injectivity result. Strict properness gives only at most order $1/t$ decay, without analytic summability or stronger asymptotic cancellation. At $n=0$, $W=X^4$ meets this condition and the actual weighted rational function is $1/t$ on its regular domain, so a simple pole remains possible."""]
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
    solution=solheader+"\n"+edit(source,cuts+renames).decode()+"\n\nopen "+NS+"\n\ntheorem solution"+sig+":= by\n  exact "+NS+".checked_"+n+" "+ARGS[i]+"\n\n#print axioms solution\n"
    fe=[(bs-a,be-a,full.encode())]
    if d["docstring"]:
        ds=d["docstring"];fe.append((ds["start"]["offset"]-a,ds["end"]["offset"]-a,b""))
    formal=edit(source[a:v],fe).decode().strip()+":= by sorry"
    solpath="Solutions/Sol_ZetaNine_CoefficientMapInjectivity_"+n+".lean";refpath="Theorems/Thm_ZetaNine_CoefficientMapInjectivity_"+n+".lean"
    reference=preamble+"\n"+formal+"\n"
    for rel,text in [(solpath,solution),(refpath,reference)]:write(OUT / "staged" / rel,text);write(PROJECT / rel,text)
    problems.append({"theorem_name":full,"theorem_title":titles[i],"formal_statement":formal,"natural_language_statement":naturals[i],"preamble":preamble,"source":origin+f" Original declaration lines {d['declStart']['line']}–{d['declEnd']['line']}.","tags":["number-theory","polynomials","injectivity","formalization"]})
    targets.append({"theorem_name":full,"local_solution":solpath,"local_reference":refpath,"wrapper_arguments":ARGS[i]})
    provtargets[full]={"declaration_fact":d,"binding_fact":bindings[0],"target_refs":rs,"rename_spans":[[x,y] for x,y,_ in renames],"original_signature":sig,"extra_hypotheses":[],"solution_sha256":digest(solution.encode()),"reference_sha256":digest(reference.encode())}
dump(OUT / "problems-request.json",{"env":REV,"private":False,"problems":problems})
dump(OUT / "target-plan.json",{"definition":"ZetaNine_CoefficientMapInjectivity","local_definition":defpath,"targets":targets,"existing_definitions":existing_defs})
dump(OUT / "integration-provenance.json",{"sources_sha256":EXPECTED,"actual_source_position_authority":"Actually executed official cross-module declaration metaprogram, all three actual Lean parser/ref oracles and Parser.parseHeader; no regex mathematical source-position queries.","graph_records":len(graph),"source_declarations":len(core),"source_defs":7,"source_proofs":18,"generated_records":[g for g in graph if g["module"].endswith(".CoefficientMapInjectivity") and g["startLine"]==0],"source_fact_counts":{k:sum(f["kind"]==k for f in fs) for k in ["decl","ref","command"]},"header":header,"definition_facts":def_facts,"cross_module_core_closure":sorted(reached),"inline_helper_names":helper_names,"inline_helper_facts":bridge_facts,"bridge_sha256":digest(bridge.encode()),"deleted_diagnostic_facts":diagnostics,"targets":provtargets,"new_external_theorem_boundaries":[]})

template=(JET / "types_original.lean").read_text(encoding="utf-8-sig").split('  emit "')[0]
all_defs=[g["name"] for g in graph if g["kind"]=="def" and g["startLine"]>0]
assert len(all_defs)==25
def report(filename,module,names):
    code=template.replace("import missions.zeta9.formalization.CoefficientMapJet","import "+module)+"".join(f'  emit "{label}" `{name}\n' for label,name in names)
    write(OUT / filename,code);write(PROJECT / filename,code)
report("types_original.lean","missions.zeta9.formalization.CoefficientMapInjectivity",[(n,n) for n in all_defs+[NS+"."+t for t in TARGETS]])
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
print(json.dumps({"complete":True,"observed_runs":len(receipt['rows']),"source_declarations":25,"actual_defs":7,"original_proofs":18,"cross_module_helpers":helper_names},ensure_ascii=False),flush=True)
