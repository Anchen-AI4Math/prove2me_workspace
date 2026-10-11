"""Actual Lean oracle-driven offline author batch; writes only under this batch."""
from pathlib import Path
import hashlib,json,os,subprocess,sys
sys.stdout.reconfigure(encoding="utf-8")
OUT=Path(__file__).resolve().parent
TASK=OUT.parents[2]
ROOT=TASK.parents[1]
PROJECT=OUT / "project"
JET=TASK / "formalization/platform/coefficient-map-jet"
REV="0df444a360eaa60ab8c11dca51a86af692955474"
NS="ZetaNine.CoefficientMapShiftDegree"
EXPECTED={"CoefficientMapShiftDegree":"96efe64f218c07a9d941136af1b4a0874bca9627c01be262c53e4445e0876953"}
DEFS=["shiftA","shiftB","shiftDifference"]
TARGETS=["actual_shift_difference_coefficient","actual_shift_difference_degree_lower_bound","actual_shift_difference_small_degree_implies_zero"]
ARGS=["n H hH","n hn H hH hdeg","n hn H hdeg hsmall"]
MATHLIB=["Mathlib.Algebra.Polynomial.Taylor","Mathlib.Algebra.Polynomial.Reverse","Mathlib.Tactic"]
import argparse
ap=argparse.ArgumentParser();ap.add_argument("--prepare-only",action="store_true")
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

math_review=TASK/"verification/formalization-coefficient-map-shift-degree-independent-2026-10-04/independent-review.json"
assert sha(math_review)=="d38de9f7991fedbd716bd2b1824cda09f979c1da91191bff43e8f0ea3922e5df"
math=json.loads(math_review.read_text(encoding="utf-8-sig"));assert math["verdict"]=="PASS" and len(math["checks"])==16 and len(math["stable_files"])==54
for row in math["stable_files"]:assert sha(ROOT/row["root_relative"])==row["sha256"]
author=TASK/"verification/formalization-coefficient-map-shift-degree-2026-10-04"
assert sha(author/"compile-receipt.json")=="93595416db563dd9cd8ffb5030455eed1edfe678b392ec64b1bd4930fdb7f853"
assert sha(author/"SHA256SUMS.txt")=="88f22efde6ad2e4552c878e55ca09f5247f9ab4ffa567c7d5edc91036808f4c5"
for line in (author/"SHA256SUMS.txt").read_text(encoding="utf-8").splitlines():
 h,path=line.split("  ",1);assert sha(ROOT/path)==h
PROJECT.mkdir(parents=True,exist_ok=True)
write(PROJECT / "lakefile.lean",f'''import Lake
open Lake DSL
package zeta9ShiftDegreeOfflineAuthor
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "{REV}"
lean_lib Native where
  roots := #[`missions.zeta9.formalization.CoefficientMapShiftDegree]
  globs := #[.one `missions.zeta9.formalization.CoefficientMapShiftDegree]
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

g=(JET / "extract_decl_graph.lean").read_text(encoding="utf-8-sig")
g=g.replace("import missions.zeta9.formalization.CoefficientMapJet","import missions.zeta9.formalization.CoefficientMapShiftDegree")
g=g.replace("missions/zeta9/formalization/platform/coefficient-map-jet/decl_graph.jsonl","../decl_graph.jsonl")
write(OUT / "extract_decl_graph.lean",g);write(PROJECT / "extract_decl_graph.lean",g)
s=(JET / "extract_sketch_info.lean").read_text(encoding="utf-8-sig")
old="missions/zeta9/formalization/platform/coefficient-map-jet/oracle-input.lean"
assert s.count(old)==1
for name in list(EXPECTED):
    snapshot="oracle-input.lean" if name.endswith("PartialFractions") else name+"-oracle-input.lean"
    code=s.replace(old,"../"+snapshot)
    write(OUT / ("extract_"+name+"_sketch.lean"),code);write(PROJECT / ("extract_"+name+"_sketch.lean"),code)
write(OUT / "extract_header.lean",(JET / "extract_header.lean").read_bytes());write(PROJECT / "extract_header.lean",(JET / "extract_header.lean").read_bytes())
if options.prepare_only:
 dump(OUT/"preparation-state.json",{"source_sha256":EXPECTED,"selected_actual_endpoints":TARGETS,"native_sources_copied":1,"new_genuine_Definitions":DEFS,"parent_Definitions":[],"external_proof_dependencies":[],"Lean_executed":False,"API_calls":False,"root_scope_writes":False})
 print("Mechanical preparation complete; no Lean executed.")
 sys.exit(0)

run("toolchain",["lake","env","lean","--version"])
run("build-native",["lake","--no-cache","build","missions.zeta9.formalization.CoefficientMapShiftDegree"])
run("stage1-extract",["lake","env","lean","extract_decl_graph.lean"])
for name in list(EXPECTED):
    facts="sketch_info.jsonl" if name.endswith("PartialFractions") else name+"-sketch_info.jsonl"
    run("stage2-"+name,["lake","env","lean","--run","extract_"+name+"_sketch.lean","missions/zeta9/formalization/"+name+".lean","ZetaNine"],facts)
run("stage2-header",["lake","env","lean","--run","extract_header.lean","missions/zeta9/formalization/CoefficientMapShiftDegree.lean"],"header_info.jsonl")

sources={n:(OUT / ("oracle-input.lean" if n.endswith("PartialFractions") else n+"-oracle-input.lean")).read_bytes() for n in list(EXPECTED)}
for n in EXPECTED:assert sources[n]==(TASK / ("formalization/"+n+".lean")).read_bytes()
source=sources["CoefficientMapShiftDegree"]
graph=rows(OUT / "decl_graph.jsonl");byname={g["name"]:g for g in graph}
facts={n:rows(OUT / ("sketch_info.jsonl" if n.endswith("PartialFractions") else n+"-sketch_info.jsonl")) for n in list(EXPECTED)}
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
core=[g for g in graph if g["module"].endswith(".CoefficientMapShiftDegree") and g["startLine"]>0]
assert len(core)==15 and sum(g["kind"]=="def" for g in core)==3 and sum(g["kind"]=="theorem" for g in core)==12
reached=closure([g["name"] for g in core]+[g["name"] for g in graph if g["isInstance"]])
bridge="";bridge_facts=[];helper_names=[];bridge_open_context=[]
assert all(byname[n]["module"]=="missions.zeta9.formalization.CoefficientMapShiftDegree" for n in reached)
write(OUT / "actual-proof-bridge.lean.inc",bridge)
def_facts=[declaration(NS+"."+n) for n in DEFS]
defpath="Definitions/Def_ZetaNine_CoefficientMapShiftDegree.lean"
definition="\n".join("import "+m for m in MATHLIB[:-1])+"\n\nset_option autoImplicit false\nnoncomputable section\nnamespace "+NS+"\n\n"

first_def=min(f["declStart"]["offset"] for f in def_facts)
definition_open_context=[f for f in facts["CoefficientMapShiftDegree"] if f["kind"]=="command" and f["syntaxKind"]=="Lean.Parser.Command.open" and f["span"]["end"]["offset"]<first_def]
definition+="\n".join(source[f["span"]["start"]["offset"]:f["span"]["end"]["offset"]].decode() for f in definition_open_context)+"\n\n"
definition+="\n\n".join(source[f["declStart"]["offset"]:f["declEnd"]["offset"]].decode() for f in def_facts)+"\n\nend "+NS+"\n"
write(OUT / "staged" / defpath,definition);write(PROJECT / defpath,definition)
header=rows(OUT / "header_info.jsonl")[0];he=header["end"]["offset"]
assert header["start"]["offset"]==0 and source[:he].decode().strip().splitlines()==["import "+m for m in MATHLIB]

fs=facts["CoefficientMapShiftDegree"];refs=[f for f in fs if f["kind"]=="ref"]
diagnostics=[f for f in fs if f["kind"]=="command" and f["syntaxKind"]=="Lean.Parser.Command.printAxioms"]
cuts=[(f["declStart"]["offset"],f["declEnd"]["offset"],b"") for f in def_facts]+[(f["span"]["start"]["offset"],f["span"]["end"]["offset"],b"") for f in diagnostics]+[(0,he,b"")]
preamble="import Definitions.Def_ZetaNine_CoefficientMapShiftDegree\n\nset_option autoImplicit false\nopen Polynomial\nopen ZetaNine "+NS+"\n"
solheader="import Definitions.Def_ZetaNine_CoefficientMapShiftDegree\n"+"\n".join("import "+m for m in MATHLIB)+"\n\n"
origin="Zeta(9) actual polynomial shift operator: missions/zeta9/research/coefficient-map-shift-degree-2026-10-04.md. Frozen source SHA256 "+EXPECTED["CoefficientMapShiftDegree"]+". The relationship to the rational telescoper is proved separately; it is not an input to these polynomial endpoints."
definition_nl=r"""For natural $n$, define actual rational polynomials $A_n=(X-(n+1))(X+n)^{10}$, $B_n=X^{10}(X+2n+1)$ and the actual linear shift difference $D_n(H)=A_nH-B_nH(X+1)$. These are three genuine polynomial definitions with no degree, kernel, rational-function or inverse premise."""
dump(OUT/"definitions-request.json",[{"definition_name":"ZetaNine_CoefficientMapShiftDegree","definition_title":"Actual rational polynomial shift difference operator","definition":definition,"natural_language_statement":definition_nl,"source":origin,"tags":["polynomials","number-theory","formalization"],"env":REV,"private":False}])
titles=["Exact next surviving coefficient of the actual polynomial shift difference","Actual shift difference degree lower bound in the nonresonant domain","A low-degree actual shift difference forces the input polynomial to vanish"]
naturals=[r"""For every natural $n$ and nonzero rational polynomial $H$ of natural degree $d$, the coefficient of $X^{d+10}$ in the actual $D_n(H)$ equals $(7n-2-d)\operatorname{LC}(H)$. This identity needs only $H\ne0$; no positivity, parity, degree-gap, monicity or preassigned operator relation is assumed. The degree-$d+11$ terms cancel in the actual polynomial calculation.""",r"""Let $n\ge1$ and let nonzero $H\in\mathbb Q[X]$ satisfy $d=\operatorname{natdeg}H\le7n-3$. Then $d+10\le\operatorname{natdeg}D_n(H)$. The exact coefficient is proved nonzero from these original inequalities. No parity or monicity premise is added. The bound matters: $n=1,H=X^5$ lies outside it and has vanishing coefficient of $X^{15}$ although $D_1(X^5)(1)=-1152$.""",r"""Let $n\ge1$ and $H\in\mathbb Q[X]$ satisfy $\operatorname{natdeg}H\le7n-3$ and $\operatorname{natdeg}D_n(H)\le8$. Then $H=0$. No nonzero-input premise or kernel equation is assumed: the original low operator degree and quotient degree bound yield a contradiction if $H\ne0$. Zero input, constant input and the $n=1,X^5$ resonance are preserved by exact boundary checks. These polynomial facts do not by themselves state a rational telescoper relationship, coefficient-map inverse or zeta irrationality.""" ]

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
    solution=solheader+"\n"+edit(source,cuts+renames).decode()+"\n\nopen ZetaNine "+NS+"\n\ntheorem solution"+sig+":= by\n  exact "+NS+".checked_"+n+" "+ARGS[i]+"\n\n#print axioms solution\n"
    fe=[(bs-a,be-a,full.encode())]
    if d["docstring"]:
        ds=d["docstring"];fe.append((ds["start"]["offset"]-a,ds["end"]["offset"]-a,b""))
    formal=edit(source[a:v],fe).decode().strip()+":= by sorry"
    solpath="Solutions/Sol_ZetaNine_CoefficientMapShiftDegree_"+n+".lean";refpath="Theorems/Thm_ZetaNine_CoefficientMapShiftDegree_"+n+".lean"
    reference=preamble+"\n"+formal+"\n"
    for rel,text in [(solpath,solution),(refpath,reference)]:write(OUT / "staged" / rel,text);write(PROJECT / rel,text)
    problems.append({"theorem_name":full,"theorem_title":titles[i],"formal_statement":formal,"natural_language_statement":naturals[i],"preamble":preamble,"source":origin+f" Original declaration lines {d['declStart']['line']}–{d['declEnd']['line']}.","tags":["number-theory","polynomials","finite-differences","formalization"]})
    targets.append({"theorem_name":full,"local_solution":solpath,"local_reference":refpath,"wrapper_arguments":ARGS[i]})
    provtargets[full]={"declaration_fact":d,"binding_fact":bindings[0],"target_refs":rs,"rename_spans":[[x,y] for x,y,_ in renames],"original_signature":sig,"extra_hypotheses":[],"solution_sha256":digest(solution.encode()),"reference_sha256":digest(reference.encode())}
dump(OUT / "problems-request.json",{"env":REV,"private":False,"problems":problems})
dump(OUT / "target-plan.json",{"definition":"ZetaNine_CoefficientMapShiftDegree","local_definition":defpath,"targets":targets,"existing_definitions":existing_defs})
dump(OUT / "integration-provenance.json",{"sources_sha256":EXPECTED,"actual_source_position_authority":"Actually executed official cross-module declaration metaprogram, the actual self-contained Lean parser/ref oracle and Parser.parseHeader; no regex mathematical source-position queries.","graph_records":len(graph),"source_declarations":len(core),"source_defs":3,"source_proofs":12,"generated_records":[g for g in graph if g["module"].endswith(".CoefficientMapShiftDegree") and g["startLine"]==0],"source_fact_counts":{k:sum(f["kind"]==k for f in fs) for k in ["decl","ref","command"]},"header":header,"definition_facts":def_facts,"cross_module_core_closure":sorted(reached),"inline_helper_names":helper_names,"inline_helper_facts":bridge_facts,"bridge_open_context_facts":bridge_open_context,"definition_open_context_facts":definition_open_context,"bridge_sha256":digest(bridge.encode()),"deleted_diagnostic_facts":diagnostics,"targets":provtargets,"new_external_theorem_boundaries":[]})

template=(JET / "types_original.lean").read_text(encoding="utf-8-sig").split('  emit "')[0]
all_defs=[g["name"] for g in graph if g["kind"]=="def" and g["startLine"]>0]
assert len(all_defs)==3
def report(filename,module,names):
    code=template.replace("import missions.zeta9.formalization.CoefficientMapJet","import "+module)+"".join(f'  emit "{label}" `{name}\n' for label,name in names)
    write(OUT / filename,code);write(PROJECT / filename,code)
report("types_original.lean","missions.zeta9.formalization.CoefficientMapShiftDegree",[(n,n) for n in all_defs+[NS+"."+t for t in TARGETS]])
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
print(json.dumps({"complete":True,"observed_runs":len(receipt['rows']),"source_declarations":15,"actual_defs":3,"original_proofs":12,"cross_module_helpers":helper_names},ensure_ascii=False),flush=True)
