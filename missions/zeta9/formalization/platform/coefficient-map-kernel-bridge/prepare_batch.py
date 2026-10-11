"""KernelBridge actual offline author; one serial Lean lane only."""
from pathlib import Path
import hashlib,json,os,subprocess,sys
sys.stdout.reconfigure(encoding="utf-8")
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[2];ROOT=TASK.parents[1];PROJECT=OUT/"p";BUILD=TASK/".rt/k1/b"
JET=TASK/"formalization/platform/coefficient-map-jet"
REV="0df444a360eaa60ab8c11dca51a86af692955474";NS="ZetaNine.CoefficientMapKernelBridge"
subprocess.run([sys.executable,str(OUT/"prepare_plan.py")],check=True)
plan=json.loads((OUT/"preparation-state.json").read_text(encoding="utf-8-sig"))
EXPECTED=plan["sources_sha256"];DEFS=plan["new_actual_definitions"]
TARGETS=[r["name"].split(".")[-1] for r in plan["selected_actual_endpoints"]];ARGS=[r["arguments"] for r in plan["selected_actual_endpoints"]]
PURE_NAME="Def_ZetaNine_HarmonicStability"
CONTROL_MODULES=[r["module"] for r in plan["native_controls"]]
control_bindings=[dict(r,task_relative=r["source_task_relative"]) for r in plan["native_controls"]]
existing_defs=plan["required_parent_definitions"]
(PROJECT/".lake").mkdir(exist_ok=True)
if not (PROJECT/".lake/packages").exists():
 p=subprocess.run(["cmd","/c","mklink","/J",str(PROJECT/".lake/packages"),str(ROOT/".lake/packages")],capture_output=True)
 assert p.returncode==0,(p.stdout+p.stderr).decode(errors="replace")
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
receipt={"source_project_task_relative":PROJECT.relative_to(TASK).as_posix(),"fresh_build_task_relative":BUILD.relative_to(TASK).as_posix(),"native_and_staged_objects_borrowed":False,"role":"author offline batch","source_sha256":EXPECTED,"root_writes":False,"API_calls":False,"rows":[]}
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

assert not BUILD.exists() or not any(BUILD.rglob("*")),"Fresh cache already populated; retain previous attempt and select a new cache."
subprocess.run([sys.executable,str(OUT / "check_output_paths.py")],check=True)
run("toolchain",["lake","env","lean","--version"])
run("build-native",["lake","--no-cache","build","missions.zeta9.formalization.CoefficientMapKernelBridge"])
for m in CONTROL_MODULES:run("native-control-"+m,["lake","--no-cache","build",m])
run("stage1-extract",["lake","env","lean","extract_decl_graph.lean"])
for name in list(EXPECTED)+[PURE_NAME]:
    facts="sketch_info.jsonl" if name.endswith("PartialFractions") else name+"-sketch_info.jsonl"
    run("stage2-"+name,["lake","env","lean","--run","extract_"+name+"_sketch.lean",("Definitions/"+name+".lean" if name==PURE_NAME else "missions/zeta9/formalization/"+name+".lean"),"ZetaNine"],facts)
run("stage2-header",["lake","env","lean","--run","extract_header.lean","missions/zeta9/formalization/CoefficientMapKernelBridge.lean"],"header_info.jsonl")

sources={n:(OUT / ("oracle-input.lean" if n.endswith("PartialFractions") else n+"-oracle-input.lean")).read_bytes() for n in list(EXPECTED)+[PURE_NAME]}
for n in EXPECTED:assert sources[n]==(TASK / ("formalization/"+n+".lean")).read_bytes()
source=sources["CoefficientMapKernelBridge"]
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
core=[g for g in graph if g["module"].endswith(".CoefficientMapKernelBridge") and g["startLine"]>0]
assert len(core)==30 and sum(g["kind"]=="def" for g in core)==7 and sum(g["kind"]=="theorem" for g in core)==23
control_roots=[g["name"] for g in graph if g["module"] in CONTROL_MODULES and g["startLine"]>0]
reached=closure([g["name"] for g in core]+control_roots+[g["name"] for g in graph if g["isInstance"]])
bridge="";bridge_facts=[];helper_names=[];bridge_open_context=[]
for module in ["CoefficientMap","CoefficientMapJet","CoefficientMapInjectivity","CoefficientMapPartialFractions","CoefficientMapReflection","CoefficientMapFiniteSum","CoefficientMapSummation","CoefficientMapAggregate","CoefficientMapTelescoper","CoefficientMapShiftDegree"]:
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
defpath="Definitions/Def_ZetaNine_CoefficientMapKernelBridge.lean"
subprocess.run([sys.executable,str(OUT/"generate_closed_equiv_field.py")],check=True)
definition=(OUT/"staged"/defpath).read_text(encoding="utf-8-sig")
field_provenance=json.loads((OUT/"embedded-bijection-provenance.json").read_text(encoding="utf-8-sig"))
definition_open_context=[]
header=rows(OUT / "header_info.jsonl")[0];he=header["end"]["offset"]
assert header["start"]["offset"]==0 and source[:he].decode().strip().splitlines()==["import missions.zeta9.formalization.CoefficientMapTelescoper","import missions.zeta9.formalization.CoefficientMapShiftDegree","import Mathlib.Order.Interval.Set.Infinite"]

fs=facts["CoefficientMapKernelBridge"];refs=[f for f in fs if f["kind"]=="ref"]
diagnostics=[f for f in fs if f["kind"]=="command" and f["syntaxKind"]=="Lean.Parser.Command.printAxioms"]
cuts=[(f["declStart"]["offset"],f["declEnd"]["offset"],b"") for f in def_facts]+[(f["span"]["start"]["offset"],f["span"]["end"]["offset"],b"") for f in diagnostics]+[(0,he,b"")]
preamble="import Definitions.Def_ZetaNine_CoefficientMapKernelBridge\n\nset_option autoImplicit false\nopen scoped BigOperators Topology\nopen Finset Polynomial Filter\nopen ZetaNine "+NS+" ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapAggregate\n"
solheader="import Definitions.Def_ZetaNine_CoefficientMapKernelBridge\nimport Mathlib.Tactic\n\nset_option autoImplicit false\nset_option maxHeartbeats 2000000\nnoncomputable section\n"+bridge
origin="Zeta(9) actual original five-dimensional coefficient map kernel and rational inverse: missions/zeta9/research/coefficient-map-kernel-2026-10-04.md. Frozen source SHA256 "+EXPECTED["CoefficientMapKernelBridge"]+". The actual kernel, polynomial relation, bijection, inverse and sum are derived from genuine data and source proofs."
definition_nl="Define the original positive/negative products and shift factors, the actual five-dimensional rational quartic aggregate equivalence, its actual inverse multiplier and prescribed real linear form. The equivalence constructor's bijective proof is closed from the genuine source proof closure, without an added kernel/bijection/inverse premise. All seven actual data functions and original Even n, n>=2 domain remain fixed. No integer inverse, denominator height, small linear form or irrationality claim is made."
dump(OUT/"definitions-request.json",[{"definition_name":"ZetaNine_CoefficientMapKernelBridge","definition_title":"Actual rational quartic aggregate equivalence and inverse multiplier","definition":definition,"natural_language_statement":definition_nl,"source":origin,"tags":["number-theory","polynomials","linear-algebra","formalization"],"env":REV,"private":False}])
titles=["The actual quartic coefficient map has trivial kernel","The actual five-dimensional rational coefficient map is bijective","The actual inverse multiplier has its prescribed sum and absolute convergence"]
naturals=["Let n>=2 be even and W be a rational polynomial of natural degree at most4. If its genuine aggregate F_n(W) is zero, then W is zero. The true rational telescoper, infinitely many positive regular evaluation points, polynomial identity and shift-degree obstruction are proved internally; none is an extra premise.","For each even n>=2 the original five-dimensional rational aggregate map on quartic coordinates is bijective. Injectivity follows from the actual quartic kernel result, then finite dimensionality gives surjectivity. No determinant, rank, bijection or inverse assumption is added.","For each even n>=2 and b:Fin5->Rat, the actual inverse rational quartic multiplier produces a HasSum of the actual weightedR at positive integers with value prescribedL(b), and its absolute norms are Summable. The input b contains the rational constant and zeta3,5,7,9 coefficients. This is the original genuine HasSum, not a totalized tsum identity. Integer inverse coefficients, height bounds and irrationality remain unproved here."]

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
    solution=solheader+"\n"+edit(source,cuts+renames).decode()+"\n\nopen ZetaNine "+NS+" ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapFiniteSum ZetaNine.CoefficientMapSummation ZetaNine.CoefficientMapAggregate ZetaNine.HarmonicStability\n\ntheorem solution"+sig+":= by\n  exact "+NS+".checked_"+n+" "+ARGS[i]+"\n\n#print axioms solution\n"
    fe=[(bs-a,be-a,full.encode())]
    if d["docstring"]:
        ds=d["docstring"];fe.append((ds["start"]["offset"]-a,ds["end"]["offset"]-a,b""))
    formal=edit(source[a:v],fe).decode().strip()+":= by sorry"
    solpath="Solutions/Sol_ZetaNine_CoefficientMapKernelBridge_"+n+".lean";refpath="Theorems/Thm_ZetaNine_CoefficientMapKernelBridge_"+n+".lean"
    reference=preamble+"\n"+formal+"\n"
    for rel,text in [(solpath,solution),(refpath,reference)]:write(OUT / "staged" / rel,text);write(PROJECT / rel,text)
    problems.append({"theorem_name":full,"theorem_title":titles[i],"formal_statement":formal,"natural_language_statement":naturals[i],"preamble":preamble,"source":origin+f" Original declaration lines {d['declStart']['line']}–{d['declEnd']['line']}.","tags":["number-theory","polynomials","finite-differences","formalization"]})
    targets.append({"theorem_name":full,"local_solution":solpath,"local_reference":refpath,"wrapper_arguments":ARGS[i]})
    provtargets[full]={"declaration_fact":d,"binding_fact":bindings[0],"target_refs":rs,"rename_spans":[[x,y] for x,y,_ in renames],"original_signature":sig,"extra_hypotheses":[],"solution_sha256":digest(solution.encode()),"reference_sha256":digest(reference.encode())}
dump(OUT / "problems-request.json",{"env":REV,"private":False,"problems":problems})
dump(OUT / "target-plan.json",{"definition":"ZetaNine_CoefficientMapKernelBridge","local_definition":defpath,"targets":targets,"existing_definitions":existing_defs})
dump(OUT / "integration-provenance.json",{"sources_sha256":EXPECTED,"actual_source_position_authority":"Actually executed official cross-module declaration metaprogram, all eleven actual native source parser/ref oracles plus the genuine pure Harmonic definition oracle and Parser.parseHeader; no regex mathematical source-position queries.","graph_records":len(graph),"source_declarations":len(core),"source_defs":7,"source_proofs":23,"generated_records":[g for g in graph if g["module"].endswith(".CoefficientMapKernelBridge") and g["startLine"]==0],"source_fact_counts":{k:sum(f["kind"]==k for f in fs) for k in ["decl","ref","command"]},"header":header,"definition_facts":def_facts,"cross_module_core_closure":sorted(reached),"native_closed_control_bindings":control_bindings,"native_closed_control_roots":control_roots,"inline_helper_names":helper_names,"inline_helper_facts":bridge_facts,"bridge_open_context_facts":bridge_open_context,"definition_open_context_facts":definition_open_context,"bridge_sha256":digest(bridge.encode()),"deleted_diagnostic_facts":diagnostics,"targets":provtargets,"embedded_bijection_provenance_sha256":sha(OUT/"embedded-bijection-provenance.json"),"new_external_theorem_boundaries":[]})

template=(JET / "types_original.lean").read_text(encoding="utf-8-sig").split('  emit "')[0]
all_defs=[g["name"] for g in graph if g["kind"]=="def" and g["startLine"]>0]
assert len(all_defs)==65
def report(filename,module,names):
    code=template.replace("import missions.zeta9.formalization.CoefficientMapJet","import "+module)+"".join(f'  emit "{label}" `{name}\n' for label,name in names)
    write(OUT / filename,code);write(PROJECT / filename,code)
report("types_original.lean","missions.zeta9.formalization.CoefficientMapKernelBridge",[(n,n) for n in all_defs+[NS+"."+t for t in TARGETS]])
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
receipt["fresh_main_cache_bindings"]=[{"task_relative":p.relative_to(TASK).as_posix(),"sha256":sha(p),"bytes":p.stat().st_size} for p in sorted(BUILD.rglob("*")) if p.is_file()]
receipt["complete"]=True;receipt["native_and_staged_objects_borrowed"]=False;dump(OUT / "compile-receipt.json",receipt)
print(json.dumps({"complete":True,"observed_runs":len(receipt['rows']),"source_declarations":30,"actual_defs":7,"original_proofs":23,"cross_module_helpers":helper_names},ensure_ascii=False),flush=True)
