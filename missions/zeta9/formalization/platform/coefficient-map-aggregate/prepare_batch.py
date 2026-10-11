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
REV="0df444a360eaa60ab8c11dca51a86af692955474"
NS="ZetaNine.CoefficientMapAggregate"
ALIAS_NS="ZetaNine.CoefficientMapAggregateValueComparison"
EXPECTED={'CoefficientMap': 'e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03', 'CoefficientMapJet': 'e50e11c0afd2eaac1d5c58c412e5e59bc5c2068c9826063eacee8dc88fc1735a', 'CoefficientMapInjectivity': 'ebe9b9c275a34fac348837e377e2e26246e9a762889c462420b43535e9055095', 'CoefficientMapPartialFractions': 'eb0b8d54cd29ddaaa9404ee26a704bb6a47e8306741c49a6bba9b7232231f61a', 'CoefficientMapFiniteSum': 'b3ede123541d6c0eb306915d93f743979b1090c34bc4df332ab6e9da07033f97', 'CoefficientMapReflection': '8fbc53b9d9c33a61e1cf8208f89cd30dd3c6793fc32aad1cad1c51286747f707', 'CoefficientMapSummation': 'c207e8fec1358e86afd61d39853a498c9758555286b7774e5f5d7809495e876d', 'CoefficientMapAggregate': 'e538a7310f81ce9ab6c5e07d4b8bd64bb70be7a899e28f085a2c8506a4ff2299'}
DEFS=["aggregate","coordinatePolynomial","polynomialCoordinates","aggregateLinearMap","coordinateLinearMap","quarticAggregateLinearMap"]
TARGETS=["aggregate_add","polynomial_restore","aggregate_zero_all_rho"]
ARGS=["n W V","W hW","n hn W hstrong hzero s hs1 hs9"]
MATHLIB=["Mathlib.Algebra.Polynomial.Eval.SMul","Mathlib.Algebra.Polynomial.BigOperators"]
HARMONIC_SHA="5ff9d83ca177893db1eb149da985ff29b85dbe83614650a995e28066f9bd3e92"
SUMMATION_DEF_SHA="469d4c0ba2f3849ad48c764f5e3a56c09f19a726c4ad9b9ba080ec69a853962c"
HELPER_CALLEES=["aggregate_add","aggregate_smul","coordinatePolynomial_add","coordinatePolynomial_smul"]


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
env=os.environ.copy();env.pop("LEAN_PATH",None);env["LEAN_NUM_THREADS"]="1"
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
package zeta9AggregateOfflineAuthor
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "{REV}"
lean_lib Native where
  roots := #[`missions.zeta9.formalization.CoefficientMapAggregate]
  globs := #[.one `missions.zeta9.formalization.CoefficientMap, .one `missions.zeta9.formalization.CoefficientMapJet, .one `missions.zeta9.formalization.CoefficientMapInjectivity, .one `missions.zeta9.formalization.CoefficientMapPartialFractions, .one `missions.zeta9.formalization.CoefficientMapFiniteSum, .one `missions.zeta9.formalization.CoefficientMapReflection, .one `missions.zeta9.formalization.CoefficientMapSummation, .one `missions.zeta9.formalization.CoefficientMapAggregate]
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
for slug,name in [("coefficient-map","CoefficientMap"),("coefficient-map-jet","CoefficientMapJet"),("coefficient-map-injectivity","CoefficientMapInjectivity"),("coefficient-map-partial-fractions","CoefficientMapPartialFractions"),("coefficient-map-finite-sum","CoefficientMapFiniteSum"),("coefficient-map-reflection","CoefficientMapReflection"),("coefficient-map-summation","CoefficientMapSummation")]:
    batch=TASK / "formalization/platform" / slug
    rel="Definitions/Def_ZetaNine_"+name+".lean"
    assert sha(ROOT / rel)==sha(batch / "staged" / rel), "Installed actual Def differs from frozen stage."
    if name=="CoefficientMapPartialFractions":assert sha(ROOT / rel)=="74904aff5266f68b9d9f5c3013fb636f48d0cadda75e872093419845f9b666e5"
    if name=="CoefficientMapSummation":assert sha(batch / "staged" / rel)==SUMMATION_DEF_SHA
    write(PROJECT / rel,(batch / "staged" / rel).read_bytes())
    existing_defs.append({"root_relative":rel,"sha256":sha(batch / "staged" / rel),"task_relative":(batch / "staged" / rel).relative_to(TASK).as_posix()})

hrel="Definitions/Def_ZetaNine_HarmonicStability.lean"
assert sha(ROOT / hrel)==HARMONIC_SHA
write(PROJECT / hrel,(ROOT / hrel).read_bytes())
write(OUT / "dependencies" / hrel,(ROOT / hrel).read_bytes())
existing_defs.append({"root_relative":hrel,"sha256":HARMONIC_SHA,"task_relative":(OUT / "dependencies" / hrel).relative_to(TASK).as_posix()})

g=(JET / "extract_decl_graph.lean").read_text(encoding="utf-8-sig")
g=g.replace("import missions.zeta9.formalization.CoefficientMapJet","import missions.zeta9.formalization.CoefficientMapAggregate")
g=g.replace("missions/zeta9/formalization/platform/coefficient-map-jet/decl_graph.jsonl","../decl_graph.jsonl")
assert g.count("fun m => projPrefix.isPrefixOf m")==1
g=g.replace("fun m => projPrefix.isPrefixOf m","fun m => projPrefix.isPrefixOf m || m == `Definitions.Def_ZetaNine_HarmonicStability")
write(OUT / "extract_decl_graph.lean",g);write(PROJECT / "extract_decl_graph.lean",g)
s=(JET / "extract_sketch_info.lean").read_text(encoding="utf-8-sig")
old="missions/zeta9/formalization/platform/coefficient-map-jet/oracle-input.lean"
assert s.count(old)==1
for name in EXPECTED:
    snapshot="oracle-input.lean" if name.endswith("PartialFractions") else name+"-oracle-input.lean"
    code=s.replace(old,"../"+snapshot)
    write(OUT / ("extract_"+name+"_sketch.lean"),code);write(PROJECT / ("extract_"+name+"_sketch.lean"),code)
hcode=s.replace(old,"../HarmonicStability-oracle-input.lean")
write(OUT / "extract_HarmonicStability_sketch.lean",hcode);write(PROJECT / "extract_HarmonicStability_sketch.lean",hcode)
write(OUT / "extract_header.lean",(JET / "extract_header.lean").read_bytes());write(PROJECT / "extract_header.lean",(JET / "extract_header.lean").read_bytes())
run("toolchain",["lake","env","lean","--version"])
run("build-native-HarmonicStability",["lake","--no-cache","build","Definitions.Def_ZetaNine_HarmonicStability"])
for module in EXPECTED:
    run("build-native-"+module,["lake","--no-cache","build","missions.zeta9.formalization."+module])
run("stage1-extract",["lake","env","lean","extract_decl_graph.lean"])
for name in EXPECTED:
    facts="sketch_info.jsonl" if name.endswith("PartialFractions") else name+"-sketch_info.jsonl"
    run("stage2-"+name,["lake","env","lean","--run","extract_"+name+"_sketch.lean","missions/zeta9/formalization/"+name+".lean","ZetaNine"],facts)
run("stage2-HarmonicStability",["lake","env","lean","--run","extract_HarmonicStability_sketch.lean","Definitions/Def_ZetaNine_HarmonicStability.lean","ZetaNine"],"HarmonicStability-sketch_info.jsonl")
run("stage2-header",["lake","env","lean","--run","extract_header.lean","missions/zeta9/formalization/CoefficientMapAggregate.lean"],"header_info.jsonl")

sources={n:(OUT / ("oracle-input.lean" if n.endswith("PartialFractions") else n+"-oracle-input.lean")).read_bytes() for n in EXPECTED}
for n in EXPECTED:assert sources[n]==(TASK / ("formalization/"+n+".lean")).read_bytes()
source=sources["CoefficientMapAggregate"]
graph=rows(OUT / "decl_graph.jsonl");byname={g["name"]:g for g in graph}
facts={n:rows(OUT / ("sketch_info.jsonl" if n.endswith("PartialFractions") else n+"-sketch_info.jsonl")) for n in EXPECTED}
harmonic_source=(OUT / "HarmonicStability-oracle-input.lean").read_bytes()
harmonic_raw_source=(ROOT / hrel).read_bytes()
assert digest(harmonic_raw_source)==HARMONIC_SHA
assert harmonic_source==harmonic_raw_source.replace(b"\r\n",b"\n")
harmonic_normalization={"raw_source_sha256":HARMONIC_SHA,"parser_normalized_sha256":digest(harmonic_source),"normalization":"Parser.mkInputContext CRLF to LF; exact official persisted inputString; no source rewrite","raw_bytes":len(harmonic_raw_source),"parser_input_bytes":len(harmonic_source),"CRLF_count":harmonic_raw_source.count(b"\r\n")}
harmonic_facts=rows(OUT / "HarmonicStability-sketch_info.jsonl")
assert len([f for f in harmonic_facts if f["kind"]=="decl"])==2
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
core=[g for g in graph if g["module"].endswith(".CoefficientMapAggregate") and g["startLine"]>0]
assert len(core)==26 and sum(g["kind"]=="def" for g in core)==6 and sum(g["kind"]=="theorem" for g in core)==20
reached=closure([g["name"] for g in core]+[g["name"] for g in graph if g["isInstance"]])
bridge="";bridge_facts=[];helper_names=[];bridge_open_context=[]
for module in list(EXPECTED)[:-1]:
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
defpath="Definitions/Def_ZetaNine_CoefficientMapAggregate.lean"
# Structure proof fields are closed below from actual graph/parser facts.
first_def=min(f["declStart"]["offset"] for f in def_facts)
definition_open_context=[f for f in facts["CoefficientMapAggregate"] if f["kind"]=="command" and f["syntaxKind"]=="Lean.Parser.Command.open" and f["span"]["end"]["offset"]<first_def]
from embed_definition_fields import create_definitions
context={"OUT":OUT,"PROJECT":PROJECT,"NS":NS,"ALIAS_NS":ALIAS_NS,"source":source,"graph":graph,"byname":byname,"facts":facts,"DEFS":DEFS,"MATHLIB":MATHLIB,"def_facts":def_facts,"definition_open_context":definition_open_context,"declaration":declaration,"closure":closure,"edit":edit,"write":write,"dump":dump,"rows":rows,"run":run,"digest":digest}
definition,alias_definition,embedded_provenance=create_definitions(context)
write(OUT / "staged" / defpath,definition);write(PROJECT / defpath,definition)
write(OUT / "native-value-comparison-definition.lean",alias_definition);write(PROJECT / "NativeValueComparisonDefinition.lean",alias_definition)
header=rows(OUT / "header_info.jsonl")[0];he=header["end"]["offset"]
assert header["start"]["offset"]==0 and source[:he].decode().strip().splitlines()==["import missions.zeta9.formalization.CoefficientMapSummation"]+["import "+m for m in MATHLIB]
fs=facts["CoefficientMapAggregate"];refs=[f for f in fs if f["kind"]=="ref"]
diagnostics=[f for f in fs if f["kind"]=="command" and f["syntaxKind"]=="Lean.Parser.Command.printAxioms"]
cuts=[(f["declStart"]["offset"],f["declEnd"]["offset"],b"") for f in def_facts]+[(f["span"]["start"]["offset"],f["span"]["end"]["offset"],b"") for f in diagnostics]+[(0,he,b"")]
preamble="import Definitions.Def_ZetaNine_CoefficientMapAggregate\n\nset_option autoImplicit false\nopen scoped BigOperators\nopen Finset Polynomial\nopen ZetaNine "+NS+" ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapSummation ZetaNine.HarmonicStability\n"
solheader="import Definitions.Def_ZetaNine_CoefficientMapAggregate\nimport Mathlib.Tactic\n"+"\n".join("import "+m for m in MATHLIB)+"\n\n"+bridge
from aggregate_metadata import build_metadata
origin,definition_nl,titles,naturals=build_metadata(EXPECTED["CoefficientMapAggregate"])
dump(OUT / "definitions-request.json",[{"definition_name":"ZetaNine_CoefficientMapAggregate","definition_title":"Actual five rational outputs and quartic coordinate maps","definition":definition,"natural_language_statement":definition_nl,"source":origin,"tags":["number-theory","linear-algebra","polynomials"],"env":REV,"private":False}])

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
    solution=solheader+"\n"+edit(source,cuts+renames).decode()+"\n\nopen ZetaNine "+NS+" ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapSummation ZetaNine.HarmonicStability\n\ntheorem solution"+sig+":= by\n  exact "+NS+".checked_"+n+" "+ARGS[i]+"\n\n#print axioms solution\n"
    fe=[(bs-a,be-a,full.encode())]
    if d["docstring"]:
        ds=d["docstring"];fe.append((ds["start"]["offset"]-a,ds["end"]["offset"]-a,b""))
    formal=edit(source[a:v],fe).decode().strip()+":= by sorry"
    solpath="Solutions/Sol_ZetaNine_CoefficientMapAggregate_"+n+".lean";refpath="Theorems/Thm_ZetaNine_CoefficientMapAggregate_"+n+".lean"
    reference=preamble+"\n"+formal+"\n"
    for rel,text in [(solpath,solution),(refpath,reference)]:write(OUT / "staged" / rel,text);write(PROJECT / rel,text)
    problems.append({"theorem_name":full,"theorem_title":titles[i],"formal_statement":formal,"natural_language_statement":naturals[i],"preamble":preamble,"source":origin+f" Original declaration lines {d['declStart']['line']}–{d['declEnd']['line']}.","tags":["number-theory","polynomials","partial-fractions","formalization"]})
    targets.append({"theorem_name":full,"local_solution":solpath,"local_reference":refpath,"wrapper_arguments":ARGS[i]})
    provtargets[full]={"declaration_fact":d,"binding_fact":bindings[0],"target_refs":rs,"rename_spans":[[x,y] for x,y,_ in renames],"original_signature":sig,"extra_hypotheses":[],"solution_sha256":digest(solution.encode()),"reference_sha256":digest(reference.encode())}
dump(OUT / "problems-request.json",{"env":REV,"private":False,"problems":problems})
dump(OUT / "target-plan.json",{"definition":"ZetaNine_CoefficientMapAggregate","local_definition":defpath,"targets":targets,"existing_definitions":existing_defs})
dump(OUT / "integration-provenance.json",{"sources_sha256":EXPECTED,"pure_HarmonicStability_sha256":HARMONIC_SHA,"pure_HarmonicStability_parser_decl_count":2,"pure_HarmonicStability_parser_normalization":harmonic_normalization,"actual_source_position_authority":"Actually executed official cross-module declaration metaprogram, all eight actual source parser/ref oracles plus the actual pure HarmonicStability Definition parser and Parser.parseHeader; no regex mathematical source-position queries.","graph_records":len(graph),"source_declarations":len(core),"source_defs":6,"source_proofs":20,"generated_records":[g for g in graph if g["module"].endswith(".CoefficientMapAggregate") and g["startLine"]==0],"source_fact_counts":{k:sum(f["kind"]==k for f in fs) for k in ["decl","ref","command"]},"header":header,"definition_facts":def_facts,"embedded_constructor_proof_fields":embedded_provenance,"cross_module_core_closure":sorted(reached),"inline_helper_names":helper_names,"inline_helper_facts":bridge_facts,"bridge_open_context_facts":bridge_open_context,"definition_open_context_facts":definition_open_context,"bridge_sha256":digest(bridge.encode()),"deleted_diagnostic_facts":diagnostics,"targets":provtargets,"new_external_theorem_boundaries":[]})

template=(JET / "types_original.lean").read_text(encoding="utf-8-sig").split('  emit "')[0]
all_defs=[g["name"] for g in graph if g["kind"]=="def" and g["startLine"]>0]
assert len(all_defs)==49
def report(filename,module,names):
    code=template.replace("import missions.zeta9.formalization.CoefficientMapJet","import "+module)+"".join(f'  emit "{label}" `{name}\n' for label,name in names)
    write(OUT / filename,code);write(PROJECT / filename,code)
report("types_original.lean","missions.zeta9.formalization.CoefficientMapAggregate",[(n,n) for n in all_defs+[NS+"."+t for t in TARGETS]])
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
run("build-native-value-alias",["lake","env","lean","-o",".lake/build/lib/lean/NativeValueComparisonDefinition.olean","NativeValueComparisonDefinition.lean"])
from embed_definition_fields import create_value_comparison
create_value_comparison(context)
run("native-value-comparison",["lake","env","lean","native-value-comparison.lean"])
field_state=json.loads((OUT / "embedded-field-provenance.json").read_text(encoding="utf-8"));field_state["data_value_kernel_comparison_pending"]=False;field_state["actual_value_comparison_log_sha256"]=sha(OUT / "native-value-comparison.log");dump(OUT / "embedded-field-provenance.json",field_state)
receipt["complete"]=True;receipt["native_and_staged_objects_borrowed"]=False;dump(OUT / "compile-receipt.json",receipt)
print(json.dumps({"complete":True,"observed_runs":len(receipt['rows']),"source_declarations":26,"actual_defs":6,"original_proofs":20,"cross_module_helpers":helper_names},ensure_ascii=False),flush=True)
