"""Reconstruct all Jet stages from independently re-executed cross-module facts."""
from pathlib import Path
import hashlib,json,sys
sys.stdout.reconfigure(encoding="utf-8")
HERE=Path(__file__).resolve().parent
BATCH=HERE.parent
TASK=BATCH.parents[2]
ROOT=TASK.parents[1]
BASE=TASK / "formalization/platform/coefficient-map"
NS="ZetaNine.CoefficientMapJet"
BNS="ZetaNine.CoefficientMap"
DEFS=["shiftedVariable","shiftedNumerator","shiftedClearedDenominator","localU","integerLocalU","clearedSeries","weightedClearedSeries","localCoefficient","weightedLocalCoefficient"]
TARGETS=["clearedSeries_unique","coefficient_convolution_explicit","integer_coefficient_convolution"]
ARGS=["n j S hS","n j s hj hs1 hs9 W","n j s hj hs1 hs9 W"]
MATHLIB=["Mathlib.RingTheory.PowerSeries.Inverse","Mathlib.Algebra.Polynomial.Eval.Coeff","Mathlib.Algebra.BigOperators.NatAntidiagonal"]
checks=[]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def digest(b): return hashlib.sha256(b).hexdigest()
def load(p): return json.loads(p.read_text(encoding="utf-8-sig"))
def rows(p): return [json.loads(s) for s in p.read_text(encoding="utf-8-sig").splitlines() if s.startswith("{")]
def check(name,okay,evidence=None):
    checks.append({"name":name,"pass":bool(okay),"evidence":evidence})
    assert okay,name
def canonical(rs):
    normalized=[]
    for r in rs:
        r=dict(r)
        for k in ["typeDeps","valueDeps"]:
            if k in r:r[k]=sorted(r[k])
        normalized.append(json.dumps(r,sort_keys=True,ensure_ascii=False))
    return sorted(normalized)
def splice(data,edits):
    edge=len(data)
    for a,b,replacement in sorted(set(edits),reverse=True):
        assert 0<=a<=b<=edge,(a,b,edge)
        data=data[:a]+replacement+data[b:]
        edge=a
    return data
source=(TASK / "formalization/CoefficientMapJet.lean").read_bytes()
base_source=(TASK / "formalization/CoefficientMap.lean").read_bytes()
check("Jet_and_Base_frozen_sources_and_independent_parser_snapshots_exact",digest(source)=="e50e11c0afd2eaac1d5c58c412e5e59bc5c2068c9826063eacee8dc88fc1735a" and digest(base_source)=="e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03" and source==(HERE / "oracle-input.lean").read_bytes()==(BATCH / "oracle-input.lean").read_bytes() and base_source==(HERE / "base-oracle-input.lean").read_bytes()==(BASE / "oracle-input.lean").read_bytes())
graph=rows(HERE / "decl_graph.jsonl")
facts=rows(HERE / "sketch_info.jsonl")
base_facts=rows(HERE / "base-sketch_info.jsonl")
headers=rows(HERE / "header_info.jsonl")
check("independent_cross_module_Stage1_graph_matches_actual_author_graph",canonical(graph)==canonical(rows(BATCH / "decl_graph.jsonl")) and len(graph)==65,{"cross_module_environment_records":65,"Jet_records":sum(g["module"].endswith(".CoefficientMapJet") for g in graph),"Base_records":sum(g["module"].endswith(".CoefficientMap") for g in graph)})
check("independent_Jet_Stage2_all_actual_decl_ref_command_spans_match",canonical(facts)==canonical(rows(BATCH / "sketch_info.jsonl")),{kind:sum(f["kind"]==kind for f in facts) for kind in ["decl","ref","command"]})
check("independent_Base_Stage2_actual_spans_match_frozen_cross_module_dependency",canonical(base_facts)==canonical(rows(BASE / "sketch_info.jsonl")))
check("actual_Lean_parseHeader_reexecuted_and_exact",len(headers)==1 and canonical(headers)==canonical(rows(BATCH / "header_info.jsonl")),headers)
header=headers[0]
header_end=header["end"]["offset"]
check("deleted_header_is_exactly_native_Base_and_three_actual_Mathlib_imports",header["start"]["offset"]==0 and source[:header_end].decode().strip().splitlines()==["import missions.zeta9.formalization.CoefficientMap"]+["import "+m for m in MATHLIB])
byname={g["name"]:g for g in graph}
check("cross_module_graph_contains_no_axiom_or_new_opaque_premise",len(byname)==65 and all(g["kind"] in ["def","theorem"] for g in graph))
decls=[f for f in facts if f["kind"]=="decl"]
base_decls=[f for f in base_facts if f["kind"]=="decl"]
refs=[f for f in facts if f["kind"]=="ref"]
commands=[f for f in facts if f["kind"]=="command"]
def declaration(full):
    g=byname[full]
    assert g["startLine"]>0
    ds=base_decls if g["module"].endswith(".CoefficientMap") else decls
    matches=[d for d in ds if d["declStart"]["line"]<=g["startLine"]<=d["declEnd"]["line"]]
    assert len(matches)==1 and matches[0]["valStart"] is not None
    return matches[0]
def closure(seed):
    found=set();work=list(seed)
    while work:
        n=work.pop()
        if n in found:continue
        found.add(n)
        work.extend(byname[n]["typeDeps"]+byname[n]["valueDeps"])
    return found
jetcore=[g for g in graph if g["module"].endswith(".CoefficientMapJet") and g["startLine"]>0]
generated=[g["name"] for g in graph if g["module"].endswith(".CoefficientMapJet") and g["startLine"]==0]
check("Jet_source_core_is_nine_defs_nineteen_proofs_generated_nine_not_source",len(jetcore)==28 and sum(g["kind"]=="def" for g in jetcore)==9 and sum(g["kind"]=="theorem" for g in jetcore)==19 and len(generated)==9,{"generated_declarations":generated})
reached=closure([g["name"] for g in jetcore]+[g["name"] for g in graph if g["isInstance"]])
base_helpers=[byname[n] for n in reached if byname[n]["module"].endswith(".CoefficientMap") and byname[n]["kind"]=="theorem" and byname[n]["startLine"]>0]
base_helpers.sort(key=lambda g:g["startLine"])
check("true_cross_module_proof_closure_is_exactly_original_denominator_nonzero",[g["name"] for g in base_helpers]==[BNS+".clearedPoleProduct_ne_zero"],{"closure":sorted(reached),"Base_helpers":[g["name"] for g in base_helpers]})
bridge="open scoped BigOperators\nopen Finset Polynomial\n\nnamespace "+BNS+"\n\n"
bridge+="\n\n".join(base_source[declaration(g["name"])["declStart"]["offset"]:declaration(g["name"])["declEnd"]["offset"]].decode() for g in base_helpers)
bridge+="\n\nend "+BNS+"\n"
check("Base_inline_bridge_exactly_reconstructed_original_proof_parser_bytes",bridge.encode()==(BATCH / "base-proof-bridge.lean.inc").read_bytes(),{"sha256":digest(bridge.encode())})
definition_facts=[declaration(NS+"."+n) for n in DEFS]
definition_path="Definitions/Def_ZetaNine_CoefficientMapJet.lean"
prefix="import Definitions.Def_ZetaNine_CoefficientMap\n"+"\n".join("import "+m for m in MATHLIB)+"\n\nset_option autoImplicit false\nnoncomputable section\nopen scoped BigOperators\nopen Finset Polynomial\n\nnamespace "+NS+"\n\n"
definition=prefix.encode()+b"\n\n".join(source[d["declStart"]["offset"]:d["declEnd"]["offset"]] for d in definition_facts)+( "\n\nend "+NS+"\n").encode()
check("nine_actual_Jet_Def_spans_no_lemma_or_closed_formula_replacement",all(byname[NS+"."+n]["kind"]=="def" for n in DEFS) and definition==(BATCH / "staged" / definition_path).read_bytes(),{"sha256":digest(definition)})
definition_request=load(BATCH / "definitions-request.json")
check("definition_request_body_matches_actual_reconstructed_Def",len(definition_request)==1 and definition_request[0]["definition"].encode()==definition)
definition_cuts=[(d["declStart"]["offset"],d["declEnd"]["offset"],b"") for d in definition_facts]
diagnostics=[f for f in commands if f["syntaxKind"]=="Lean.Parser.Command.printAxioms"]
diagnostic_cuts=[(f["span"]["start"]["offset"],f["span"]["end"]["offset"],b"") for f in diagnostics]
check("exactly_ten_parser_certified_print_diagnostics_removed",len(diagnostics)==10 and all(source[a:b].startswith(b"#print axioms ") for a,b,_ in diagnostic_cuts))
solution_header="import Definitions.Def_ZetaNine_CoefficientMapJet\nimport Mathlib.Tactic\n"+"\n".join("import "+m for m in MATHLIB)+"\n\n"+bridge
preamble="import Definitions.Def_ZetaNine_CoefficientMapJet\n\nset_option autoImplicit false\nopen scoped BigOperators\nopen Finset Polynomial\nopen "+NS+"\n"
request=load(BATCH / "problems-request.json")
check("exact_three_endpoints_and_pinned_public_offline_request",request["env"]=="0df444a360eaa60ab8c11dca51a86af692955474" and request["private"] is False and [p["theorem_name"] for p in request["problems"]]==[NS+"."+n for n in TARGETS])
targets=[]
for i,n in enumerate(TARGETS):
    full=NS+"."+n;d=declaration(full)
    begin,val=d["declStart"]["offset"],d["valStart"]["offset"]
    targetrefs=[r for r in refs if r["const"]==full]
    bindings=[r for r in targetrefs if begin<=r["start"]["offset"]<val]
    assert len(bindings)==1
    a,b=bindings[0]["start"]["offset"],bindings[0]["end"]["offset"]
    assert source[a:b].decode()==n
    signature=source[b:val]
    renames=[]
    for r in targetrefs:
        x,y=r["start"]["offset"],r["end"]["offset"]
        if any(ca<=x and y<=cb for ca,cb,_ in diagnostic_cuts):continue
        old=source[x:y].decode();assert old in [n,full]
        renames.append((x,y,("checked_"+n if old==n else NS+".checked_"+n).encode()))
    core=splice(source,[(0,header_end,b"")]+definition_cuts+diagnostic_cuts+renames)
    solution=solution_header.encode()+b"\n"+core+("\n\nopen "+NS+"\n\ntheorem solution").encode()+signature+(":= by\n  exact "+NS+".checked_"+n+" "+ARGS[i]+"\n\n#print axioms solution\n").encode()
    formal_edits=[(a-begin,b-begin,full.encode())]
    if d["docstring"]:
        doc=d["docstring"];formal_edits.append((doc["start"]["offset"]-begin,doc["end"]["offset"]-begin,b""))
    formal=splice(source[begin:val],formal_edits).decode().strip()+":= by sorry"
    reference=(preamble+"\n"+formal+"\n").encode()
    solpath="Solutions/Sol_ZetaNine_CoefficientMapJet_"+n+".lean"
    refpath="Theorems/Thm_ZetaNine_CoefficientMapJet_"+n+".lean"
    check(n+"_full_solution_exact_independent_splice_of_original_proofs_and_header",solution==(BATCH / "staged" / solpath).read_bytes(),{"solution_sha256":digest(solution),"rename_spans":[[x,y] for x,y,_ in renames],"Jet_proofs_retained":19,"Base_proof_inlined":1,"native_or_Theorems_or_Solutions_imports_added":False,"Mathlib_Tactic_restores_actual_transitive_original_import":True})
    check(n+"_reference_request_original_signature_no_added_assumptions",reference==(BATCH / "staged" / refpath).read_bytes() and request["problems"][i]["formal_statement"]==formal and request["problems"][i]["preamble"]==preamble,{"actual_original_signature":signature.decode()})
    targets.append({"theorem":full,"solution":solpath,"reference":refpath,"signature":signature.decode(),"rename_spans":[[x,y] for x,y,_ in renames]})
frozen=[]
for line in (BATCH / "SHA256SUMS.txt").read_text(encoding="utf-8-sig").splitlines():
    h,rel=line.split("  ",1);p=(BATCH / rel).resolve();assert p.is_relative_to(TASK)
    frozen.append({"path":p.relative_to(TASK).as_posix(),"expected":h,"actual":sha(p)})
check("all_111_author_frozen_members_hash_verified",len(frozen)==111 and all(f["actual"]==f["expected"] for f in frozen))
check("frozen_author_control_hashes_exact",sha(BATCH / "author-audit.json")=="a2b03ceb4e2ac3d2c4bc062f32cd8dcbac73b68bc0799802e886365eed6f3345" and sha(BATCH / "root-copy-plan.json")=="69972187996b6f673479bdfb3fa4cbefa831cd6b50bbdce1d54665b07d9d812a" and sha(BATCH / "SHA256SUMS.txt")=="e02c356dcefe9c702277a7e28231619f6d51eddd1cb35dca22097a8fbe47bc73")
author=load(BATCH / "author-audit.json")
check("two_author_failed_attempts_retained_not_erased",len(author["retained_failed_attempts"])==2 and [f["exit_code"] for f in author["retained_failed_attempts"]]==[1,1] and (BATCH / "original-compile-exit.txt.before-cache-layout-fix").read_text().strip()=="1" and (BATCH / "stage2-header-exit.txt.before-raw-fix").read_text().strip()=="1" and all((BATCH / f["evidence"]).exists() for f in author["retained_failed_attempts"]),author["retained_failed_attempts"])
result={"checks":checks,"targets":targets,"frozen_manifest_members":frozen,"cross_module_core_closure":sorted(reached),"Base_helpers":[g["name"] for g in base_helpers],"actual_Stage1_records":len(graph),"Jet_source_records":28,"Jet_generated_records":generated,"actual_Stage2_counts":{kind:sum(f["kind"]==kind for f in facts) for kind in ["decl","ref","command"]},"header":header}
(HERE / "reconstruction-report.json").write_text(json.dumps(result,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
print("Independent Jet reconstruction PASS: original cross-module proof closure, header/diagnostic/ref splices, seven exact stages and 111 frozen hashes.")
