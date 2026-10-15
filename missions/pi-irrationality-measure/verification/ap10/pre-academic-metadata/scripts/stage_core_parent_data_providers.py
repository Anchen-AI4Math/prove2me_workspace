"""Pure AP10 module-sized data staging; exact source Defs, no proof lemmas."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import stage_weighted_simplex_domains_providers as ap9
import preflight_staged_module as runner

TASK, ROOT, V, CORE = ap9.TASK, ap9.ROOT, ap9.V, ap9.CORE
SELF = Path(__file__).resolve()
COMMIT = ap9.COMMIT
SOURCE_SNAPSHOT, GENERATED_SNAPSHOT = ap9.SOURCE_SNAPSHOT, ap9.GENERATED_SNAPSHOT
SOURCE_JSON, GENERATED_JSON = ap9.SOURCE_JSON, ap9.GENERATED_JSON
PREFIX = "OAI.PiExponent."
CORE_IMPORTS = TASK / "port/lean/OAI/NumberTheory/PiExponent/CoreImports.lean"
PARAM_CERT = V / "providers-complete-preview/all-shared-safe-leaves/snapshots/Def_OAI_NumberTheory_PiExponent_Approximation_Parameters/provider-validation-structural.json"
ADM_CERT = V / "ap2/complete-validation.json"
CONFIGS = {
    "interpolation": {
        "source_module": "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
        "platform_module": "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_CoreData",
        "source_sha256": "ab84501a2a29cb569118260ffd1adb30ca827936727fa868db0e829cb1bfde38",
        "namespace": "OAI.PiExponent.InterpolationMatrix",
        "short_names": ["exponentVector", "truncatedLog", "monomialImage", "entry", "matrix", "truncatedLogMatrix"],
        "prior": [],
        "mathlib_additions": ["Mathlib.RingTheory.PowerSeries.Log"],
        "title": "Core polynomial data for interpolation matrices",
        "statement": "Define the finite exponent vector, truncated formal logarithm, polynomial image of a monomial, coefficient entry, interpolation matrix, and its truncated-log specialization. The matrix is indexed by the exact weighted row and column domains from the source. These definitions supply the linear algebra data of the conditional determinant argument; no surjectivity claim is included.",
    },
    "arithmetic": {
        "source_module": "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
        "platform_module": "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_MatrixArithmetic_CoreData",
        "source_sha256": "fb2547fa5e853f3f9962729dc5f0e5f39d034f13307212886ddd9ae9541ecb66",
        "namespace": "OAI.PiExponent.MatrixArithmetic",
        "short_names": ["logWeights", "rationalCenters", "truncationOrders", "rowWeightedSum", "meanRowWeight", "selectedMinor"],
        "prior": ["interpolation"],
        "mathlib_additions": ["Mathlib.RingTheory.PowerSeries.Log", "Mathlib.NumberTheory.Zsqrtd.GaussianInt", "Mathlib.NumberTheory.Chebyshev", "Mathlib.LinearAlgebra.Matrix.Determinant.Basic"],
        "title": "Arithmetic data associated with interpolation minors",
        "statement": "For integer numerators and natural denominators, define ceiling-log weights, the associated rational imaginary centers, logarithmic truncation orders, the total weighted row sum and its normalized mean, and a selected square interpolation minor. These exact source definitions supply the quantities appearing in the determinant estimates; no arithmetic lower bound is asserted.",
    },
    "determinant": {
        "source_module": "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
        "platform_module": "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData",
        "source_sha256": "74329150cc64ac655ee0ce56454519170ce15b4b58dfd85ba5a9ab850c740e53",
        "namespace": "OAI.PiExponent.DeterminantContradiction",
        "short_names": ["FixedData", "finiteNumerators", "finiteDenominators", "Row", "Column", "actualMatrix", "actualMinor", "actualMean", "actualRowCount", "lowIndexCount", "collisionRate", "collisionLimit", "GlobalInterpolationStatement", "AnalyticAggregateStatement"],
        "prior": ["interpolation", "arithmetic"],
        "mathlib_additions": ["Mathlib.RingTheory.PowerSeries.Log", "Mathlib.NumberTheory.Zsqrtd.GaussianInt", "Mathlib.NumberTheory.Chebyshev", "Mathlib.LinearAlgebra.Matrix.Determinant.Basic"],
        "title": "Fixed-data interfaces for the determinant contradiction",
        "statement": "Specialize admissible approximation parameters using the source arithmetic and collision constants. Define the associated interpolation matrix, selected minor, weighted row mean, counts and collision rate/limit. Define the global interpolation hypothesis and analytic aggregate hypothesis in their original quantified form. These interfaces state the exact assumptions of the conditional determinant contradiction; neither hypothesis is proved here.",
    },
}

sha, sha_bytes, read, encode, rel, workspace_rel, need = ap9.sha, ap9.sha_bytes, ap9.read, ap9.encode, ap9.rel, ap9.workspace_rel, ap9.need


def config(key):
    c=dict(CONFIGS[key]); c["stage"]=V/"ap10"/key
    c["source"]=TASK/"port/lean"/Path(*c["source_module"].split(".")).with_suffix(".lean")
    c["original"]=TASK/"source/lean"/Path(*c["source_module"].split(".")).with_suffix(".lean")
    c["names"]=[c["namespace"]+"."+n for n in c["short_names"]]
    c["provider_file"]=c["platform_module"].replace(".","/")+".lean"
    return c


def published_bindings():
    """Bind actual published body hashes to certified CI names, not package labels."""
    coverage=read(ap9.COVERAGE); bindings={}; pins={rel(ap9.COVERAGE):sha(ap9.COVERAGE)}; witnesses={}
    records={x["definition_name"]:x for x in coverage["records"]}
    for name,certpath,structural in [
        ("OAI_NumberTheory_PiExponent_Approximation_Parameters",PARAM_CERT,True),
        ("OAI_NumberTheory_PiExponent_Approximation_AdmissibleParameters",ADM_CERT,False)]:
        witness=records[name]; path=TASK/witness["publication_record"]; published=read(path)
        need(sha(path)==witness["publication_record_sha256"],"Published parameter record changed")
        body=published["publish_intent"]["payload"]["definition"].encode()
        need(body==published["target_readback"]["body"]["definition"].encode()
             and sha_bytes(body)==witness["literal_source_sha256"],"Published parameter literal body differs")
        cert=read(certpath)
        need(cert["validated"] is True and sha(certpath)==published["publish_intent"]["validation_sha256"],"Published CI certificate binding changed")
        if structural:
            need(cert["provider_source_sha256"]==sha_bytes(body) and cert["whole_atomic_graph_ci_coverage_equal"] is True,"Parameter structural domain/source differs")
            module=cert["platform_module"]; names=cert["compared_names"]
        else:
            source_module="OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters"
            selected=cert["provider_manifests"][source_module]
            need(selected["source_sha256"]==sha_bytes(body) and cert["full_provider_ci_domains_checked"] is True,"Admissible actual58CI/source differs")
            module=selected["platform_module"]; names=selected["declarations"]
        bindings.update({n:module for n in names}); pins[rel(path)]=sha(path);pins[rel(certpath)]=sha(certpath)
        witnesses[module]={"publication_record":rel(path),"publication_record_sha256":sha(path),"literal_source_sha256":sha_bytes(body),"actual_ci_certificate":rel(certpath),"actual_ci_certificate_sha256":sha(certpath),"declared_names":names}
    # These two plain definitions have literal source AST commands in the
    # published bodies; unlike structure projections, they need no name inference.
    for defname,module_name,symbol,start,end in [
        ("OAI_NumberTheory_PiExponent_Approximation_Arithmetic","OAI.NumberTheory.PiExponent.Approximation.Arithmetic",PREFIX+"Arithmetic.lcmConstant",453,522),
        ("OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CollisionConstant","OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",PREFIX+"DeterminantContradiction.collisionConstant",463,522)]:
        witness=records[defname]; path=TASK/witness["publication_record"]; published=read(path); body=published["publish_intent"]["payload"]["definition"].encode()
        source=TASK/"port/lean"/Path(*module_name.split(".")).with_suffix(".lean")
        astmod=next(x for x in read(ap9.AST)["modules"] if x["module"]==module_name)
        unit=next(x for x in astmod["units"] if symbol in x["graph_names"])
        command=source.read_bytes()[unit["start"]["offset"]:unit["end"]["offset"]]
        need(sha(path)==witness["publication_record_sha256"] and body==published["target_readback"]["body"]["definition"].encode()
             and sha_bytes(body)==witness["literal_source_sha256"]
             and body.replace(b"\r\n",b"\n").count(command.replace(b"\r\n",b"\n"))==1,
             "Actual published constant declaration differs")
        module="Definitions.Def_"+defname;bindings[symbol]=module;pins[rel(path)]=sha(path);pins[rel(source)]=sha(source)
        witnesses[module]={"publication_record":rel(path),"publication_record_sha256":sha(path),"literal_source_sha256":sha_bytes(body),"literal_ast_command":unit,"declared_names":[symbol]}
    for key in ap9.CONFIGS:
        ap9.check_only(key); c=ap9.config(key); p=c["stage"] / "preparation.json"; body=c["stage"] / c["provider_file"]
        bindings.update({n:c["platform_module"] for n in c["names"]});pins[rel(p)]=sha(p);pins[rel(body)]=sha(body)
        witnesses[c["platform_module"]]={"prepared_provider":rel(body),"source_sha256":sha(body),"exact_ast_preparation":rel(p),"exact_ast_preparation_sha256":sha(p),"declared_names":c["names"],"requires_actual_compile_before_import":True}
    return bindings,pins,witnesses


def authority(c):
    raw=c["source"].read_bytes(); need(sha_bytes(raw)==c["source_sha256"],"Pinned AP10 source changed")
    mod=next(x for x in read(ap9.AST)["modules"] if x["module"]==c["source_module"])
    scopes=next(x for x in read(ap9.SCOPES)["modules"] if x["source"]==c["source_module"].replace(".","/")+".lean")
    graph={x["name"]:x for x in map(json.loads,ap9.GRAPH.read_text(encoding="utf-8").splitlines())}
    owners={x["source_name"]:x for x in read(ap9.OWNERS)["owners"]}
    original=c["original"].read_bytes().replace(b"\r\n",b"\n"); result=[]
    for name in c["names"]:
        u=next(x for x in mod["units"] if name in x["graph_names"])
        s=next(x for x in scopes["declarations"] if x["verified_name"]==name)
        a,b=u["start"]["offset"],u["end"]["offset"]; command=raw[a:b]
        need(mod["source_sha256"]==c["source_sha256"] and scopes["source_sha256"]==c["source_sha256"]
             and u["graph_names"]==[name] and u["graph_kinds"]==["def"] and u["privateTok"] is None
             and not u["is_instance_command"] and not u["is_local_instance"]
             and s["namespace"]==c["namespace"] and all(x["kind"]=="namespace" for x in s["scope_stack"])
             and original.count(command.replace(b"\r\n",b"\n"))==1,"Exact original public Def AST/context differs")
        o=owners[name]
        need(o["source_module"]==c["source_module"] and o["source_sha256"]==c["source_sha256"]
             and o["command_unit"]==c["source_module"]+":"+str(a)
             and o["unit_start_offset"]==a and o["unit_end_offset"]==b and not o["source_private"]
             and o["graph_kind"]=="def","Actual source owner differs")
        contexts=[raw[x["range"]["start"]["offset"]:x["range"]["end"]["offset"]].decode() for x in s["context_commands"]]
        need(all(x["syntaxKind"]=="Lean.Parser.Command.open" for x in s["context_commands"]),"Unsupported source context")
        result.append({"name":name,"start":a,"end":b,"source_lines":[u["start"]["line"],u["end"]["line"]],"sha256":sha_bytes(command),"bytes":command,"ast":u,"scope":s,"owner":o,"graph":graph[name],"contexts":contexts})
    return result


def stage_files(key):
    c=config(key); units=authority(c);available,pins,witnesses=published_bindings()
    for prior in c["prior"]:
        pc=config(prior); p=pc["stage"]/"preparation.json"; body=pc["stage"]/pc["provider_file"]
        need(body.is_file() and read(p)["provided_names"]==pc["names"],"Prior exact AP10 stage not prepared")
        available.update({n:pc["platform_module"] for n in pc["names"]});pins[rel(p)]=sha(p);pins[rel(body)]=sha(body)
        witnesses[pc["platform_module"]]={"prepared_provider":rel(body),"source_sha256":sha(body),"exact_ast_preparation":rel(p),"exact_ast_preparation_sha256":sha(p),"declared_names":pc["names"],"requires_actual_compile_before_import":True}
    own=set(c["names"]);dependencies=sorted({n for u in units for n in u["graph"]["typeDeps"]+u["graph"]["valueDeps"]}-own)
    missing=set(dependencies)-set(available);need(not missing,"Missing actual project dependency declarations: "+str(sorted(missing)))
    modules=sorted({available[n] for n in dependencies});mathlib=[x.split()[1] for x in CORE_IMPORTS.read_text(encoding="utf-8").splitlines() if x.startswith("import ")]
    mathlib=sorted(set(mathlib+c["mathlib_additions"]));c["imports"]=mathlib+modules
    # Preserve real source namespace and opens. All selected contexts are opens,
    # and there are no source section variables to lift for these data commands.
    contexts=[]
    for u in units:
        for text in u["contexts"]:
            if text not in contexts:contexts.append(text)
    prefix=("".join("import "+m+"\n" for m in c["imports"])+"\nnamespace "+c["namespace"]+"\n\n"+"\n".join(contexts)+"\n\n").encode()
    provider=prefix+b"\n\n".join(u["bytes"] for u in units)+("\n\nend "+c["namespace"]+"\n").encode()
    need(b"sorry" not in provider and b"theorem " not in provider,"AP10 data package contains a proof lemma")
    outputs={c["provider_file"]:provider,SOURCE_SNAPSHOT:ap9.snapshot(c,units,False),GENERATED_SNAPSHOT:ap9.snapshot(c,units,True)}
    pins.update({rel(p):sha(p) for p in [SELF,Path(ap9.__file__),c["source"],c["original"],ap9.AST,ap9.SCOPES,ap9.GRAPH,ap9.OWNERS,CORE,ap9.RUNTIME,ap9.PREFLIGHT,ap9.CONTEXT,CORE_IMPORTS]})
    plans=[(c["provider_file"],c["imports"],"emit-olean",c["platform_module"]),(SOURCE_SNAPSHOT,["Lean",c["source_module"]],"modecheck","SourceSnapshot"),(GENERATED_SNAPSHOT,["Lean",c["platform_module"]],"modecheck","GeneratedSnapshot")];commands=[]
    for i,(filename,imports,mode,module) in enumerate(plans,1):
        outputs[f"c{i}.json"]=encode({"schema_version":1,"artifact_kind":"ap10-core-data-bounded-compiler-manifest","output":workspace_rel(c["stage"]/filename),"output_sha256":sha_bytes(outputs[filename]),"imports":imports,"input_hashes":pins,"runtime_sha256":sha(ap9.RUNTIME),"mode":mode,"emit_olean":mode=="emit-olean","timeout_seconds":300,"expected_actual_module_identity":module,"validated":False,"submission_ready":False})
        commands.append("python scripts/preflight_staged_module.py ap10/"+key+"/"+filename+" --root ap10/"+key+" --imports-manifest ap10/"+key+f"/c{i}.json --timeout-seconds 300"+(" --emit-olean" if mode=="emit-olean" else ""))
    url=f"https://github.com/openai/math/blob/{COMMIT}/lean/"+c["source_module"].replace(".","/")+".lean"
    outputs["academic-metadata.json"]=encode({"definition_title":c["title"],"natural_language_statement":c["statement"],"source":"OpenAI math, commit "+COMMIT+": "+url,"source_commit":COMMIT,"source_url":url,"tags":["linear-algebra","number-theory","openai-pi-exponent-017"]})
    outputs["preparation.json"]=encode({"schema_version":1,"artifact_kind":"ap10-core-data-provider-preparation","source_commit":COMMIT,"source_module":c["source_module"],"platform_module":c["platform_module"],"source_path":rel(c["source"]),"source_sha256":sha(c["source"]),"original_source_path":rel(c["original"]),"original_source_sha256":sha(c["original"]),"provided_names":c["names"],"provider_file":c["provider_file"],"exact_source_units":[{k:v for k,v in u.items() if k!="bytes"} for u in units],"source_context_commands":contexts,"imports":c["imports"],"project_dependencies":dependencies,"actual_dependency_bindings":{n:available[n] for n in dependencies},"dependency_provider_evidence":{m:witnesses[m] for m in modules},"outside_dependency_closure_complete":True,"mathlib_import_basis":{"core_imports_source":rel(CORE_IMPORTS),"core_imports_sha256":sha(CORE_IMPORTS),"core_original_external_imports":mathlib,"blanket_Mathlib_import":False},"input_hashes":pins,"order":[p[0] for p in plans],"commands":commands,"snapshot_outputs":{SOURCE_SNAPSHOT:rel(c["stage"]/SOURCE_JSON),GENERATED_SNAPSHOT:rel(c["stage"]/GENERATED_JSON)},"expected_provider_olean":"verification/staged-build/lib/lean/"+c["platform_module"].replace(".","/")+".olean","Lean_started":False,"API_used":False,"validated":False,"submission_ready":False,"proposal_status":"Draft"})
    return outputs


def check_only(key):
    c=config(key);generated=stage_files(key)
    for name,raw in generated.items():need((c["stage"]/name).is_file() and (c["stage"]/name).read_bytes()==raw,"Exact AP10 stage reconstruction differs: "+name)
    for i,filename in enumerate([c["provider_file"],SOURCE_SNAPSHOT,GENERATED_SNAPSHOT],1):
        m=read(c["stage"]/f"c{i}.json");runner.verify_manifest_inputs(m);runner.verify_source_certificate(c["stage"]/filename,m)
    return {"stage":rel(c["stage"]),"checked_files":len(generated),"provided_names":c["names"],"all_hashes_match":True,"Lean_started":False,"API_used":False,"validated":False}


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument("--provider",choices=list(CONFIGS),required=True)
    modes=parser.add_mutually_exclusive_group(required=True);modes.add_argument("--prepare",action="store_true");modes.add_argument("--check-only",action="store_true");args=parser.parse_args()
    if args.prepare:
        c=config(args.provider)
        for name,raw in stage_files(args.provider).items():
            p=c["stage"]/name
            if p.exists():need(p.read_bytes()==raw,"Refusing to overwrite frozen AP10 stage: "+name)
            else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(raw)
    print(json.dumps(check_only(args.provider),indent=2))


if __name__=="__main__":main()
