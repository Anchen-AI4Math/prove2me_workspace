#!/usr/bin/env python3
"""Certify isolated context source34 and four providers from EXISTING evidence.

Never starts Lean or a network request. Preparations write only new validation
manifests/group snapshot source; exact frozen generation inputs remain unchanged.
"""
from __future__ import annotations

import argparse
from datetime import datetime
import hashlib
import json
from pathlib import Path

import generate_namespace_context_providers as gen
import generate_platform_provider_bundles as producer
import preflight_staged_module as runner
import validate_shared_source_snapshot as shared
import validate_provider_bundle as ordinary
from certify_command_emission_probe import checked_expr, normalized
from provider_source_subset_cache_windows import _drive_case_pair, validate_provider_source_subset_cache
from prepare_fast_provider_snapshot import OLD_RESOLVER, FAST_RESOLVER, validate_requests
from rewrite_ast_imports import external_import_union, import_edits
from skeleton_subtract import declaration_edits
from span_edits import apply_edits
from validate_ast_facts import validate_facts

TASK, ROOT, V, DEST = gen.TASK, gen.ROOT, gen.V, gen.DEST
SELF = Path(__file__).resolve()
BATCH = DEST/"namespace-context"
SOURCE_CERT = DEST/"source-snapshot/source34-validation.json"
GROUP = DEST/"generated-snapshot"
STD3 = {"propext","Classical.choice","Quot.sound"}


def sha(path):return gen.sha(path)
def read(path):return gen.read(path)
def rel(path):return gen.task_relative(path)


def fail(condition,message):
    if condition:raise ValueError(message)


def file(value):
    p=Path(value)
    if not p.is_absolute():p=TASK/p
    p=p.resolve()
    fail(not p.is_relative_to(TASK.resolve()) or not p.is_file(),"Missing/outside mission evidence: "+str(value))
    return p


def implementation_pins():
    return {rel(p):sha(p) for p in [SELF,Path(gen.__file__),Path(producer.__file__),
        TASK/"scripts/prepare_fast_provider_snapshot.py",TASK/"scripts/certify_command_emission_probe.py",
        TASK/"scripts/validate_shared_source_snapshot.py",TASK/"scripts/preflight_staged_module.py",
        TASK/"scripts/provider_source_subset_cache_windows.py"]}


def write_exact(path,document):
    raw=(json.dumps(document,indent=2,ensure_ascii=False)+"\n").encode("utf-8")
    if path.exists():
        fail(read(path)!=document,"Existing evidence/manifest differs; preserve it before replacement: "+str(path))
    else:
        path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(raw)


def written_bytes(text,existing):
    data=existing.read_bytes()
    fail(b"\r" in data.replace(b"\r\n",b""),"Bare CR in snapshot source")
    crlf=b"\r\n" in data
    fail(crlf and b"\n" in data.replace(b"\r\n",b""),"Mixed snapshot line endings")
    return text.replace("\n","\r\n").encode() if crlf else text.encode()


def render_group(requests,modules,output):
    core=(V/"TypeOnlyTheoremSnapshotCore.inc").read_text(encoding="utf-8")
    fail(producer.PROVIDER_EXPORTER.count(OLD_RESOLVER)!=1,"Frozen resolver anchor changed")
    exporter=producer.PROVIDER_EXPORTER.replace(OLD_RESOLVER,FAST_RESOLVER,1)
    anchor='    let row := Json.mkObj [\n'
    fail(exporter.count(anchor)!=1,"Source/exporter Std3 guard anchor changed")
    exporter=exporter.replace(anchor,'''    unless axiomNames.all (fun n => n == "propext" || n == "Classical.choice" || n == "Quot.sound") do
      throwError "Source-fast CI contains nonstandard axioms: {name}"
'''+anchor,1)
    return ("import Lean\n"+"".join("import "+m+"\n" for m in modules)+"\n"+core.rstrip()+"\n\n"+exporter
        +"\nopen PiExponentProviderSnapshot\n\ndef providerRequests : Array ProviderRequest := #[\n"
        +",\n".join(producer.render_request(x) for x in requests)+"\n  ]\n\nrun_meta do\n"
        +"  exportProviderSnapshotJsonl providerRequests "+producer.lean_string(producer.workspace_relative(output))+"\n")


def setup():
    runner.validate_runtime()
    g=gen.readonly_generator()
    captured=[];old=gen.write
    try:
        gen.write=lambda p,x:captured.append((p,x))
        overlay_path,overlay=gen.context_overlay(g)
    finally:gen.write=old
    fail(len(captured)!=1 or read(overlay_path)!=overlay,"Exact AST context overlay differs from fresh authority")
    report=read(DEST/"generation-report.json")
    fail(report["input_hashes"]!=g.input_hashes or report.get("lean_started") or report.get("api_used"),"Context generation inputs/flags changed")
    fail([x["source_module"] for x in report["generated"]]!=gen.MODULES,"Context stage must contain exactly the fixed four modules")
    results={}
    for module in gen.MODULES:
        fail(bool(g.module_name_risk(module)),"Unsupported fresh namespace/name/private boundary: "+module)
        stem=g.platform_module(module).split(".")[-1]
        mp=BATCH/"Definitions"/(stem+".manifest.json");m=read(mp)
        fail(m!=next(x for x in report["generated"] if x["source_module"]==module),"Manifest differs from frozen generation report")
        for p,h in m["input_hashes"].items():fail(sha(file(p))!=h,"Context generation pin changed: "+p)
        for key,hkey in [("source","source_sha256"),("original_source","original_source_sha256"),("facts","facts_sha256"),("output","output_sha256")]:
            fail(sha(ROOT/m[key])!=m[hkey],"Context bundle lineage hash changed: "+key)
        fail(m.get("renames") or m.get("elaboration_only_helpers") or m.get("kept_local_instances"),"Only public atomic ordinary contexts supported")
        selected=g.artifact_plan["definition_bundles"][module]["units"]
        fail(m["selected_units"]!=selected,"Selected commands differ from process-local context plan")
        for k in selected:
            u=g.units[k]
            fail(len(u["graph_names"])!=1 or u["private"] or u["deprivate"] or u["is_instance_command"] or u["is_local_instance"],"Complex/private/multi-CI provider unsupported")
            ordinary.verify_fact_command(ROOT/m["facts"],u["start"]["offset"],g.graph[u["graph_names"][0]]["kind"])
        raw=(ROOT/m["source"]).read_bytes()
        validate_facts(ROOT/m["source"],g._module_facts(module),m["source_sha256"])
        imports=sorted(set(external_import_union(module,g.imports)+[g.platform_module(x) for x in g.artifact_plan["definition_bundles"][module]["imports"]]))
        fail(m["imports"]!=imports,"Imports do not equal real context-overlay closure")
        edits=declaration_edits(g.modules[module]["units"],{g.units[k]["start"]["offset"] for k in selected})
        edits+=import_edits(g.imports["modules"][module]["imports"],imports)
        records=[{"start":x.start,"end":x.end,"reason":x.reason,"replacement":x.replacement.decode()} for x in edits]
        fail(m["edits"]!=records or (ROOT/m["output"]).read_bytes()!=apply_edits(raw,edits,m["source_sha256"]),"Exact independent AST bundle byte reconstruction differs")
        requests=g.snapshot_requests(module,False);generated=g.snapshot_requests(module,True)
        validate_requests(requests,module);validate_requests(generated,m["platform_module"])
        sd=BATCH/"snapshots"/stem;doc=read(sd/"snapshot-requests.json")
        fail(doc!={"original":requests,"generated":generated},"Snapshot request domain differs from actual command Graph")
        bindings=gen.request_catalog_binding(g,requests,generated)
        fail(read(file(m["source_catalog_bindings"]))!=bindings or sha(file(m["source_catalog_bindings"]))!=m["source_catalog_bindings_sha256"],"Complete6148 owner row binding differs")
        core=(V/"TypeOnlyTheoremSnapshotCore.inc").read_text(encoding="utf-8")
        comparison=read(sd/"snapshot-comparison-plan.json")
        for generated_flag,name,out in [(False,"SnapshotOriginal.lean","original.jsonl"),(True,"SnapshotGenerated.lean","generated.jsonl")]:
            path=sd/name;req=generated if generated_flag else requests;owner=m["platform_module"] if generated_flag else module
            expected=producer.render_snapshot(core,owner,req,sd/out)
            key="generated_exporter_sha256" if generated_flag else "original_exporter_sha256"
            fail(path.read_bytes()!=written_bytes(expected,path) or sha(path)!=comparison[key],"Frozen per-module snapshot source differs")
        results[module]={"manifest":mp,"data":m,"snapshot_dir":sd,"original":requests,"generated":generated}
    return g,results


def match_dependencies(left,right):
    fail(len(left)!=len(right),"Actual OLean dependency domains differ")
    for a,b in zip(left,right,strict=True):
        def canonical(d):
            keys=set(d)
            if keys=={"module","path","resolved_search_root","sha256"}:
                digest=d["sha256"]
            elif keys in [{"module","path","resolved_search_root","sha256_before"},
                          {"module","path","resolved_search_root","sha256_before","sha256_after","stable_during_compile"}]:
                digest=d["sha256_before"]
                if "sha256_after" in d:
                    fail(d["sha256_after"] is not None or d["stable_during_compile"] is not None,"Manifest OLean placeholders unexpectedly populated")
            else:raise ValueError("Unknown actual OLean witness schema")
            return {"module":d["module"],"path":d["path"],"resolved_search_root":d["resolved_search_root"],"sha256":digest}
        x=canonical(a);y=canonical(b)
        for key in ["path","resolved_search_root"]:x[key],y[key]=_drive_case_pair(x[key],y[key])
        fail(x!=y,"OLean evidence differs outside narrow drive-letter case: "+str(a.get("module")))


def record(source,manifest,mode,module,root):
    m=read(manifest)
    fail(runner.certified_imports(source,m)!=m["imports"],"Exact imports differ")
    runner.verify_manifest_inputs(m);runner.verify_source_certificate(source,m)
    summary,_=shared.validate_preflight(source,manifest,m)
    r=read(source.with_suffix(".lean.preflight.json"))
    fail(r["source"]!=rel(source) or r["manifest"]!=rel(manifest) or r["module_root"]!=rel(root)
         or r["mode"]!=mode or r["actual_module_identity"]!=module,"Actual preflight identity/path/mode differs")
    fail(r["source_certificate"]!=runner.verify_source_certificate(source,m),"Preflight exact source certificate differs from current bytes")
    runtime,*_=runner.validate_runtime()
    roots=runner.effective_search_path(runtime["environment"]["LEAN_PATH"])
    fail([str(p) for p in roots]!=r["effective_lean_path"],"Current ordered runtime search path changed")
    current=runner.dependency_certificates(m["imports"],roots,{module})
    before=[{k:d[k] for k in ["module","path","resolved_search_root","sha256_before"]} for d in r["dependency_oleans"]]
    now=[{k:d[k] for k in ["module","path","resolved_search_root","sha256_before"]} for d in current]
    match_dependencies(before,now)
    if m.get("actual_import_oleans") is not None:match_dependencies(m["actual_import_oleans"],current)
    if mode=="emit-olean":
        expected=V/"staged-build/lib/lean"/Path(*module.split(".")).with_suffix(".olean")
        fail(file(r["output_olean"])!=expected.resolve() or sha(expected)!=r["output_olean_sha256"],"Actual emitted provider OLean differs")
    else:fail(r["output_olean"] is not None or r["output_olean_sha256"] is not None,"Unexpected OLean emission from snapshot")
    return {"summary":summary,"record":rel(source.with_suffix(".lean.preflight.json")),
        "record_sha256":sha(source.with_suffix(".lean.preflight.json")),"data":r}


def rows(path,requests,preflight):
    data=[json.loads(l) for l in path.read_bytes().splitlines() if l.strip()]
    fail(len(data)!=len(requests),"Actual CI row count differs from exact request domain")
    r=preflight["data"];finished=datetime.fromisoformat(r["at_utc"]).timestamp()
    fail(not finished-r["seconds"]-2<=path.stat().st_mtime<=finished+2,"Snapshot JSONL is outside the actual preflight write window")
    for row,req in zip(data,requests,strict=True):
        fail(set(row)!={"axioms","closedType","closedValue","commandUnit","declGraphRowSha256","declGraphSha256","envKind","kindMetadata","levelParams","module","resolvedName","resolvedUserName","resolvedViaPrivateUserNameAndModuleOwner","schemaVersion","sourceGraphName","sourceWasPrivate","type","value"},"Actual public CI row schema differs")
        fail(row["schemaVersion"]!=1 or row["sourceGraphName"]!=req["source_graph_name"] or row["resolvedName"]!=req["expected_public_name"]
            or row["resolvedUserName"]!=req["expected_user_name"] or row["module"]!=req["expected_module"] or row["envKind"]!=req["expected_kind"]
            or row["commandUnit"]!=req["command_unit"] or row["declGraphSha256"]!=req["decl_graph_sha256"] or row["declGraphRowSha256"]!=req["decl_graph_row_sha256"]
            or row["sourceWasPrivate"] is not False or row["resolvedViaPrivateUserNameAndModuleOwner"] is not False or row["closedType"] is not True,"Actual public CI identity/module/closedness differs")
        levels=row["levelParams"]
        fail(not isinstance(levels,list) or any(not isinstance(x,str) for x in levels) or len(set(levels))!=len(levels),"Invalid universe binder domain")
        checked_expr(row["type"],set(levels))
        fail(not isinstance(row["axioms"],list) or any(not isinstance(x,str) for x in row["axioms"]) or not set(row["axioms"])<=STD3,"Actual CI axioms outside Std3")
        if row["envKind"]=="theorem":
            fail(row["value"] is not None or row["closedValue"] is not None or row["kindMetadata"]!={"proofValueExported":False},"Theorem proof values must remain null")
        elif row["envKind"]=="def":
            fail(row["value"] is None or row["closedValue"] is not True or row["kindMetadata"]!={"safety":"Lean.DefinitionSafety.safe","valueExported":True},"Ordinary safe Def value is missing")
            checked_expr(row["value"],set(levels))
        else:raise ValueError("Complex/structural/private actual CI unsupported")
    return data


def source_certificate(g,results):
    folder=DEST/"source-snapshot";source=folder/"ContextSourceSnapshot.lean";mp=folder/"source-imports.json";m=read(mp)
    req=[x for module in gen.MODULES for x in results[module]["original"]]
    fail(m["requests"]!=req or len(req)!=34,"Source certificate domain must be exact34")
    fail(source.read_bytes()!=written_bytes(render_group(req,gen.MODULES,folder/"source.jsonl"),source),"Exact source34 exporter reconstruction differs")
    fail(read(file(m["source_request_bindings"]))!=dict(gen.request_catalog_binding(g,req,req),purpose="exact source-only original public CI snapshot; generated provider comparison remains required"),"Source34 exact6148 catalog binding differs")
    fail(sha(file(m["source_request_bindings"]))!=m["source_request_bindings_sha256"],"Source34 bindings SHA changed")
    pf=record(source,mp,"modecheck","ContextSourceSnapshot",folder)
    actual=rows(folder/"source.jsonl",req,pf)
    certificate={"schema_version":1,"artifact_kind":"context-source34-kernel-certificate","validated":True,
        "partial":True,"platform_ready":False,"usable_as_full_source_certificate":False,"source_version":875,
        "source_module_count":4,"row_count":34,"provided_names":[x["sourceGraphName"] for x in actual],
        "source_jsonl":rel(folder/"source.jsonl"),"source_jsonl_sha256":sha(folder/"source.jsonl"),
        "source_exporter_sha256":sha(source),"source_manifest_sha256":sha(mp),"preflight":pf,
        "owner_catalog":rel(gen.CATALOG),"owner_catalog_sha256":sha(gen.CATALOG),"owner_count_metadata_only":6148,
        "decl_graph_sha256":g.graph_sha,"input_hashes":m["input_hashes"],"implementation_hashes":implementation_pins(),
        "closed_kernel_types":True,"ordinary_def_values_complete":True,"theorem_values_null":True,"Std3_only":True,
        "generated_kernel_comparison_required":True,"submission_ready":False}
    return certificate,actual


def source_cache(g,results):
    certificate,actual=source_certificate(g,results)
    fail(not SOURCE_CERT.is_file() or read(SOURCE_CERT)!=certificate,"Source34 certificate is missing/stale; certify exact existing source evidence first")
    return certificate,actual


def bundle_manifest(result):
    m=result["data"];stem=m["platform_module"].split(".")[-1]
    document={k:m[k] for k in ["output","output_sha256","source","source_sha256","original_source","original_source_sha256","imports","input_hashes"]}
    document["runtime_sha256"]=sha(V/"lean-runtime.json");document["input_hashes"]=dict(document["input_hashes"])
    document["input_hashes"][rel(result["manifest"])]=sha(result["manifest"])
    return BATCH/"validation"/stem/"b.json",document


def bundle_record(result):
    mp,expected=bundle_manifest(result)
    fail(read(mp)!=expected,"Compact actual bundle manifest differs")
    m=result["data"]
    return record(ROOT/m["output"],mp,"emit-olean",m["platform_module"],BATCH)


def degree_provider():
    module="OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree"
    result=ordinary.structural_check("all-shared-safe-leaves",module,"verification/providers-complete-preview")
    fast=__import__("prepare_fast_provider_snapshot").checked_fast_generated_snapshot(result)
    p=V/"providers-complete-preview/all-shared-safe-leaves/validation"/Path(result["manifest"]).name.removesuffix(".manifest.json")/"provider-validation-fast.json"
    cert=read(p);fail(cert.get("validated") is not True,"PolynomialFrameDegree actual interface certificate missing")
    for evidence in cert["preflights"]:
        rp=file(evidence["record"]);r=read(rp)
        fail(sha(rp)!=evidence["record_sha256"],"Degree provider record changed")
        s=file(r["source"]);mp=file(r["manifest"])
        record(s,mp,r["mode"],r["actual_module_identity"],file(r["source"]).parents[1] if r["mode"]=="emit-olean" else s.parent)
    req=read(TASK/result["snapshot_dir"] / "snapshot-requests.json")
    source=validate_provider_source_subset_cache(V/"shared-source-snapshot/provider-subset/provider-subset-validation.json",req["original"])
    comparison=ordinary.compare_snapshots(result,[],source,"provider-source-subset",fast)
    fail(comparison!=cert["snapshot_comparison"],"Degree provider exact source/generated interface comparison changed")
    bundle=next(x for x in cert["preflights"] if x["role"]=="provider-bundle")
    return {"certificate":rel(p),"certificate_sha256":sha(p),"output_olean":bundle["output_olean"],"output_olean_sha256":bundle["output_olean_sha256"]}


def generated_group(g,results,prepare=False):
    source_cert,_=source_cache(g,results)
    preflights={m:bundle_record(results[m]) for m in gen.MODULES}
    external=degree_provider()
    req=[x for m in gen.MODULES for x in results[m]["generated"]]
    modules=[results[m]["data"]["platform_module"] for m in gen.MODULES]
    source,output,mp=GROUP/"SnapshotGeneratedContextFast.lean",GROUP/"generated.jsonl",GROUP/"gi.json"
    text=render_group(req,modules,output)
    if prepare:
        if source.with_suffix(".lean.preflight.json").exists() or output.exists():
            fail(not source.is_file() or source.read_bytes()!=written_bytes(text,source),"Existing generated group evidence/source differs")
        elif source.exists():fail(source.read_bytes()!=written_bytes(text,source),"Preserve changed generated group source before replacement")
        else:source.parent.mkdir(parents=True,exist_ok=True);source.write_bytes(text.replace("\n","\r\n").encode())
    fail(not source.is_file() or source.read_bytes()!=written_bytes(text,source),"Generated group exporter byte reconstruction differs")
    runtime,runtime_sha,*_=runner.validate_runtime()
    deps=runner.dependency_certificates(["Lean",*modules],runner.effective_search_path(runtime["environment"]["LEAN_PATH"]),{"SnapshotGeneratedContextFast"})
    for d,m in zip(deps[1:],gen.MODULES,strict=True):
        pf=preflights[m]["data"]
        fail(Path(d["path"]).resolve()!=file(pf["output_olean"]) or d["sha256_before"]!=pf["output_olean_sha256"],"Generated group is not importing actual current emitted context provider")
    pins=dict(g.input_hashes);pins.update(implementation_pins());pins[rel(SOURCE_CERT)]=sha(SOURCE_CERT)
    pins[external["certificate"]]=external["certificate_sha256"]
    for pf in preflights.values():
        for p in [file(pf["record"]),file(pf["data"]["manifest"]),file(pf["data"]["output_olean"])]:pins[rel(p)]=sha(p)
    document={"output":producer.workspace_relative(source),"output_sha256":sha(source),"imports":["Lean",*modules],
        "runtime_sha256":runtime_sha,"input_hashes":pins,"actual_import_oleans":deps,"requests":req,
        "source34_certificate":rel(SOURCE_CERT),"source34_certificate_sha256":sha(SOURCE_CERT),
        "expected_jsonl":rel(output),"partial":True,"validated":False,"submission_ready":False}
    if prepare:write_exact(mp,document)
    else:
        existing=read(mp);lhs=dict(existing);rhs=dict(document);lhs.pop("actual_import_oleans");rhs.pop("actual_import_oleans")
        fail(lhs!=rhs,"Generated group manifest/input bindings differ")
        match_dependencies(existing["actual_import_oleans"],deps)
    return source,mp,output,req,preflights,external


def certify_generated(g,results,write=True):
    source,mp,output,req,bundles,external=generated_group(g,results)
    pf=record(source,mp,"modecheck","SnapshotGeneratedContextFast",GROUP)
    actual=rows(output,req,pf)
    source_cert,original=source_cache(g,results)
    comparisons=[]
    for old,new in zip(original,actual,strict=True):
        fail(old["sourceGraphName"]!=new["sourceGraphName"] or old["envKind"]!=new["envKind"] or old["kindMetadata"]!=new["kindMetadata"]
             or set(old["axioms"])!=set(new["axioms"]),"Source/generated kind/safety/axiom/name domain differs")
        for field in ["type"]+(["value"] if old["envKind"]=="def" else []):
            left=normalized(old[field],{n:i for i,n in enumerate(old["levelParams"])},{})
            right=normalized(new[field],{n:i for i,n in enumerate(new["levelParams"])},{})
            fail(len(old["levelParams"])!=len(new["levelParams"]) or left!=right,"Exact structural kernel "+field+" differs: "+old["sourceGraphName"])
        comparisons.append({"name":old["sourceGraphName"],"type_equal":True,"definition_value_equal":old["envKind"]=="def","Std3_equal":True})
    certificates={}
    for module in gen.MODULES:
        r=results[module];names={x["source_graph_name"] for x in r["generated"]}
        cert={"schema_version":1,"artifact_kind":"namespace-context-provider-kernel-certificate","source_module":module,
            "platform_module":r["data"]["platform_module"],"validated":True,"preview_only":True,"submission_ready":False,
            "provider_source_sha256":r["data"]["output_sha256"],"manifest":rel(r["manifest"]),"manifest_sha256":sha(r["manifest"]),
            "source34_certificate":rel(SOURCE_CERT),"source34_certificate_sha256":sha(SOURCE_CERT),"source_scope_partial":True,
            "bundle_preflight":bundles[module],"generated_group_preflight":pf,"generated_group_jsonl_sha256":sha(output),
            "comparisons":[x for x in comparisons if x["name"] in names],"external_provider":external,
            "context_overlay_sha256":sha(DEST/"context-overlay.json"),"implementation_hashes":implementation_pins(),
            "closed_types":True,"full_def_values_equal":True,"theorem_values_null":True,"Std3_only":True,"proof_axioms":"Std3"}
        path=BATCH/"validation"/r["data"]["platform_module"].split(".")[-1]/"context-provider-validation.json"
        if write:write_exact(path,cert)
        else:fail(not path.is_file() or read(path)!=cert,"Context provider certificate differs from full live revalidation")
        certificates[module]={"path":rel(path),"sha256":sha(path),"data":cert}
    return {"validated":True,"providers":4,"compared_names":34,"source_partial":True,"submission_ready":False,
            "certificates":certificates}


def validate_context_provider(module):
    """Read-only publisher entry point: recheck all actual source/group evidence."""
    fail(module not in gen.MODULES,"Only the four exact isolated context providers are supported")
    g,results=setup()
    validation=certify_generated(g,results,write=False)
    result=results[module]
    return {"module":module,"manifest":result["manifest"],"provider_source":ROOT/result["data"]["output"],
            "source_bytes":(ROOT/result["data"]["output"]).read_bytes(),
            "certificate":validation["certificates"][module],"validated":True,"submission_ready":False}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    mode=parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check-only",action="store_true")
    mode.add_argument("--certify-source",action="store_true")
    mode.add_argument("--prepare-bundle",action="store_true")
    mode.add_argument("--prepare-generated-group",action="store_true")
    mode.add_argument("--certify-existing",action="store_true")
    parser.add_argument("--module")
    args=parser.parse_args()
    try:
        g,results=setup()
        if args.check_only:out={"supported":True,"providers":4,"source_requests":34,"validated":False,"submission_ready":False}
        elif args.certify_source:
            certificate,_=source_certificate(g,results);write_exact(SOURCE_CERT,certificate)
            out={"validated":True,"certificate":rel(SOURCE_CERT),"certificate_sha256":sha(SOURCE_CERT),"partial":True,"rows":34,"submission_ready":False}
        elif args.prepare_bundle:
            module=next((m for m in gen.MODULES if args.module in {m,m.split(".")[-1]}),None)
            fail(module is None,"--module must identify one of the exact four context providers")
            source_cache(g,results)
            if module==gen.MODULES[0]:degree_provider()
            for dependency in g.artifact_plan["definition_bundles"][module]["imports"]:
                if dependency in results:bundle_record(results[dependency])
            mp,document=bundle_manifest(results[module]);write_exact(mp,document)
            out={"manifest":rel(mp),"manifest_sha256":sha(mp),"source":rel(ROOT/results[module]["data"]["output"]),"root":rel(BATCH),"mode":"emit-olean","validated":False}
        elif args.prepare_generated_group:
            source,mp,*_=generated_group(g,results,prepare=True)
            out={"source":rel(source),"source_sha256":sha(source),"manifest":rel(mp),"manifest_sha256":sha(mp),"root":rel(GROUP),"requests":34,"validated":False}
        else:out=certify_generated(g,results)
        print(json.dumps(out,indent=2))
    except (ValueError,KeyError,FileNotFoundError,TypeError,StopIteration) as error:
        print(json.dumps({"validated":False,"status":"rejected","error":str(error)}));raise SystemExit(2)


if __name__=="__main__":main()
