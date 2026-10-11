"""Supplemental 13-CI source/generated exporter and complete provider consumer.

The 49 structural CIs retain the frozen complete ConstantInfo comparison.
Nine remaining Admissible declarations and four WeightSeparation definitions
receive the same schema-v2 type, full definition value and Std3 comparison.
No Lean process or API call is started.
"""
from __future__ import annotations
import argparse
import copy
import json
from pathlib import Path

import stage_admissible_provider as stage
import generate_shared_source_snapshot as base
import generate_structural_kernel_source_snapshot as source_gen
import structural_kernel_snapshot as kernel
import certify_structural_kernel_source_snapshot as source_certifier
import structural_provider_certificate_evidence_windows as windows
import validate_provider_bundle as ordinary

TASK, DEST = stage.TASK, stage.DEST
V = TASK / "verification"
EXTRAS = DEST / "e"
CATALOG = V / "shared-source-snapshot/complete-source/CompleteSource875.owners.json"
CORE = V / "StructuralKernelSnapshotCore.inc"


def read(path):
    return json.loads(path.read_bytes())


def require(condition, message):
    if not condition:
        raise ValueError(message)


def provider_paths(module):
    stem = "Def_" + module.replace(".", "_")
    manifest = DEST / stage.BATCH / "Definitions" / (stem + ".manifest.json")
    return manifest, read(manifest)


def provider_imports(module, write=False):
    path, manifest = provider_paths(module)
    imports = EXTRAS / ("weight-imports.json" if module == stage.WEIGHT else "admissible-imports.json")
    doc = dict(schema_version=2, artifact_kind="complete-provider-bundle-imports",
        runtime_sha256=base.sha_file(base.RUNTIME), input_hashes={},
        source=manifest["source"], source_sha256=manifest["source_sha256"],
        original_source=manifest["original_source"], original_source_sha256=manifest["original_source_sha256"],
        output=manifest["output"], output_sha256=manifest["output_sha256"], imports=manifest["imports"])
    if write:
        base.write_json(imports, doc)
    else:
        require(read(imports) == doc, "Provider imports manifest differs")
    return dict(source=(ordinary.ROOT / manifest["output"]).relative_to(V).as_posix(),
        root=DEST.joinpath(stage.BATCH).relative_to(V).as_posix(), manifest=imports,
        module=manifest["platform_module"], imports=manifest["imports"], mode="emit-olean", role="provider-bundle")


def owners():
    catalog = read(CATALOG)
    require(catalog["source_version"] == 875, "Full 875-owner catalog required")
    require(base.sha_file(source_gen.UNIT_PLAN) == catalog["unit_plan_sha256"]
        and base.sha_file(source_gen.ARTIFACT_PLAN) == catalog["artifact_plan_sha256"], "Frozen source plans differ")
    all_owners = {r["source_name"]: r for r in catalog["owners"]}
    # Family order is checked by root rather than inferred from dictionary order.
    families = read(source_gen.CATALOG)["families"]
    structural_names = set(next(f["source_names"] for f in families if f["source_module"] == stage.ADMISSIBLE))
    selected = []
    for module in stage.MODULES:
        path, manifest = provider_paths(module)
        request_path = DEST / stage.BATCH / "snapshots" / path.name.removesuffix(".manifest.json") / "snapshot-requests.json"
        for req in read(request_path)["original"]:
            name = req["source_graph_name"]
            if module == stage.ADMISSIBLE and name in structural_names:
                continue
            row = copy.deepcopy(all_owners[name])
            require(row["source_module"] == module and row["command_unit"] in manifest["selected_units"]
                and row["source_private"] is False and row["graph_kind"] in ("def", "theorem"), "Unsupported extra owner")
            require(req["decl_graph_row_sha256"] == row["decl_graph_row_sha256"]
                and req["command_unit"] == row["command_unit"] and req["expected_module"] == module,
                "Supplement owner/request differs")
            row["family_root"] = name
            selected.append(row)
    require(len(selected) == 13 and len({r["source_name"] for r in selected}) == 13, "Complete extra domain must have 13 CIs")
    graph, graph_sha = base.load_decl_graph()
    extraction = read(base.EXTRACTION_STATE)
    raw_owners = base.collect_complete_source_owners(base.unit_index(read(source_gen.UNIT_PLAN)), graph)
    for row in selected:
        actual = base.validate_owner(raw_owners[row["source_name"]], graph, graph_sha, extraction)
        require(all(actual[k] == v for k, v in row.items() if k != "family_root"), "Owner authentication differs")
    return selected, graph, graph_sha


def render(records, imports, output):
    return ("".join("import " + module + "\n" for module in imports) + "\n"
        + CORE.read_text(encoding="utf-8").rstrip() + "\n\nopen PiExponentStructuralKernelSnapshot\n\n"
        + "def extraRequests : Array StructuralRequest := #[\n"
        + ",\n".join(source_gen.request_lean(r) for r in records) + "\n]\n\nrun_meta do\n"
        + "  exportStructuralSnapshotJsonl extraRequests " + json.dumps(base.workspace_relative(output)) + "\n")


def expected_exporter(generated=False, bind=False):
    records, _, _ = owners()
    originals = copy.deepcopy(records)
    manifests = {m:provider_paths(m)[1] for m in stage.MODULES}
    if generated:
        for row in records:
            row["source_module"] = manifests[row["source_module"]]["platform_module"]
    stem = "ExtraGenerated" if generated else "ExtraSource"
    lean, jsonl, manifest_path = (EXTRAS / (stem + suffix) for suffix in (".lean", ".jsonl", ".imports.json"))
    imports = ["Lean"] + (sorted(m["platform_module"] for m in manifests.values()) if generated else ["OAI.NumberTheory.PiExponent.Main"])
    text = render(records, imports, jsonl)
    pins = [Path(__file__),Path(stage.__file__),CORE,CATALOG,base.DECL_GRAPH,base.RUNTIME,
        source_gen.UNIT_PLAN,source_gen.ARTIFACT_PLAN,Path(kernel.__file__),Path(source_certifier.__file__)]
    for module in stage.MODULES:
        path, m = provider_paths(module)
        pins += [path,ordinary.ROOT / m["output"],ordinary.ROOT / m["source"],ordinary.ROOT / m["facts"]]
    doc = dict(schema_version=2,artifact_kind="supplemental-complete-ConstantInfo-exporter",
        output=base.workspace_relative(lean),output_sha256=base.sha_bytes(text.encode()),
        imports=imports,runtime_sha256=base.sha_file(base.RUNTIME),
        input_hashes={base.task_relative(p):base.sha_file(p) for p in pins},
        snapshot_jsonl=base.workspace_relative(jsonl),expected_rows=13,
        source_only=not generated,source_commit=ordinary.COMMIT,partial=True,platform_ready=False)
    if generated and bind:
        deps = []
        for module in stage.MODULES:
            pstage = provider_imports(module)
            e = ordinary.verify_preflight_record(pstage)
            olean = TASK / e["output_olean"]
            relative = Path(*e["actual_module_identity"].split(".")).with_suffix(".olean")
            root = olean
            for _ in relative.parts:
                root = root.parent
            deps.append(dict(module=e["actual_module_identity"],path=str(olean.resolve()),
                sha256=e["output_olean_sha256"],resolved_search_root=str(root.resolve())))
            for path in [TASK / e["record"],TASK / e["log"],olean,pstage["manifest"]]:
                doc["input_hashes"][base.task_relative(path)] = base.sha_file(path)
        doc["actual_import_oleans"] = deps
    return dict(source=lean,manifest=manifest_path,jsonl=jsonl,text=text,document=doc,records=records,originals=originals)


def prepare():
    stage.configure()
    EXTRAS.mkdir(parents=True,exist_ok=True)
    for module in stage.MODULES:
        provider_imports(module,write=True)
    for generated in [False,True]:
        r = expected_exporter(generated)
        base.atomic_write(r["source"],r["text"].encode())
        if not generated:
            base.write_json(r["manifest"],r["document"])
    return cheap_check()


def exporter_stage(r):
    return dict(source=r["source"].relative_to(V).as_posix(),root=EXTRAS.relative_to(V).as_posix(),
        manifest=r["manifest"],module=r["source"].stem,imports=r["document"]["imports"],
        mode="modecheck",role="supplemental-generated" if r["source"].stem.endswith("Generated") else "supplemental-source")


def cheap_check():
    stage.configure()
    result = []
    for module in stage.MODULES:
        ps = provider_imports(module)
        path, manifest = provider_paths(module)
        original, output = ordinary.ROOT / manifest["source"],ordinary.ROOT / manifest["output"]
        stage.structural._reconstruct_provider_source(manifest,original,output)
        ordinary.derive_expected_imports(manifest,DEST / stage.BATCH,path.name.removesuffix(".manifest.json"),DEST)
        require(ordinary.exact_import_header(output.read_bytes(),manifest["imports"]),"Exact provider header differs")
        result.append("python scripts/preflight_staged_module.py " + ps["source"] + " --root " + ps["root"]
            + " --imports-manifest " + ps["manifest"].relative_to(V).as_posix() + " --emit-olean --timeout-seconds 300")
    source = expected_exporter(False)
    require(read(source["manifest"]) == source["document"] and source["source"].read_bytes() == source["text"].encode(),"Source supplemental exporter changed")
    source_stage = exporter_stage(source)
    result.insert(0,"python scripts/preflight_staged_module.py " + source_stage["source"] + " --root " + source_stage["root"]
        + " --imports-manifest " + source_stage["manifest"].relative_to(V).as_posix() + " --timeout-seconds 300")
    generated = expected_exporter(True)
    require(generated["source"].read_bytes() == generated["text"].encode(),"Generated supplemental exporter changed")
    paths = [str(p.resolve()) for p in DEST.rglob("*") if p.is_file()]
    require(max(map(len,paths)) < 240,"Strict Windows path budget exceeded")
    return dict(cheap_bindings_checked=True,extra_rows=13,structural_rows=49,provider_rows=58,
        max_path_length=max(map(len,paths)),preflight_commands=result,
        lean_started=False,api_used=False,validated=False)


def bind():
    cheap_check()
    r = expected_exporter(True,bind=True)
    base.write_json(r["manifest"],r["document"])
    ps = exporter_stage(r)
    return dict(command="python scripts/preflight_staged_module.py " + ps["source"] + " --root " + ps["root"]
        + " --imports-manifest " + ps["manifest"].relative_to(V).as_posix() + " --timeout-seconds 300")


def certify(replay=False):
    cheap_check()  # Fast schema/byte/import/path checks precede the full source replay.
    kernel.expression_names = source_certifier.expression_names_safe
    records, graph, graph_sha = owners()
    extracted = []
    evidence = []
    for generated in [False,True]:
        r = expected_exporter(generated,bind=generated)
        require(read(r["manifest"]) == r["document"],"Supplement import bindings changed")
        e = ordinary.verify_preflight_record(exporter_stage(r))
        rows = [json.loads(line) for line in r["jsonl"].read_bytes().splitlines() if line.strip()]
        require(len(rows) == 13,"Supplement row domain changed")
        for row, req, owner in zip(rows,r["records"],records,strict=True):
            kernel.validate_row_basic(row,{k:req[k] for k in source_gen.REQUEST_FIELDS},owner,graph,graph_sha,
                expected_module=req["source_module"])
        extracted.append(rows)
        evidence.append(e)
    for old,new in zip(*extracted,strict=True):
        kernel.compare_rows(old,new,old["sourceModule"],new["sourceModule"])
    # Reuse the frozen 49-CI structural validator with its exact authenticated
    # Windows drive-case reconciliation. This reads the existing source74 cert.
    old_basis, old_replay = source_gen.build_basis,stage.structural.replay_source_certificate
    norm, source_norm = {},{}
    source_gen.build_basis = lambda: windows._reconciled_basis(old_basis,norm)
    stage.structural.replay_source_certificate = lambda p: windows._replay_source_certificate_windows(p,source_norm)
    try:
        result = stage.structural.structural_check(stage.ADMISSIBLE)
        if replay:
            certpath = result["snapshot_dir"] / "provider-validation-structural.json"
            before = certpath.read_bytes()
            captured = {}
            old_write = base.write_json
            def capture(path,value):
                require(Path(path).resolve() == certpath.resolve(),"Unexpected structural replay write")
                captured["report"] = value
            base.write_json = capture
            try:
                stage.structural.certify(result,stage.structural.SOURCE_CERTIFICATE)
            finally:
                base.write_json = old_write
            require(captured.get("report") == json.loads(before) and certpath.read_bytes() == before,"Fresh structural report differs")
            structural = json.loads(before)
        else:
            structural = stage.structural.certify(result,stage.structural.SOURCE_CERTIFICATE)
            certpath = TASK / structural["certificate"]
    finally:
        source_gen.build_basis,stage.structural.replay_source_certificate = old_basis,old_replay
    manifests = {m:provider_paths(m) for m in stage.MODULES}
    report = dict(schema_version=1,artifact_kind="complete-admissible-provider-kernel-validation",
        validated=True,partial_source_certificate=True,platform_ready=False,source_commit=ordinary.COMMIT,
        source_structural_rows=49,supplemental_rows=13,admissible_provider_rows=58,weight_provider_rows=4,
        types_equal=True,full_definition_values_equal=True,Std3_only=True,theorem_values_null=True,
        complete_inductive_constructor_recursor_metadata_equal=True,recursor_rules_full_rhs_equal=True,
        full_provider_ci_domains_checked=True,source74_certificate_sha256=base.sha_file(stage.structural.SOURCE_CERTIFICATE),
        structural_certificate=base.task_relative(certpath),structural_certificate_sha256=base.sha_file(certpath),
        source_and_generated_extra_preflights=evidence,
        source_extra_jsonl_sha256=base.sha_file(EXTRAS / "ExtraSource.jsonl"),
        generated_extra_jsonl_sha256=base.sha_file(EXTRAS / "ExtraGenerated.jsonl"),
        provider_manifests={m:dict(path=base.task_relative(p),sha256=base.sha_file(p),
            source_sha256=manifest["output_sha256"],platform_module=manifest["platform_module"],
            declarations=[r["source_name"] for r in records if r["source_module"] == m])
            for m,(p,manifest) in manifests.items()},
        provider_preflights={m:ordinary.verify_preflight_record(provider_imports(m)) for m in stage.MODULES},
        consumer=base.task_relative(Path(__file__)),consumer_sha256=base.sha_file(Path(__file__)),
        windows_catalog_reconciliation=norm,windows_source_reconciliation=source_norm,
        lean_started=False,api_used=False)
    report["provider_manifests"][stage.ADMISSIBLE]["declarations"] = sorted(set(
        report["provider_manifests"][stage.ADMISSIBLE]["declarations"] + structural["compared_names"]))
    path = DEST / "complete-validation.json"
    if replay:
        require(read(path) == report,"Fresh complete provider report differs from stored certificate")
    else:
        base.write_json(path,report)
    return dict(validated=True,certificate=base.task_relative(path),certificate_sha256=base.sha_file(path),
        rows=62,read_only_replay=replay,lean_started=False,api_used=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode",choices=["prepare","check","bind","certify","replay"])
    args = parser.parse_args()
    stage.configure()
    fn = {"prepare":prepare,"check":cheap_check,"bind":bind,"certify":certify,"replay":lambda:certify(True)}[args.mode]
    print(json.dumps(fn(),ensure_ascii=False,indent=2))


if __name__ == "__main__":
    main()
