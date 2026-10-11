"""Certify the isolated FormalLog18 provider and exact equation API evidence.

No Lean process or network request is started. Certification writes only new
companion certificates; publisher entry points replay all evidence read-only.
The source certificate is partial and never authenticates the full6148 domain.
"""
from __future__ import annotations

import argparse
from datetime import datetime
import json
from pathlib import Path

import generate_formal_log_truncation_provider as gen
import generate_equation_provenance_probe as equation
import validate_namespace_context_providers as context
from certify_command_emission_probe import checked_expr, normalized
from prepare_fast_provider_snapshot import validate_requests

TASK, ROOT, V, DEST, BATCH = gen.TASK, gen.ROOT, gen.V, gen.DEST, gen.BATCH
MODULE, STEM = gen.MODULE, gen.STEM
SELF = Path(__file__).resolve()
SOURCE_CERT = DEST / "source-snapshot/source18-validation.json"
PROVIDER_CERT = BATCH / "validation" / STEM / "provider-validation.json"
EQUATION_CERT = DEST / "equation-provenance/equation-validation.json"
sha, read, rel, fail, file = context.sha, context.read, context.rel, context.fail, context.file
FROZEN_GENERATOR_SHA = "2a43e21fb7483d2c34243af3758887f09ac876403e90eebbfb7c86b9702469ec"
SOURCE_COMMIT = "adc7f1241b42e322a6451854ab7e4b4c146bf78a"


def implementation_pins():
    return {rel(p): sha(p) for p in [SELF, Path(gen.__file__), Path(equation.__file__),
        Path(context.__file__), TASK / "scripts/certify_command_emission_probe.py",
        TASK / "scripts/provider_source_subset_cache_windows.py",
        TASK / "scripts/replay_fast_provider_snapshot_windows.py",
        TASK / "scripts/preflight_staged_module.py", TASK / "scripts/validate_shared_source_snapshot.py"]}


def exact_source(source, expected):
    fail(source.read_bytes() != context.written_bytes(expected, source),
         "Exporter source differs from exact frozen reconstruction: " + rel(source))


def setup():
    fail(sha(Path(gen.__file__)) != FROZEN_GENERATOR_SHA, "Frozen FormalLog producer changed")
    g, report, mp, m = gen.load_stage()
    dependencies = gen.context_evidence(g)
    fail(dependencies != m["dependency_certificates"], "Actual dependency context replay differs")
    fail(g.input_hashes != m["input_hashes"], "Current producer inputs differ from exact frozen manifest")
    fail(report.get("lean_started") is not False or report.get("api_used") is not False
         or report.get("source_full6148_certificate_claimed") is not False, "Unsafe generation report flags")
    fail(m["source_module"] != MODULE or m["platform_module"] != "Definitions." + STEM
         or m["source_commit"] != SOURCE_COMMIT, "Wrong exact FormalLog source/provider/commit")
    for key, digest in [("source", "source_sha256"), ("original_source", "original_source_sha256"),
                        ("facts", "facts_sha256"), ("output", "output_sha256")]:
        fail(sha(ROOT / m[key]) != m[digest], "FormalLog lineage hash changed: " + key)
    for flag in ["source_skeleton_preserved", "full_definition_proofs_preserved",
                 "independent_byte_reconstruction_equal", "source_unchanged"]:
        fail(m.get(flag) is not True, "Source skeleton/proof reconstruction flag missing: " + flag)
    fail(gen.collisions(g, m) != m["actual_import_closure_collision_check"], "Whole import public name closure differs")
    original, generated = g.snapshot_requests(MODULE, False), g.snapshot_requests(MODULE, True)
    validate_requests(original, MODULE); validate_requests(generated, m["platform_module"])
    fail(len(original) != 18 or len(generated) != 18, "Only exact18 public FormalLog CIs supported")
    folder = BATCH / "snapshots" / STEM
    fail(read(folder / "snapshot-requests.json") != {"original": original, "generated": generated},
         "Frozen exact18 request domain differs")
    bp = file(m["source_catalog_bindings"])
    fail(read(bp) != gen.context.request_catalog_binding(g, original, generated)
         or sha(bp) != m["source_catalog_bindings_sha256"], "Exact6148 metadata owner binding differs")
    fail(rel(bp) != rel(folder / "source-catalog-bindings.json"), "Unexpected source catalog binding path")
    return g, report, mp, m, original, generated, bp


def written_during(path, pf):
    record = pf["data"]
    finished = datetime.fromisoformat(record["at_utc"]).timestamp()
    fail(not finished - record["seconds"] - 2 <= path.stat().st_mtime <= finished + 2,
         "Actual exporter output is outside retained preflight write window: " + rel(path))


def checked_api_ci(ci, kind, name, owner_module, own_module):
    fail(set(ci) != {"actualName", "userName", "levelParams", "kind", "type", "value", "owner", "axioms"},
         "Equation API CI schema differs")
    fail(ci["actualName"] != name or ci["userName"] != name or ci["kind"] != kind, "Exact API CI name/kind differs")
    owner = ci["owner"]
    if owner.get("kind") == "ImportedModule":
        fail(set(owner) != {"kind", "module", "index"} or owner["module"] != owner_module
             or type(owner["index"]) is not int or owner["index"] < 0, "Imported API CI ownership differs")
    elif kind == "theorem" and owner.get("kind") == "OwnModule":
        fail(owner != {"kind": "OwnModule", "module": own_module}, "Lazy equation actual OwnModule ownership differs")
    else:
        raise ValueError("Unsupported API CI actual ownership")
    levels = ci["levelParams"]
    fail(not isinstance(levels, list) or any(not isinstance(x, str) for x in levels)
         or len(set(levels)) != len(levels), "Invalid equation API universe domain")
    checked_expr(ci["type"], set(levels))
    fail(not isinstance(ci["axioms"], list) or any(not isinstance(x, str) for x in ci["axioms"])
         or not set(ci["axioms"]) <= context.STD3, "Equation API nonstandard axioms")
    if kind == "def":
        fail(ci["value"] is None, "API primary lacks full definition value")
        checked_expr(ci["value"], set(levels))
    else:
        fail(ci["value"] is not None, "Equation theorem proof value must remain null")


def api_output(path, pf, side, module, primary_row):
    written_during(path, pf)
    d = read(path)
    fail(set(d) != {"side", "expectedModule", "primaryBinding", "getEqnsForReturnedSome", "actualEquationNames",
                    "equations", "unfolding", "probeMainModule", "theoremProofValuesExported"}, "Equation API output schema differs")
    fail(d["side"] != side or d["expectedModule"] != module
         or d["probeMainModule"] != pf["data"]["actual_module_identity"]
         or d["theoremProofValuesExported"] is not False or d["getEqnsForReturnedSome"] is not True
         or d["actualEquationNames"] != [equation.REQUIRED] or len(d["equations"]) != 1
         or d["unfolding"] is not None, "Exact formal equation API getter domain differs")
    ci = d["primaryBinding"]
    checked_api_ci(ci, "def", equation.PRIMARY, module, d["probeMainModule"])
    fail(primary_row["resolvedName"] != equation.PRIMARY or primary_row["envKind"] != "def", "Primary is outside safe full-CI snapshot")
    for api_key, row_key in [("levelParams", "levelParams"), ("type", "type"), ("value", "value")]:
        fail(ci[api_key] != primary_row[row_key], "Equation API primary differs from same-side safe CI: " + api_key)
    fail(set(ci["axioms"]) != set(primary_row["axioms"]), "API primary axioms differ from same-side safe CI")
    e = d["equations"][0]
    fail(set(e) != {"getter", "inversePrimary", "CI"} or e["getter"] != "Lean.Meta.getEqnsFor?"
         or e["inversePrimary"] != equation.PRIMARY, "Exact getEqnsFor?/isEqnThm? inverse relation differs")
    checked_api_ci(e["CI"], "theorem", d["actualEquationNames"][0], module, d["probeMainModule"])
    return d


def source_certificate(state):
    g, report, mp, m, original, generated, bp = state
    folder = DEST / "source-snapshot"
    source, output, sm = folder / "SourceFormalLogTruncationSnapshot.lean", folder / "source.jsonl", folder / "si.json"
    text = context.render_group(original, [MODULE], output).replace("import Lean\n", "import Lean\nimport Lean.Meta.Eqns\n", 1)
    eq_path = DEST / "equation-provenance/original.json"
    text += equation.PROBE + ("\nrun_meta do\n  PiExponentEquationProvenanceProbe.exportEquationSnapshot `" + equation.PRIMARY
        + " " + json.dumps(MODULE) + " " + json.dumps(gen.provider.workspace_relative(eq_path)) + " \"original\"\n")
    exact_source(source, text)
    expected = gen.snapshot_manifest(g, source, ["Lean", "Lean.Meta.Eqns", MODULE], original, output, bp, {rel(mp): sha(mp)})
    expected.update(expected_equation_api_json=rel(eq_path), equation_api_primary=equation.PRIMARY)
    actual_manifest = read(sm)
    assert_manifest(actual_manifest, expected)
    pf = context.record(source, sm, "modecheck", source.stem, folder)
    actual = context.rows(output, original, pf)
    primary = next(x for x in actual if x["sourceGraphName"] == equation.PRIMARY)
    api = api_output(eq_path, pf, "original", MODULE, primary)
    cert = {"schema_version": 1, "artifact_kind": "formal-log-source18-kernel-certificate", "validated": True,
        "partial": True, "platform_ready": False, "usable_as_full_source_certificate": False,
        "source_version": 875, "source_commit": SOURCE_COMMIT, "row_count": 18,
        "provided_names": [x["sourceGraphName"] for x in actual], "source_jsonl": rel(output), "source_jsonl_sha256": sha(output),
        "source_exporter_sha256": sha(source), "source_manifest_sha256": sha(sm), "preflight": pf,
        "owner_catalog": rel(gen.context.CATALOG), "owner_catalog_sha256": sha(gen.context.CATALOG), "owner_count_metadata_only": 6148,
        "decl_graph_sha256": g.graph_sha, "input_hashes": actual_manifest["input_hashes"], "implementation_hashes": implementation_pins(),
        "closed_kernel_types": True, "ordinary_def_values_complete": True, "theorem_values_null": True, "Std3_only": True,
        "equation_api_output": rel(eq_path), "equation_api_output_sha256": sha(eq_path),
        "actual_equation_names": api["actualEquationNames"], "api_and_source18_same_actual_preflight": True,
        "generated_kernel_comparison_required": True, "submission_ready": False}
    return cert, actual, api


def assert_manifest(actual, expected):
    a, b = dict(actual), dict(expected)
    left, right = a.pop("actual_import_oleans"), b.pop("actual_import_oleans")
    fail(a != b, "Exact snapshot manifest reconstruction differs")
    context.match_dependencies(left, right)


def source_cache(state):
    cert, rows, api = source_certificate(state)
    fail(not SOURCE_CERT.is_file() or read(SOURCE_CERT) != cert, "Fresh source18 companion certificate missing/stale")
    return cert, rows, api


def bundle_record(state):
    _, _, mp, m, *_ = state
    b = BATCH / "validation" / STEM / "b.json"
    expected = {k: m[k] for k in ["output", "output_sha256", "source", "source_sha256", "original_source", "original_source_sha256", "imports", "input_hashes"]}
    expected["input_hashes"] = dict(expected["input_hashes"], **{rel(mp): sha(mp)})
    expected["runtime_sha256"] = sha(V / "lean-runtime.json")
    fail(read(b) != expected, "Exact emitted bundle manifest reconstruction differs")
    return context.record(ROOT / m["output"], b, "emit-olean", m["platform_module"], BATCH), b


def compare_rows(original, generated):
    comparisons = []
    for old, new in zip(original, generated, strict=True):
        fail(old["sourceGraphName"] != new["sourceGraphName"] or old["envKind"] != new["envKind"]
             or old["kindMetadata"] != new["kindMetadata"] or set(old["axioms"]) != set(new["axioms"])
             or len(old["levelParams"]) != len(new["levelParams"]), "Source/generated exact CI domain/kind/metadata/Std3 differs")
        for field in ["type"] + (["value"] if old["envKind"] == "def" else []):
            fail(normalized(old[field], {p:i for i,p in enumerate(old["levelParams"])}, {})
                 != normalized(new[field], {p:i for i,p in enumerate(new["levelParams"])}, {}),
                 "Exact structural kernel " + field + " differs: " + old["sourceGraphName"])
        comparisons.append({"name": old["sourceGraphName"], "type_equal": True,
                            "definition_value_equal": old["envKind"] == "def", "Std3_equal": True})
    return comparisons


def provider_certificate(state):
    g, _, mp, m, _, requests, bp = state
    _, original, source_api = source_cache(state)
    bundle, b = bundle_record(state)
    folder = DEST / "generated-snapshot"
    source, output, gm = folder / "SnapshotGeneratedFormalLogFast.lean", folder / "generated.jsonl", folder / "gi.json"
    exact_source(source, context.render_group(requests, [m["platform_module"]], output))
    pins = {rel(mp): sha(mp), rel(b): sha(b), bundle["record"]: bundle["record_sha256"]}
    expected = gen.snapshot_manifest(g, source, ["Lean", m["platform_module"]], requests, output, bp, pins)
    assert_manifest(read(gm), expected)
    pf = context.record(source, gm, "modecheck", source.stem, folder)
    provider_import = next(x for x in pf["data"]["dependency_oleans"] if x["module"] == m["platform_module"])
    fail(provider_import["sha256_before"] != bundle["data"]["output_olean_sha256"], "Generated CI snapshot imports a different provider OLean")
    generated = context.rows(output, requests, pf)
    comparisons = compare_rows(original, generated)
    cert = {"schema_version": 1, "artifact_kind": "formal-log-provider-kernel-certificate", "source_module": MODULE,
        "platform_module": m["platform_module"], "validated": True, "preview_only": True, "submission_ready": False,
        "provider_source_sha256": m["output_sha256"], "manifest": rel(mp), "manifest_sha256": sha(mp),
        "source18_certificate": rel(SOURCE_CERT), "source18_certificate_sha256": sha(SOURCE_CERT), "source_scope_partial": True,
        "bundle_preflight": bundle, "generated_snapshot_preflight": pf, "generated_jsonl": rel(output), "generated_jsonl_sha256": sha(output),
        "comparisons": comparisons, "row_count": 18, "source_commit": SOURCE_COMMIT,
        "whole_import_closure": m["actual_import_closure_collision_check"], "dependency_certificates": m["dependency_certificates"],
        "implementation_hashes": implementation_pins(), "closed_types": True, "full_def_values_equal": True,
        "theorem_values_null": True, "Std3_only": True, "proof_axioms": "Std3"}
    return cert, generated, source_api, bundle, b, pins


def equation_certificate(state, provider_result):
    g, _, mp, m, _, _, bp = state
    provider_cert, rows, source_api, bundle, b, pins = provider_result
    folder = DEST / "equation-provenance"
    source, output, em = folder / "ProbeGeneratedFormalLog.lean", folder / "generated.json", folder / "ei.json"
    core = (V / "TypeOnlyTheoremSnapshotCore.inc").read_text(encoding="utf-8")
    exact_source(source, "import Lean\nimport Lean.Meta.Eqns\nimport " + m["platform_module"] + "\n\n" + core + equation.PROBE
        + "\nrun_meta do\n  PiExponentEquationProvenanceProbe.exportEquationSnapshot `" + equation.PRIMARY + " "
        + json.dumps(m["platform_module"]) + " " + json.dumps(gen.provider.workspace_relative(output)) + " \"generated\"\n")
    # Frozen preparation is intercepted to verify the equation plan and compiler
    # manifest byte-for-byte without rewriting historical preparation material.
    captured = []
    old_save, old_source = gen.save, gen.source_bytes
    try:
        gen.save = lambda p, d: captured.append((p, d))
        gen.source_bytes = exact_source
        gen.equation_stage(g, m, bp, bundle, pins)
    finally:
        gen.save, gen.source_bytes = old_save, old_source
    fail(len(captured) != 2, "Unexpected equation stage evidence domain")
    for p, expected in captured:
        if p == em: assert_manifest(read(p), expected)
        else: fail(read(p) != expected, "Frozen exact equation plan differs")
    pf = context.record(source, em, "modecheck", source.stem, folder)
    imported = next(x for x in pf["data"]["dependency_oleans"] if x["module"] == m["platform_module"])
    fail(imported["sha256_before"] != bundle["data"]["output_olean_sha256"], "Equation probe imports a different provider OLean")
    primary = next(x for x in rows if x["sourceGraphName"] == equation.PRIMARY)
    generated_api = api_output(output, pf, "generated", m["platform_module"], primary)
    source_ci, generated_ci = source_api["equations"][0]["CI"], generated_api["equations"][0]["CI"]
    fail(len(source_ci["levelParams"]) != len(generated_ci["levelParams"])
         or set(source_ci["axioms"]) != set(generated_ci["axioms"]), "Equation universe arity or axioms differ")
    fail(normalized(source_ci["type"], {p:i for i,p in enumerate(source_ci["levelParams"])}, {})
         != normalized(generated_ci["type"], {p:i for i,p in enumerate(generated_ci["levelParams"])}, {}), "Exact API equation kernel type differs")
    return {"schema_version": 1, "artifact_kind": "formal-log-equation-api-kernel-certificate", "validated": True,
        "provider_certificate": rel(PROVIDER_CERT), "provider_certificate_sha256": sha(PROVIDER_CERT),
        "source18_certificate": rel(SOURCE_CERT), "source18_certificate_sha256": sha(SOURCE_CERT),
        "primary_binding": equation.PRIMARY, "required_source_equation": equation.REQUIRED,
        "source_actual_equation_names": source_api["actualEquationNames"], "generated_actual_equation_names": generated_api["actualEquationNames"],
        "getter": "Lean.Meta.getEqnsFor?", "inverse_getter": "Lean.Meta.isEqnThm?", "inverse_primary": equation.PRIMARY,
        "source_actual_owner": source_ci["owner"], "generated_actual_owner": generated_ci["owner"],
        "primary_closed_type_equal": True, "primary_full_safe_def_value_equal": True,
        "equation_closed_type_equal": True, "equation_Std3_equal": True, "theorem_values_null": True,
        "prefix_name_inference": False, "generated_provider_availability_established": True,
        "source_output": rel(DEST / "equation-provenance/original.json"),
        "source_output_sha256": sha(DEST / "equation-provenance/original.json"),
        "generated_output": rel(output), "generated_output_sha256": sha(output), "generated_probe_preflight": pf,
        "source_scope_partial": True, "full6148_closure_established": False,
        "implementation_hashes": implementation_pins(), "submission_ready": False}


def validate_formal_log_provider():
    """Read-only publisher entry point: exact current source/bundle/generated replay."""
    state = setup(); cert, *_ = provider_certificate(state)
    fail(not PROVIDER_CERT.is_file() or read(PROVIDER_CERT) != cert, "FormalLog provider certificate missing/stale")
    m = state[3]; source = ROOT / m["output"]
    return {"module": MODULE, "manifest": state[2], "provider_source": source, "source_bytes": source.read_bytes(),
            "certificate": {"path": rel(PROVIDER_CERT), "sha256": sha(PROVIDER_CERT), "data": cert},
            "validated": True, "submission_ready": False}


def validate_equation_certificate():
    """Read-only equation consumer: replay provider and both fresh formal API outputs."""
    state = setup(); result = provider_certificate(state)
    fail(read(PROVIDER_CERT) != result[0], "Provider certificate differs from exact readonly replay")
    cert = equation_certificate(state, result)
    fail(not EQUATION_CERT.is_file() or read(EQUATION_CERT) != cert, "Equation API certificate missing/stale")
    return {"path": rel(EQUATION_CERT), "sha256": sha(EQUATION_CERT), "data": cert}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--certify-source", action="store_true")
    mode.add_argument("--certify-existing", action="store_true")
    mode.add_argument("--validate-only", action="store_true")
    mode.add_argument("--validate-equation-only", action="store_true")
    args = parser.parse_args()
    try:
        if args.validate_only:
            result = validate_formal_log_provider(); out = {k:v for k,v in result.items() if k not in {"source_bytes", "provider_source", "manifest", "certificate"}}
            out["certificate"] = result["certificate"]["path"]
        elif args.validate_equation_only:
            result = validate_equation_certificate(); out = {"validated": True, "certificate": result["path"], "sha256": result["sha256"]}
        else:
            state = setup()
            if args.certify_source:
                cert, *_ = source_certificate(state); path = SOURCE_CERT
            else:
                result = provider_certificate(state)
                context.write_exact(PROVIDER_CERT, result[0])
                cert = equation_certificate(state, result); path = EQUATION_CERT
            context.write_exact(path, cert)
            out = {"validated": True, "certificate": rel(path), "sha256": sha(path), "partial_source": True, "submission_ready": False}
        print(json.dumps(out, indent=2))
    except (ValueError, KeyError, FileNotFoundError, TypeError, StopIteration) as error:
        print(json.dumps({"validated": False, "status": "rejected", "error": str(error)})); raise SystemExit(2)


if __name__ == "__main__": main()
