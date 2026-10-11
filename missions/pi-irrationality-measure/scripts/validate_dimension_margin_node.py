"""Certify Dimension margin from actual four-file Lean evidence; no Lean/API here.

--check-only replays the frozen 875-plan source/AST generator once. After four
strict <=300s preflights, --certify-existing compares exact kernel types,
seven public inline CI types and actual proof references. The saved certificate
can then be checked with --validate-only without rebuilding the graph.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from unittest.mock import patch

import generate_platform_provider_nodes as nodegen
import prepare_dimension_margin_node as prep
import validate_formal_log_node as kernel
import formal_log_node_refs as refs
import validate_namespace_context_providers as context
import validate_standalone_platform_node as standalone

STAGE, TASK, ROOT, V = prep.STAGE, prep.TASK, prep.ROOT, prep.V
SELF = Path(__file__).resolve()
CERT = STAGE / "dimension-margin-validation.json"
sha, read, rel, fail, file = context.sha, context.read, context.rel, context.fail, context.file


def reconstruct(m):
    """Execute original producer with all writes captured; no stage bytes change."""
    n = nodegen.ProviderNodeGenerator()
    fail(n.g.input_hashes != m["input_hashes"], "Current 875-plan input domain differs")
    captured = {}
    def capture_bytes(path, data):
        fail(path.resolve().parent != STAGE or path.name in captured,
             "Unexpected or duplicate generator write")
        captured[path.name] = bytes(data)
        return len(data)
    def capture_text(path, value, encoding=None, errors=None, newline=None):
        return capture_bytes(path, value.encode(encoding or "utf-8", errors or "strict"))
    old_sha = nodegen.sha
    def captured_sha(path):
        p = path.resolve()
        if p.parent == STAGE and p.name in captured:
            return hashlib.sha256(captured[p.name]).hexdigest()
        return old_sha(path)
    class Destination:
        def __truediv__(self, slug):
            fail(slug != "OAI_PiExponent_exists_dimension_margin", "Wrong authority stage slug")
            return STAGE
    with patch.object(nodegen, "DEST", Destination()), \
         patch.object(Path, "write_bytes", capture_bytes), \
         patch.object(Path, "write_text", capture_text), \
         patch.object(Path, "mkdir", lambda *args, **kwargs: None), \
         patch.object(nodegen, "sha", captured_sha):
        result = n.generate(prep.KEY)
    fail((TASK / result["stage"]).resolve() != STAGE.resolve(), "Generated stage differs")
    expected = json.loads(captured.pop("manifest.json"))
    fail(expected != m or set(captured) != set(m["outputs_sha256"]) or len(captured) != 4,
         "Frozen manifest/four-file domain differs from exact source/AST reconstruction")
    for name, data in captured.items():
        fail((STAGE / name).read_bytes() != data or sha(STAGE / name) != m["outputs_sha256"][name],
             "Exact frozen source/AST bytes differ: " + name)
    inventory = n.import_collision_inventory(prep.KEY)
    fail(inventory != m["whole_import_closure_inventory"] or bool(inventory["collisions"]),
         "Whole public import inventory changed/collides")
    target = n.g.units[prep.KEY]
    fail(target["private"] or target["deprivate"] or target["graph_kinds"] != ["theorem"]
         or target["graph_names"] != [m["source_graph_name"]], "Target is not unchanged public theorem")
    for r in m["public_inline_ci_requests"]:
        u = n.g.units[r["source_unit"]]
        fail(u["private"] or u["deprivate"] or u["graph_kinds"] != ["theorem"]
             or r["source_graph_name"] != r["generated_name"]
             or r["source_graph_name"] not in u["graph_names"],
             "Inline request is not unchanged public theorem")
    return n


def preparation():
    prep.check()
    m = read(STAGE / "manifest.json")
    p = read(STAGE / "preparation.json")
    _, definition, base, addon, extended, output, ci, pins, filenames = prep.expected()
    fail(extended.read_bytes() != base.read_bytes() + addon, "WithRefs is not exact prefix/addon")
    fail(p["proof_reference_requests"] != ["solution", *[r["generated_name"] for r in m["public_inline_ci_requests"]]]
         or p["proof_reference_output"] != rel(output) or p["certified_inputs_sha256"] != sha(STAGE / "certified-inputs.json")
         or p["generated_with_refs_prefix_bytes"] != base.stat().st_size,
         "Proof collector/preparation identity differs")
    return m, p, definition, output, filenames


def compiled(m, p, definition, filenames):
    result = {}
    for name in filenames:
        source = STAGE / name
        mp = TASK / p["compile_manifests"][name]["manifest"]
        pf = context.record(source, mp, "modecheck", source.stem, STAGE)
        if name != "SnapshotOriginal.lean":
            dep = next((row for row in pf["data"]["dependency_oleans"]
                        if row["module"] == prep.PLATFORM), None)
            fail(dep is None or dep["sha256_before"] != definition["output_olean_sha256"],
                 "Actual imported Dimension OLean differs")
        result[name] = pf
    return result


def certify():
    m, p, definition, output, filenames = preparation()
    n = reconstruct(m)
    records = compiled(m, p, definition, filenames)
    source_pf = records["SnapshotOriginal.lean"]
    generated_pf = records["SnapshotGeneratedWithRefs.lean"]
    original = kernel.kernel_rows(STAGE / "original-type.json", [m["source_graph_name"]], source_pf)
    generated = kernel.kernel_rows(STAGE / "generated-type.json", [m["theorem_name"], "solution"], generated_pf)
    for row in generated: kernel.same_type(original[0], row)
    source_names = [r["source_graph_name"] for r in m["public_inline_ci_requests"]]
    generated_names = [r["generated_name"] for r in m["public_inline_ci_requests"]]
    old_inline = kernel.kernel_rows(ROOT / m["public_inline_type_json_outputs"]["original"], source_names, source_pf)
    new_inline = kernel.kernel_rows(ROOT / m["public_inline_type_json_outputs"]["generated"], generated_names, generated_pf)
    for left, right in zip(old_inline, new_inline, strict=True): kernel.same_type(left, right)
    for side, pf in (("original", source_pf), ("generated", generated_pf)):
        fail(kernel.kernel_rows(ROOT / m["inline_type_json_outputs"][side], [], pf) != [],
             "Unexpected private CI export")
    audits = {"source": standalone.audit_axioms(file(source_pf["data"]["log"]), m["source_graph_name"]),
              "snapshot_solution": standalone.audit_axioms(file(generated_pf["data"]["log"]), "solution"),
              "exact_solution": standalone.audit_axioms(file(records[Path(m["solution"]).name]["data"]["log"]), "solution")}
    actual = refs.checked_output(STAGE, m, generated_pf, output)
    fail([r["name"] for r in actual] != ["solution", *generated_names]
         or set(actual[0]["axioms"]) != set(audits["snapshot_solution"]),
         "Same-run proof reference/axiom evidence differs")
    allowed = set(definition["provided_names"]) | set(generated_names)
    graph_names = set(n.g.graph)
    ref_audits = []
    for row in actual:
        names = set(row["typeRefs"] + row["valueRefs"])
        fail(m["theorem_name"] in names or "solution" in names or row["name"] in names,
             "Proof uses target stub, itself, or solution")
        project = {x for x in names if x in graph_names or
                   x.startswith(("OAI.", "Definitions.", "Theorems.", "Solutions.", "_private.OAI."))}
        fail(not project <= allowed, "Proof uses unavailable project declarations: " + str(sorted(project - allowed)))
        ref_audits.append({"name": row["name"], "actual_project_refs": sorted(project),
                           "closed_type_and_proof": True, "axioms": row["axioms"],
                           "actual_owner": row["owner"]})
    paths = [STAGE / "original-type.json", STAGE / "generated-type.json", output]
    paths += [ROOT / m[field][side] for field in ("inline_type_json_outputs", "public_inline_type_json_outputs")
              for side in ("original", "generated")]
    pins = {rel(path): sha(path) for path in (SELF, Path(prep.__file__), Path(nodegen.__file__),
            Path(kernel.__file__), Path(refs.__file__), Path(context.__file__), Path(standalone.__file__),
            Path(prep.refs_producer.__file__))}
    return {"schema_version": 1, "artifact_kind": "dimension-margin-proof-node-kernel-certificate",
            "validated": True, "node": prep.KEY, "theorem_name": m["theorem_name"],
            "source_commit": m["source_commit"], "manifest": rel(STAGE / "manifest.json"),
            "manifest_sha256": sha(STAGE / "manifest.json"),
            "frozen_four_files_sha256": m["outputs_sha256"],
            "generated_with_refs": rel(STAGE / "SnapshotGeneratedWithRefs.lean"),
            "generated_with_refs_sha256": sha(STAGE / "SnapshotGeneratedWithRefs.lean"),
            "definition": definition, "child_certificates": [],
            "source_components": m["source_components"],
            "source_command_witness": kernel.source_command_witness(m, n),
            "source_and_AST_reconstructed": True, "public_import_collision_free": True,
            "kernel_types_equal": True, "seven_public_inline_kernel_types_equal": True,
            "theorem_values_null": True, "theorem_proof_values_exported": False,
            "actual_project_reference_coverage_complete": True,
            "allowed_project_names": sorted(allowed), "solution_proof_reference_evidence": ref_audits,
            "Std3_only": True, "axioms": audits, "preflights": records,
            "max_file_seconds": max(x["data"]["seconds"] for x in records.values()),
            "output_json_sha256": {rel(x): sha(x) for x in paths},
            "implementation_hashes": pins, "input_hashes": m["input_hashes"],
            "submission_ready": False, "full_tree_ready": False}


def validate_saved():
    """Fast final gate: source, compilation and certificate pins; no 875 graph."""
    m, p, definition, output, filenames = preparation()
    c = read(CERT)
    fail(c.get("validated") is not True or c.get("definition") != definition
         or c.get("manifest_sha256") != sha(STAGE / "manifest.json")
         or c.get("frozen_four_files_sha256") != m["outputs_sha256"]
         or c.get("generated_with_refs_sha256") != sha(STAGE / "SnapshotGeneratedWithRefs.lean")
         or c.get("submission_ready") is not False, "Saved certificate identity differs")
    for path, expected in c["implementation_hashes"].items():
        fail(sha(file(path)) != expected, "Validation implementation changed: " + path)
    for path, expected in c["output_json_sha256"].items():
        fail(sha(file(path)) != expected, "Kernel evidence changed: " + path)
    records = compiled(m, p, definition, filenames)
    fail(records != c["preflights"], "Retained actual compile evidence differs")
    fail(c["max_file_seconds"] > 300 or c["Std3_only"] is not True
         or c["kernel_types_equal"] is not True or c["seven_public_inline_kernel_types_equal"] is not True
         or c["actual_project_reference_coverage_complete"] is not True,
         "Saved certificate gates incomplete")
    return {"validated": True, "certificate": rel(CERT), "sha256": sha(CERT),
            "max_file_seconds": c["max_file_seconds"], "submission_ready": False}


def main():
    a = argparse.ArgumentParser(description=__doc__)
    mode = a.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check-only", action="store_true")
    mode.add_argument("--certify-existing", action="store_true")
    mode.add_argument("--validate-only", action="store_true")
    args = a.parse_args()
    if args.check_only:
        m, *_ = preparation()
        reconstruct(m)
        result = {"exact_source_AST_and_four_files_checked": True, "validated": False,
                  "submission_ready": False}
    elif args.certify_existing:
        certificate = certify()
        context.write_exact(CERT, certificate)
        result = validate_saved()
    else:
        result = validate_saved()
    print(json.dumps(result, indent=2))


if __name__ == "__main__": main()
