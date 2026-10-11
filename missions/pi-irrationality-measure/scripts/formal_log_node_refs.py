"""Read-only WithRefs source and actual output consumer for FormalLog nodes."""
from __future__ import annotations

import hashlib
from pathlib import Path

import stage_formal_log_base_node as producer
import generate_formal_log_truncation_provider as formal
import validate_namespace_context_providers as context

sha, read, rel, fail = context.sha, context.read, context.rel, context.fail
FROZEN_PRODUCER_SHA = "c21ee20505edcee3ff6b8ae8a8d2ce9a21bf89ac58dbe1b88a5aaf7f00be3bfd"


def checked_preparation(stage):
    fail(sha(Path(producer.__file__)) != FROZEN_PRODUCER_SHA, "Frozen WithRefs producer changed")
    m, p = read(stage / "manifest.json"), read(stage / "preparation.json")
    base, source, mp, output = stage / "SnapshotGenerated.lean", stage / "SnapshotGeneratedWithRefs.lean", stage / "c4.json", stage / "proof-references.json"
    addon = producer.proof_reference_addon(m["public_inline_ci_requests"], output).encode()
    expected = base.read_bytes() + addon
    fail(source.read_bytes() != expected, "WithRefs is not exact original snapshot bytes plus exact narrow exporter")
    fail(p["stage"] != rel(stage) or p["attempt_root"] != rel(stage.parent)
         or p["base_snapshot"] != rel(base) or p["base_snapshot_sha256"] != sha(base)
         or p["generated_with_refs"] != rel(source) or p["generated_with_refs_sha256"] != sha(source)
         or p["generated_with_refs_prefix_bytes"] != base.stat().st_size
         or p["proof_reference_addon_sha256"] != hashlib.sha256(addon).hexdigest()
         or p["proof_reference_output"] != rel(output)
         or p["proof_reference_requests"] != ["solution", *[r["generated_name"] for r in m["public_inline_ci_requests"]]]
         or p["exact_old_snapshot_prefix"] is not True or p["pure_python_prepared"] is not True
         or p["Lean_started"] is not False or p["validated"] is not False or p["submission_ready"] is not False,
         "Exact WithRefs preparation/source lineage differs")
    fail(p["compile_manifests"][source.name] != {"manifest": rel(mp), "manifest_sha256": sha(mp)}, "WithRefs actual compilation manifest binding differs")
    return source, mp, output


def kernel_refs(tree):
    found = set()
    def visit(t):
        if not isinstance(t, list): return
        # Lean.Expr.getUsedConstants follows projection bodies; the structure
        # Name stored by a projection is not an Expr.const occurrence.
        if t and t[0] == "const": found.add(t[1])
        for part in t: visit(part)
    visit(tree)
    return found


def checked_output(stage, manifest, pf, output):
    from validate_formal_log_truncation_provider import written_during
    written_during(output, pf)
    doc = read(output)
    fail(set(doc) != {"schemaVersion", "probeMainModule", "rows"} or doc["schemaVersion"] != 1
         or doc["probeMainModule"] != pf["data"]["actual_module_identity"], "Actual proof-reference output schema/owner differs")
    rows = doc["rows"]
    expected_names = ["solution", *[r["generated_name"] for r in manifest["public_inline_ci_requests"]]]
    fail(not isinstance(rows, list) or [r["name"] for r in rows] != expected_names, "Exact actual proof-reference Name domain differs")
    snapshot = read(stage / "generated-type.json") + read(formal.ROOT / manifest["public_inline_type_json_outputs"]["generated"])
    by_name = {r["name"]: r for r in snapshot}
    for row in rows:
        fail(set(row) != {"name", "userName", "kind", "levelParams", "closedType", "closedValue", "typeRefs", "valueRefs", "axioms", "owner"}, "Actual proof reference CI schema differs")
        fail(row["name"] != row["userName"] or row["kind"] != "theorem"
             or row["closedType"] is not True or row["closedValue"] is not True
             or row["owner"] != {"kind": "OwnModule", "module": doc["probeMainModule"]}, "Proof reference CI identity/closedness/actual ownership differs")
        fail(row["levelParams"] != by_name[row["name"]]["levelParams"], "Proof reference CI universe binders differ from same-run kernel snapshot")
        for field in ["typeRefs", "valueRefs"]:
            fail(not isinstance(row[field], list) or any(not isinstance(x, str) for x in row[field])
                 or row[field] != sorted(set(row[field])), "Actual proof reference set must be sorted unique Names")
        fail(set(row["typeRefs"]) != kernel_refs(by_name[row["name"]]["type"]), "Actual primitive type reference set differs from same-run structural kernel type")
        fail(not isinstance(row["axioms"], list) or any(not isinstance(x, str) for x in row["axioms"])
             or not set(row["axioms"]) <= context.STD3, "Actual generated proof axioms outside Std3")
    return rows
