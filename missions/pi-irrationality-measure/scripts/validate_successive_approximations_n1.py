"""Certify n1 from existing four-file Lean evidence; never starts Lean/API."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from unittest.mock import patch

import formal_log_node_refs as refs
import generate_platform_provider_nodes as nodegen
import prepare_successive_approximations_n1 as prep
import stage_successive_approximations_frontier as frontier
import validate_formal_log_node as kernel
import validate_namespace_context_providers as context
import validate_standalone_platform_node as standalone

TASK, ROOT, V = prep.TASK, prep.ROOT, prep.V
STAGE = prep.STAGE
CERT = STAGE / "n1-validation.json"
SELF = Path(__file__).resolve()
sha, read, rel, fail, file = context.sha, context.read, context.rel, context.fail, context.file


def reconstruction(manifest):
    generator, _, _ = frontier.promoted_generator()
    fail(generator.g.input_hashes != manifest["input_hashes"], "Frozen n1 source/AST input domain differs")
    captured = {}

    def capture_bytes(path, data):
        p = path.resolve()
        fail(p.parent != STAGE.resolve() or p.name in captured, "Unexpected or duplicate generator output")
        captured[p.name] = bytes(data)
        return len(data)

    def capture_text(path, value, encoding=None, errors=None, newline=None):
        return capture_bytes(path, value.encode(encoding or "utf-8", errors or "strict"))

    old_sha = nodegen.sha

    def captured_sha(path):
        p = path.resolve()
        if p.parent == STAGE.resolve() and p.name in captured:
            return hashlib.sha256(captured[p.name]).hexdigest()
        return old_sha(path)

    key = prep.KEY

    class Destination:
        def __truediv__(self, slug):
            fail(slug != "OAI_PiExponent_exists_successive_approximations", "n1 generation slug differs")
            return STAGE

    with patch.object(nodegen, "DEST", Destination()), \
         patch.object(Path, "write_bytes", capture_bytes), \
         patch.object(Path, "write_text", capture_text), \
         patch.object(Path, "mkdir", lambda *args, **kwargs: None), \
         patch.object(nodegen, "sha", captured_sha):
        report = generator.generate(key)
    fail(report["theorem_name"] != prep.NAME or report["node"] != key, "Reconstructed node identity differs")
    generated_manifest = json.loads(captured.pop("manifest.json"))
    statement_name = Path(generated_manifest["statement"]).name
    solution_name = Path(generated_manifest["solution"]).name
    fail(statement_name not in captured or solution_name not in captured, "Reconstruction lost theorem/solution source")
    generated_manifest["statement"] = (STAGE / "Theorems" / statement_name).relative_to(ROOT).as_posix()
    generated_manifest["solution"] = (STAGE / "Solutions" / solution_name).relative_to(ROOT).as_posix()
    generated_manifest["statement_sha256"] = hashlib.sha256(captured[statement_name]).hexdigest()
    generated_manifest["solution_sha256"] = hashlib.sha256(captured[solution_name]).hexdigest()
    generated_manifest["outputs_sha256"].pop(statement_name)
    generated_manifest["outputs_sha256"].pop(solution_name)
    for name, data in captured.items():
        actual = STAGE / name
        if name == statement_name:
            actual = STAGE / "Theorems" / name
        elif name == solution_name:
            actual = STAGE / "Solutions" / name
        fail(not actual.is_file() or actual.read_bytes() != data,
             "Exact source/AST regenerated file differs: " + str(actual))
    actual_manifest = read(STAGE / "manifest.json")
    if generated_manifest != actual_manifest:
        keys = sorted(key for key in set(generated_manifest) | set(actual_manifest)
                      if generated_manifest.get(key) != actual_manifest.get(key))
        raise ValueError("Exact source/AST n1 generator manifest differs at: " + ", ".join(keys)
                         + "; regenerated=" + repr(generated_manifest.get("outputs_sha256"))
                         + "; staged=" + repr(actual_manifest.get("outputs_sha256")))
    return generator


def actual_child_binding():
    row = prep.child_binding()
    fail(row["ready"] is not True, "Accepted local large-log child is not certified/importable")
    return row


def compiled(manifest, child):
    files = [Path(manifest["statement"]).name, Path(manifest["solution"]).name,
             "SnapshotOriginal.lean", "SnapshotGeneratedWithRefs.lean"]
    records = {}
    for name in files:
        source = STAGE / name
        if name.startswith("Thm_"):
            source = STAGE / "Theorems" / name
        elif name.startswith("Sol_"):
            source = STAGE / "Solutions" / name
        mp = TASK / read(STAGE / "preparation.json")["compile_manifests"][name]["manifest"]
        mode = "modecheck"
        module_name = ".".join(source.relative_to(STAGE).with_suffix("").parts)
        rec = context.record(source, mp, mode, module_name, STAGE)
        if name != "SnapshotOriginal.lean":
            imported = next((x for x in rec["data"]["dependency_oleans"]
                             if x["module"] == prep.CHILD_MODULE), None)
            fail(imported is None or imported["sha256_before"] != child["output_olean_sha256"],
                 "n1 imported child OLean differs from its exact certified bytes")
        records[name] = rec
    return records


def certify():
    prep.check()
    manifest = read(STAGE / "manifest.json")
    preparation = read(STAGE / "preparation.json")
    child = actual_child_binding()
    n = reconstruction(manifest)
    records = compiled(manifest, child)
    source_pf, generated_pf = records["SnapshotOriginal.lean"], records["SnapshotGeneratedWithRefs.lean"]
    original = kernel.kernel_rows(STAGE / "original-type.json", [prep.NAME], source_pf)
    generated = kernel.kernel_rows(STAGE / "generated-type.json", [prep.NAME, "solution"], generated_pf)
    for row in generated:
        kernel.same_type(original[0], row)
    inline_rows = {}
    for field in ("inline_type_json_outputs", "public_inline_type_json_outputs"):
        for side in ("original", "generated"):
            output_path = ROOT / manifest[field][side]
            rows = kernel.kernel_rows(output_path, [], records["SnapshotOriginal.lean"] if side == "original" else generated_pf)
            fail(rows != [], "n1 has unexpected inline proof/type exports")
            inline_rows[rel(output_path)] = rows
    audits = {
        "original_source": standalone.audit_axioms(file(source_pf["data"]["log"]), prep.NAME),
        "generated_solution": standalone.audit_axioms(file(generated_pf["data"]["log"]), "solution"),
        "exact_solution": standalone.audit_axioms(file(records[Path(manifest["solution"]).name]["data"]["log"]), "solution"),
    }
    if any(not set(value) <= context.STD3 for value in audits.values()):
        raise ValueError("n1 proof axioms exceed Std3")
    actual_refs = refs.checked_output(STAGE, manifest, generated_pf, STAGE / "proof-references.json")
    fail([row["name"] for row in actual_refs] != ["solution"], "Exact n1 proof-reference collector domain differs")
    proof = actual_refs[0]
    fail(proof["owner"] != {"kind": "OwnModule", "module": generated_pf["data"]["actual_module_identity"]}
         or prep.NAME in proof["valueRefs"] or "solution" in proof["valueRefs"],
         "n1 solution ownership/self-reference proof check failed")
    allowed = {prep.CHILD_NAME}
    graph = set(n.g.graph)
    project_refs = {x for x in proof["typeRefs"] + proof["valueRefs"]
                    if x in graph or x.startswith(("OAI.", "Definitions.", "Theorems.", "Solutions.", "_private.OAI."))}
    fail(not project_refs <= allowed, "n1 proof uses unapproved project constants: " + str(sorted(project_refs - allowed)))
    witness = kernel.source_command_witness(manifest, n)
    output_paths = [STAGE / "original-type.json", STAGE / "generated-type.json",
                    STAGE / "proof-references.json"]
    output_paths += [ROOT / manifest[field][side] for field in
                     ("inline_type_json_outputs", "public_inline_type_json_outputs")
                     for side in ("original", "generated")]
    implementations = [SELF, Path(prep.__file__), Path(frontier.__file__),
                       Path(nodegen.__file__), Path(kernel.__file__), Path(refs.__file__),
                       Path(context.__file__), Path(standalone.__file__), Path(prep.refs_producer.__file__)]
    report = {
        "schema_version": 1,
        "artifact_kind": "successive-approximations-n1-kernel-certificate",
        "node": prep.KEY,
        "theorem_name": prep.NAME,
        "source_commit": manifest["source_commit"],
        "source_components": manifest["source_components"],
        "source_command_witness": witness,
        "stage_manifest_sha256": sha(STAGE / "manifest.json"),
        "preparation_sha256": sha(STAGE / "preparation.json"),
        "academic_metadata_sha256": sha(STAGE / "academic-metadata.json"),
        "child_certificate": child,
        "compiler_records": {name: {"record": row["record"], "record_sha256": row["record_sha256"],
                                     "seconds": row["data"]["seconds"], "mode": row["data"]["mode"],
                                     "actual_module_identity": row["data"]["actual_module_identity"],
                                     "output_olean_sha256": row["data"]["output_olean_sha256"]}
                              for name, row in records.items()},
        "preflights": records,
        "types_equal": True,
        "inline_type_outputs": inline_rows,
        "proof_references": actual_refs,
        "project_proof_references": sorted(project_refs),
        "axiom_audits": {name: sorted(value) for name, value in audits.items()},
        "proof_axioms": "Std3",
        "max_file_seconds": max(row["data"]["seconds"] for row in records.values()),
        "output_json_sha256": {rel(path): sha(path) for path in output_paths},
        "implementation_hashes": {rel(path): sha(path) for path in implementations},
        "input_hashes": manifest["input_hashes"],
        "validated": True,
        "Lean_started_by_validator": False,
        "API_used": False,
        "submission_ready": False,
    }
    write_cert(report)
    return report


def write_cert(report):
    raw = (json.dumps(report, indent=2, ensure_ascii=False) + "\n").encode()
    if CERT.exists() and CERT.read_bytes() != raw:
        raise ValueError("Existing n1 validation certificate differs; preserve it before a new validation run")
    if not CERT.exists():
        CERT.write_bytes(raw)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certify-existing", action="store_true", required=True)
    args = parser.parse_args()
    print(json.dumps(certify(), indent=2, ensure_ascii=False))
