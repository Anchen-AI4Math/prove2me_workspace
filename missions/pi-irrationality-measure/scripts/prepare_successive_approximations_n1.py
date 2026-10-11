"""Prepare strict c1-c4 compiler manifests for the first approximation node.

Pure Python only. The local large-log child must be compiled and bound before
any of these manifests can be used as proof validation evidence.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import preflight_staged_module as runner
import stage_formal_log_base_node as refs_producer

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
V = TASK / "verification"
STAGE = V / "ap4/n1"
KEY = "OAI.NumberTheory.PiExponent.Approximation.SuccessiveApproximations:164"
NAME = "OAI.PiExponent.exists_successive_approximations"
MODULE = "OAI.NumberTheory.PiExponent.Approximation.SuccessiveApproximations"
CHILD_NAME = "OAI.PiExponent.exists_large_log_approximation"
CHILD_MODULE = "Theorems.Thm_OAI_PiExponent_exists_large_log_approximation"
CHILD_OLEAN = V / "staged-build/lib/lean/Theorems/Thm_OAI_PiExponent_exists_large_log_approximation.olean"
SELF = Path(__file__).resolve()


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rel(path: Path) -> str:
    return path.relative_to(TASK).as_posix()


def read(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def write_new(path: Path, value) -> None:
    raw = value if isinstance(value, bytes) else (json.dumps(value, indent=2, ensure_ascii=False) + "\n").encode()
    if path.exists():
        if path.read_bytes() != raw:
            try:
                old = json.loads(path.read_text(encoding="utf-8"))
            except (UnicodeDecodeError, json.JSONDecodeError):
                old = {}
            old_validated = old.get("validated", old.get("node_validated", False))
            if old.get("Lean_started") is not False or old_validated is not False:
                raise ValueError("Existing n1 evidence has advanced; preserve it before changing: " + str(path))
            base = path.with_name(path.name + ".before-next-preparation")
            backup = base
            suffix = 2
            while backup.exists() and backup.read_bytes() != path.read_bytes():
                backup = path.with_name(base.name + "." + str(suffix))
                suffix += 1
            if not backup.exists():
                backup.write_bytes(path.read_bytes())
            path.write_bytes(raw)
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)


def repaired_addon(requests, output: Path) -> bytes:
    addon = refs_producer.proof_reference_addon(requests, output).encode()
    for old, new in ((b"def export (", b"def exportProofRefs ("),
                     (b"FormalLogProofReferenceSnapshot.export ",
                      b"FormalLogProofReferenceSnapshot.exportProofRefs ")):
        if addon.count(old) != 1 or addon.count(new) != 0:
            raise ValueError("Proof-reference collector identifier repair is not exact")
        addon = addon.replace(old, new, 1)
    return addon


def expected():
    manifest = read(STAGE / "manifest.json")
    required = {
        "node": KEY,
        "theorem_name": NAME,
        "source_graph_name": NAME,
        "source_commit": "adc7f1241b42e322a6451854ab7e4b4c146bf78a",
        "validated": False,
        "submission_ready": False,
        "lean_started": False,
        "api_used": False,
        "full_tree_ready": False,
    }
    if any(manifest.get(key) != value for key, value in required.items()):
        raise ValueError("Frozen n1 node identity/state differs")
    if manifest["child_nodes"] != {
        "OAI.NumberTheory.PiExponent.Approximation.ApproximationSelection:131": CHILD_NAME
    }:
        raise ValueError("n1 must have exactly the accepted large-log child")
    if manifest["definition_certificates"] or manifest["node_generated_names"]:
        raise ValueError("n1 unexpectedly has Definition or private helper obligations")
    if len(manifest["source_components"]) != 1 or manifest["source_components"][0]["source_module"] != MODULE:
        raise ValueError("n1 source witness module differs")
    if len(manifest["public_inline_ci_requests"]) != 0:
        raise ValueError("n1 unexpectedly has public inline proof references")
    metadata = read(STAGE / "academic-metadata.json")
    if set(metadata) != {"theorem_title", "natural_language_statement", "explanation", "tags",
                         "source_commit", "source_url"}:
        raise ValueError("Academic metadata must contain exactly the six platform fields")
    statement = metadata["natural_language_statement"].lower()
    if metadata["source_commit"] != manifest["source_commit"] or not any(
            marker in statement for marker in ("assume", "suppose")):
        raise ValueError("Academic metadata lost source or conditionality")
    source = manifest["source_components"][0]
    for field in ("source", "facts", "original_source"):
        path = ROOT / source[field]
        if sha(path) != source[field + "_sha256"]:
            raise ValueError("n1 source/AST witness changed: " + source[field])
    for path, expected_hash in manifest["input_hashes"].items():
        if sha(TASK / path) != expected_hash:
            raise ValueError("Frozen global generator input changed: " + path)
    for filename, expected_hash in manifest["outputs_sha256"].items():
        path = (STAGE / filename)
        if filename.startswith("Thm_"):
            path = STAGE / "Theorems" / filename
        elif filename.startswith("Sol_"):
            path = STAGE / "Solutions" / filename
        if sha(path) != expected_hash:
            raise ValueError("Frozen n1 generator output changed: " + filename)
    if manifest["statement"] != (STAGE / "Theorems" / Path(manifest["statement"]).name).relative_to(ROOT).as_posix():
        raise ValueError("n1 theorem module is not routed under Theorems/")
    if manifest["solution"] != (STAGE / "Solutions" / Path(manifest["solution"]).name).relative_to(ROOT).as_posix():
        raise ValueError("n1 solution module is not routed under Solutions/")
    return manifest, metadata


def child_binding():
    prep_path = V / "ap4/c1/child-module.json"
    source_path = V / "ap4/c1/Theorems/Thm_OAI_PiExponent_exists_large_log_approximation.lean"
    if not prep_path.is_file():
        return {"ready": False, "reason": "local child source/certificate pending"}
    child = read(prep_path)
    if child.get("theorem_name") != CHILD_NAME:
        raise ValueError("Local child source theorem identity differs")
    # The owner file is preparation only. A compiler/kernel certificate is
    # required before pinning the imported OLean as proved input.
    if not CHILD_OLEAN.is_file():
        return {"ready": False, "reason": "local child OLean not yet produced",
                "source": rel(source_path), "module": CHILD_MODULE}
    cert_candidates = [V / "ap4/c1/actual-child-validation.json"]
    cert_path = next((path for path in cert_candidates if path.is_file()), None)
    if cert_path is None:
        return {"ready": False, "reason": "local child OLean exists but exact child kernel certificate is pending",
                "source": rel(source_path), "module": CHILD_MODULE,
                "output_olean": rel(CHILD_OLEAN), "output_olean_sha256": sha(CHILD_OLEAN)}
    cert = read(cert_path)
    owner = cert.get("actual_module_owner", {})
    if (cert.get("validated") is not True or cert.get("module") != CHILD_MODULE
            or cert.get("Std3_only") is not True
            or owner.get("module") != CHILD_MODULE or owner.get("kind") != "ImportedModule"
            or not isinstance(owner.get("index"), int) or owner["index"] < 0
            # Actual-child validators record workspace-relative paths, while
            # this mission's preparation records task-relative paths. Resolve
            # the exact recorded path and require it to be the expected OLean.
            or not (ROOT / cert.get("child_olean", "")).resolve() == CHILD_OLEAN.resolve()
            or cert.get("child_olean_sha256") != sha(CHILD_OLEAN)):
        raise ValueError("Local child certificate is present but not the exact proved-child certificate")
    return {"ready": True, "module": CHILD_MODULE, "theorem_name": CHILD_NAME,
            "certificate": rel(cert_path), "certificate_sha256": sha(cert_path),
            "output_olean": rel(CHILD_OLEAN), "output_olean_sha256": sha(CHILD_OLEAN),
            "proof_axioms": "Std3", "validated": True}


def prepare():
    manifest, metadata = expected()
    base = STAGE / "SnapshotGenerated.lean"
    output = STAGE / "proof-references.json"
    extended = STAGE / "SnapshotGeneratedWithRefs.lean"
    addon = repaired_addon(manifest["public_inline_ci_requests"], output)
    write_new(extended, base.read_bytes() + addon)
    child = child_binding()
    input_pins = {rel(SELF): sha(SELF), rel(Path(refs_producer.__file__)): sha(Path(refs_producer.__file__)),
                  rel(STAGE / "manifest.json"): sha(STAGE / "manifest.json"),
                  rel(STAGE / "academic-metadata.json"): sha(STAGE / "academic-metadata.json")}
    for relative, expected_hash in manifest["input_hashes"].items():
        input_pins[relative] = expected_hash
    if child["ready"]:
        input_pins[child["output_olean"]] = child["output_olean_sha256"]
        input_pins[child["certificate"]] = child["certificate_sha256"]
    certified_inputs = {
        "schema_version": 1,
        "artifact_kind": "successive-approximations-n1-certified-inputs",
        "node": KEY,
        "definition_certificates": [],
        "child_certificates": [child] if child["ready"] else [],
        "pending_child": None if child["ready"] else {
            "node": "OAI.NumberTheory.PiExponent.Approximation.ApproximationSelection:131",
            "theorem_name": CHILD_NAME, "module": CHILD_MODULE, **child},
        "Lean_started": False,
        "validated": False,
        "submission_ready": False,
    }
    write_new(STAGE / "certified-inputs.json", certified_inputs)
    files = [Path(manifest["statement"]).name, Path(manifest["solution"]).name,
             "SnapshotOriginal.lean", extended.name]
    compile = {}
    for index, filename in enumerate(files, 1):
        source = STAGE / filename
        if filename.startswith("Thm_"):
            source = STAGE / "Theorems" / filename
        elif filename.startswith("Sol_"):
            source = STAGE / "Solutions" / filename
        imports = (["Lean", MODULE] if filename == "SnapshotOriginal.lean" else manifest["imports"])
        document = {
            "schema_version": 1,
            "artifact_kind": "successive-approximations-n1-file-import-certificate",
            "output": source.relative_to(ROOT).as_posix(),
            "output_sha256": sha(source),
            "imports": imports,
            "input_hashes": input_pins,
            "pending_required_import_pins": [] if child["ready"] else [CHILD_MODULE],
            "runtime_sha256": manifest["runtime_sha256"],
            "node": KEY,
            "node_validated": False,
            "timeout_seconds": 300,
            "Lean_started": False,
            "submission_ready": False,
        }
        mp = STAGE / f"c{index}.json"
        write_new(mp, document)
        compile[filename] = {"manifest": rel(mp), "manifest_sha256": sha(mp),
                             "pending_child_binding": not child["ready"]}
    outputs = [STAGE / "original-type.json", STAGE / "generated-type.json", output]
    outputs += [ROOT / manifest["inline_type_json_outputs"][side] for side in ("original", "generated")]
    outputs += [ROOT / manifest["public_inline_type_json_outputs"][side] for side in ("original", "generated")]
    artifact_paths = [source for source in outputs]
    artifact_paths += [STAGE / (filename + ".preflight.json") for filename in files]
    max_path = max((len(str(path.resolve())) for path in artifact_paths), default=0)
    if max_path >= 240:
        raise ValueError("n1 compiler artifacts exceed conservative Windows path budget")
    preparation = {
        "schema_version": 1,
        "artifact_kind": "successive-approximations-n1-preparation",
        "stage": rel(STAGE),
        "node": KEY,
        "frozen_manifest_sha256": sha(STAGE / "manifest.json"),
        "metadata_sha256": sha(STAGE / "academic-metadata.json"),
        "certified_inputs": rel(STAGE / "certified-inputs.json"),
        "certified_inputs_sha256": sha(STAGE / "certified-inputs.json"),
        "base_snapshot": rel(base),
        "base_snapshot_sha256": sha(base),
        "generated_with_refs": rel(extended),
        "generated_with_refs_sha256": sha(extended),
        "generated_with_refs_prefix_bytes": base.stat().st_size,
        "reference_addon_sha256": hashlib.sha256(addon).hexdigest(),
        "proof_reference_output": rel(output),
        "proof_reference_requests": ["solution"],
        "child_binding": child,
        "compile_manifests": compile,
        "compile_commands": {
            "Thm_OAI_PiExponent_exists_successive_approximations.lean":
                "python scripts/preflight_staged_module.py ap4/n1/Theorems/Thm_OAI_PiExponent_exists_successive_approximations.lean --root ap4/n1 --imports-manifest ap4/n1/c1.json --timeout-seconds 300",
            "Sol_OAI_PiExponent_exists_successive_approximations.lean":
                "python scripts/preflight_staged_module.py ap4/n1/Solutions/Sol_OAI_PiExponent_exists_successive_approximations.lean --root ap4/n1 --imports-manifest ap4/n1/c2.json --timeout-seconds 300",
            "SnapshotOriginal.lean":
                "python scripts/preflight_staged_module.py ap4/n1/SnapshotOriginal.lean --root ap4/n1 --imports-manifest ap4/n1/c3.json --timeout-seconds 300",
            "SnapshotGeneratedWithRefs.lean":
                "python scripts/preflight_staged_module.py ap4/n1/SnapshotGeneratedWithRefs.lean --root ap4/n1 --imports-manifest ap4/n1/c4.json --timeout-seconds 300",
        },
        "maximum_artifact_path_length": max_path,
        "exact_snapshot_prefix": True,
        "Lean_started": False,
        "validated": False,
        "submission_ready": False,
    }
    write_new(STAGE / "preparation.json", preparation)
    return {"prepared": True, "node": NAME, "files": files,
            "child_binding_ready": child["ready"], "maximum_artifact_path_length": max_path,
            "Lean_started": False, "validated": False, "submission_ready": False}


def check():
    manifest, _ = expected()
    preparation = read(STAGE / "preparation.json")
    child = child_binding()
    if preparation["child_binding"] != child:
        raise ValueError("n1 child certificate binding changed; regenerate only after certifying the child")
    extended = STAGE / "SnapshotGeneratedWithRefs.lean"
    base = STAGE / "SnapshotGenerated.lean"
    output = STAGE / "proof-references.json"
    addon = repaired_addon(manifest["public_inline_ci_requests"], output)
    if extended.read_bytes() != base.read_bytes() + addon:
        raise ValueError("SnapshotGeneratedWithRefs is not the exact base prefix plus proof collector")
    pending = not child["ready"]
    for filename, row in preparation["compile_manifests"].items():
        source = STAGE / filename
        if filename.startswith("Thm_"):
            source = STAGE / "Theorems" / filename
        elif filename.startswith("Sol_"):
            source = STAGE / "Solutions" / filename
        mp = TASK / row["manifest"]
        document = read(mp)
        if sha(mp) != row["manifest_sha256"] or sha(source) != document["output_sha256"]:
            raise ValueError("n1 compiler manifest or source bytes changed: " + filename)
        runner.verify_manifest_inputs(document)
        runner.verify_source_certificate(source, document)
        if not pending:
            runner.certified_imports(source, document)
        elif CHILD_MODULE not in document.get("pending_required_import_pins", []):
            raise ValueError("n1 child import is neither pinned nor explicitly pending")
    return {"checked": True, "node": NAME, "child_binding_pending": pending,
            "maximum_artifact_path_length": preparation["maximum_artifact_path_length"],
            "Lean_started": False, "validated": False, "submission_ready": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--prepare", action="store_true")
    group.add_argument("--check", action="store_true")
    args = parser.parse_args()
    print(json.dumps(prepare() if args.prepare else check(), indent=2, ensure_ascii=False))
