"""Prepare strict c1-c4 manifests for the selector-normalization node."""
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
STAGE = V / "ap4/n2"
KEY = "OAI.NumberTheory.PiExponent.Approximation.SuccessiveApproximations:4368"
NAME = "OAI.PiExponent.exists_normalized_selection_of_selector"
MODULE = "OAI.NumberTheory.PiExponent.Approximation.SuccessiveApproximations"
PLATFORM = "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_SuccessiveApproximations"
DEF_INPUT = STAGE / "definition-input.json"
SELF = Path(__file__).resolve()


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rel(path: Path) -> str:
    return path.relative_to(TASK).as_posix()


def read(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def write(path: Path, value) -> None:
    raw = value if isinstance(value, bytes) else (json.dumps(value, indent=2, ensure_ascii=False) + "\n").encode()
    if path.exists():
        if path.read_bytes() == raw:
            return
        try:
            previous = json.loads(path.read_text(encoding="utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError):
            previous = {}
        if previous.get("Lean_started") is not False or previous.get("validated", previous.get("node_validated", False)) is not False:
            raise ValueError("Existing n2 evidence advanced; preserve it before replacement: " + str(path))
        base = path.with_name(path.name + ".before-next-preparation")
        backup, suffix = base, 2
        while backup.exists() and backup.read_bytes() != path.read_bytes():
            backup, suffix = path.with_name(base.name + "." + str(suffix)), suffix + 1
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
            raise ValueError("n2 proof-reference collector identifier repair is not exact")
        addon = addon.replace(old, new, 1)
    return addon


def validate_inputs():
    manifest = read(STAGE / "manifest.json")
    metadata = read(STAGE / "academic-metadata.json")
    witness = read(STAGE / "inline-helper-ast-witness.json")
    definition = read(DEF_INPUT)
    if (manifest.get("node") != KEY or manifest.get("theorem_name") != NAME
            or manifest.get("source_graph_name") != NAME
            or manifest.get("source_commit") != "adc7f1241b42e322a6451854ab7e4b4c146bf78a"
            or manifest.get("validated") is not False or manifest.get("submission_ready") is not False
            or manifest.get("lean_started") is not False or manifest.get("api_used") is not False):
        raise ValueError("Frozen n2 identity/state differs")
    if set(metadata) != {"theorem_title", "natural_language_statement", "explanation", "tags", "source_commit", "source_url"}:
        raise ValueError("n2 academic metadata must have exactly six platform fields")
    if metadata["source_commit"] != manifest["source_commit"] or "selector" not in metadata["natural_language_statement"].lower():
        raise ValueError("n2 academic metadata has drifted from the source result")
    if len(manifest["definition_dependency_witnesses"]) != 1:
        raise ValueError("n2 must consume exactly the published normalizedLogWeights Definition")
    if manifest["definition_dependency_witnesses"][0]["platform_module"] != PLATFORM:
        raise ValueError("n2 Definition dependency module differs")
    if manifest["child_nodes"] or manifest["node_generated_names"]:
        raise ValueError("n2 has an unexpected child/private-helper dependency")
    if definition.get("validated") is not True or definition.get("source174_certificate_used") is not False:
        raise ValueError("n2 actual Definition input is not strictly certified")
    if (definition.get("source_module") != MODULE or definition.get("platform_module") != PLATFORM
            or definition.get("definition_id") != "74cfcd7f-9e25-450a-a16f-f6d00a7187e2"):
        # Stable identity is separately pinned below; fail closed if the
        # published Definition or module mapping changes.
        raise ValueError("n2 published Definition identity differs")
    cert, publication, olean = (TASK / definition[field] for field in
                                ("certificate", "publication", "output_olean"))
    if any(sha(path) != definition[field + "_sha256"] for path, field in
           ((cert, "certificate"), (publication, "publication"), (olean, "output_olean"))):
        raise ValueError("n2 actual Definition certificate/publication/OLean pin changed")
    if len(witness["helpers"]) != 2 or [row["source_graph_name"] for row in witness["helpers"]] != [
            "OAI.PiExponent.normalizedLogWeights_succ", "OAI.PiExponent.reverse_logWeights_prod"]:
        raise ValueError("n2 raw AST helper witness domain differs")
    if witness["helpers"][0]["raw_proof_suffix_utf8"] != ":= rfl" or any(
            row["generated_companion"] is not False or row["no_companion_identity_inferred"] is not True
            for row in witness["helpers"]):
        raise ValueError("n2 helper proof or companion identity lacks exact source AST evidence")
    if sha(STAGE / "inline-helper-ast-witness.json") != read(V / "ap4/frontier-plan.json")["n2_inline_helper_ast_witness_sha256"]:
        raise ValueError("n2 helper AST witness differs from frontier plan")
    for source in manifest["source_components"]:
        for field in ("source", "facts", "original_source"):
            if sha(ROOT / source[field]) != source[field + "_sha256"]:
                raise ValueError("n2 source/AST provenance changed: " + source[field])
    for relative, expected in manifest["input_hashes"].items():
        if sha(TASK / relative) != expected:
            raise ValueError("Frozen n2 generator input changed: " + relative)
    for filename, expected in manifest["outputs_sha256"].items():
        path = STAGE / filename
        if filename.startswith("Thm_"):
            path = STAGE / "Theorems" / filename
        elif filename.startswith("Sol_"):
            path = STAGE / "Solutions" / filename
        if sha(path) != expected:
            raise ValueError("Frozen n2 source output changed: " + filename)
    return manifest, metadata, definition, witness


def prepare():
    manifest, metadata, definition, witness = validate_inputs()
    base = STAGE / "SnapshotGenerated.lean"
    output = STAGE / "proof-references.json"
    extended = STAGE / "SnapshotGeneratedWithRefs.lean"
    addon = repaired_addon(manifest["public_inline_ci_requests"], output)
    write(extended, base.read_bytes() + addon)
    certified = {
        "schema_version": 1,
        "artifact_kind": "successive-approximations-n2-certified-inputs",
        "node": KEY,
        "definition": definition,
        "child_certificates": [],
        "Lean_started": False,
        "validated": False,
        "submission_ready": False,
    }
    write(STAGE / "certified-inputs.json", certified)
    inputs = {
        rel(SELF): sha(SELF),
        rel(Path(refs_producer.__file__)): sha(Path(refs_producer.__file__)),
        rel(STAGE / "manifest.json"): sha(STAGE / "manifest.json"),
        rel(STAGE / "academic-metadata.json"): sha(STAGE / "academic-metadata.json"),
        rel(STAGE / "inline-helper-ast-witness.json"): sha(STAGE / "inline-helper-ast-witness.json"),
        rel(DEF_INPUT): sha(DEF_INPUT),
        definition["certificate"]: definition["certificate_sha256"],
        definition["stage_manifest"]: definition["stage_manifest_sha256"],
        definition["publication"]: definition["publication_sha256"],
        definition["output_olean"]: definition["output_olean_sha256"],
    }
    for relative, expected in manifest["input_hashes"].items():
        inputs[relative] = expected
    inputs[rel(STAGE / "certified-inputs.json")] = sha(STAGE / "certified-inputs.json")
    filenames = [Path(manifest["statement"]).name, Path(manifest["solution"]).name,
                 "SnapshotOriginal.lean", extended.name]
    compile = {}
    for i, filename in enumerate(filenames, 1):
        source = STAGE / filename
        if filename.startswith("Thm_"):
            source = STAGE / "Theorems" / filename
        elif filename.startswith("Sol_"):
            source = STAGE / "Solutions" / filename
        imports = ["Lean", MODULE] if filename == "SnapshotOriginal.lean" else manifest["imports"]
        doc = {
            "schema_version": 1,
            "artifact_kind": "successive-approximations-n2-file-import-certificate",
            "output": source.relative_to(ROOT).as_posix(),
            "output_sha256": sha(source),
            "imports": imports,
            "input_hashes": inputs,
            "runtime_sha256": manifest["runtime_sha256"],
            "node": KEY,
            "node_validated": False,
            "timeout_seconds": 300,
            "Lean_started": False,
            "submission_ready": False,
        }
        mp = STAGE / f"c{i}.json"
        write(mp, doc)
        compile[filename] = {"manifest": rel(mp), "manifest_sha256": sha(mp)}
    artifacts = [STAGE / "original-type.json", STAGE / "generated-type.json", output]
    artifacts += [ROOT / manifest[key][side] for key in ("inline_type_json_outputs", "public_inline_type_json_outputs")
                  for side in ("original", "generated")]
    artifacts += [STAGE / (filename + ".preflight.json") for filename in filenames]
    max_path = max(len(str(path.resolve())) for path in artifacts)
    if max_path >= 240:
        raise ValueError("n2 compiler artifacts exceed conservative Windows path budget")
    write(STAGE / "preparation.json", {
        "schema_version": 1,
        "artifact_kind": "successive-approximations-n2-preparation",
        "stage": rel(STAGE),
        "node": KEY,
        "stage_manifest_sha256": sha(STAGE / "manifest.json"),
        "metadata_sha256": sha(STAGE / "academic-metadata.json"),
        "ast_witness_sha256": sha(STAGE / "inline-helper-ast-witness.json"),
        "definition_input": rel(DEF_INPUT),
        "definition_input_sha256": sha(DEF_INPUT),
        "definition": definition,
        "certified_inputs_sha256": sha(STAGE / "certified-inputs.json"),
        "base_snapshot": rel(base),
        "base_snapshot_sha256": sha(base),
        "generated_with_refs": rel(extended),
        "generated_with_refs_sha256": sha(extended),
        "generated_with_refs_prefix_bytes": base.stat().st_size,
        "reference_addon_sha256": hashlib.sha256(addon).hexdigest(),
        "proof_reference_output": rel(output),
        "proof_reference_requests": ["solution", *[row["generated_name"] for row in manifest["public_inline_ci_requests"]]],
        "compile_manifests": compile,
        "maximum_artifact_path_length": max_path,
        "compile_commands": {
            "Thm_OAI_PiExponent_exists_normalized_selection_of_selector.lean":
                "python scripts/preflight_staged_module.py ap4/n2/Theorems/Thm_OAI_PiExponent_exists_normalized_selection_of_selector.lean --root ap4/n2 --imports-manifest ap4/n2/c1.json --timeout-seconds 300",
            "Sol_OAI_PiExponent_exists_normalized_selection_of_selector.lean":
                "python scripts/preflight_staged_module.py ap4/n2/Solutions/Sol_OAI_PiExponent_exists_normalized_selection_of_selector.lean --root ap4/n2 --imports-manifest ap4/n2/c2.json --timeout-seconds 300",
            "SnapshotOriginal.lean":
                "python scripts/preflight_staged_module.py ap4/n2/SnapshotOriginal.lean --root ap4/n2 --imports-manifest ap4/n2/c3.json --timeout-seconds 300",
            "SnapshotGeneratedWithRefs.lean":
                "python scripts/preflight_staged_module.py ap4/n2/SnapshotGeneratedWithRefs.lean --root ap4/n2 --imports-manifest ap4/n2/c4.json --timeout-seconds 300",
        },
        "Lean_started": False,
        "validated": False,
        "submission_ready": False,
    })
    return check()


def check():
    manifest, _, definition, _ = validate_inputs()
    preparation = read(STAGE / "preparation.json")
    if preparation["definition"] != definition:
        raise ValueError("n2 actual Definition binding changed")
    base = STAGE / "SnapshotGenerated.lean"
    output = STAGE / "proof-references.json"
    extended = STAGE / "SnapshotGeneratedWithRefs.lean"
    addon = repaired_addon(manifest["public_inline_ci_requests"], output)
    if extended.read_bytes() != base.read_bytes() + addon:
        raise ValueError("n2 WithRefs file is not exact base prefix plus collector")
    for filename, row in preparation["compile_manifests"].items():
        source = STAGE / filename
        if filename.startswith("Thm_"):
            source = STAGE / "Theorems" / filename
        elif filename.startswith("Sol_"):
            source = STAGE / "Solutions" / filename
        mp = TASK / row["manifest"]
        doc = read(mp)
        if sha(mp) != row["manifest_sha256"] or doc["output_sha256"] != sha(source):
            raise ValueError("n2 compiler manifest/source bytes changed: " + filename)
        runner.verify_manifest_inputs(doc)
        runner.verify_source_certificate(source, doc)
        runner.certified_imports(source, doc)
    return {"checked": True, "node": NAME, "maximum_artifact_path_length": preparation["maximum_artifact_path_length"],
            "definition_olean_sha256": definition["output_olean_sha256"],
            "inline_helpers": ["OAI.PiExponent.normalizedLogWeights_succ", "OAI.PiExponent.reverse_logWeights_prod"],
            "Lean_started": False, "validated": False, "submission_ready": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--prepare", action="store_true")
    group.add_argument("--check", action="store_true")
    args = parser.parse_args()
    print(json.dumps(prepare() if args.prepare else check(), indent=2, ensure_ascii=False))
