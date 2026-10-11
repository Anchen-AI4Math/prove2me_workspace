"""Validate n2z from existing modecheck evidence; never starts Lean or API."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import formal_log_node_refs as refs
import generate_platform_provider_nodes as nodegen
import prepare_successive_approximations_n2z as prep
import stage_formal_log_base_node as refs_producer
import stage_successive_approximations_n2z as staging
import validate_formal_log_node as kernel
import validate_namespace_context_providers as context
import validate_standalone_platform_node as standalone

TASK, ROOT, V, STAGE = prep.TASK, prep.ROOT, prep.V, prep.STAGE
CERT = STAGE / "n2z-validation.json"
SELF = Path(__file__).resolve()
sha, read, rel, fail, file = context.sha, context.read, context.rel, context.fail, context.file


def reconstruction(manifest, witness):
    zero = witness["helpers"][0]["raw_command_utf8"].encode("utf-8")
    expected_zero = zero.replace(b"\r\n", b"\n").rstrip(b"\n") + b"\n\n"
    marker = b"@[simp] theorem normalizedLogWeights_succ"
    old_files = {
        "theorem": prep.V / "ap4/n2/Theorems/Thm_OAI_PiExponent_exists_normalized_selection_of_selector.lean",
        "solution": prep.V / "ap4/n2/Solutions/Sol_OAI_PiExponent_exists_normalized_selection_of_selector.lean",
        "generated": prep.V / "ap4/n2/SnapshotGenerated.lean",
    }
    for key, old in old_files.items():
        if key == "generated":
            continue
        source = old.read_bytes()
        fail(source.count(marker) != 1, "Frozen n2 source insertion point differs: " + key)
        expected = source.replace(marker, expected_zero + marker, 1)
        current = {"theorem": STAGE / "Theorems/Thm_OAI_PiExponent_exists_normalized_selection_of_selector.lean",
                   "solution": STAGE / "Solutions/Sol_OAI_PiExponent_exists_normalized_selection_of_selector.lean",
                   "generated": STAGE / "SnapshotGenerated.lean"}[key].read_bytes()
        if key == "generated":
            expected = expected.replace(b"ap4/n2/", b"ap4/n2z/")
        fail(current != expected, "n2z generated source does not equal n2 plus AST-exact zero helper: " + key)
    reqs = manifest["public_inline_ci_requests"]
    source_collect = nodegen.public_inline_snapshot_code(
        reqs, "missions/pi-irrationality-measure/verification/ap4/n2z/original-public-inline-types.json",
        generated=False).encode()
    generated_collect = nodegen.public_inline_snapshot_code(
        reqs, "missions/pi-irrationality-measure/verification/ap4/n2z/generated-public-inline-types.json",
        generated=True).encode()
    old_original = (prep.V / "ap4/n2/SnapshotOriginal.lean").read_bytes().replace(b"ap4/n2/", b"ap4/n2z/")
    old_generated = (prep.V / "ap4/n2/SnapshotGenerated.lean").read_bytes()
    if old_generated.count(marker) != 1:
        raise ValueError("Frozen n2 generated snapshot helper insertion point differs")
    old_generated = old_generated.replace(marker, expected_zero + marker, 1).replace(b"ap4/n2/", b"ap4/n2z/")
    fail((STAGE / "SnapshotOriginal.lean").read_bytes() != old_original + source_collect,
         "n2z source public-inline collector is not reconstructed exactly")
    fail((STAGE / "SnapshotGenerated.lean").read_bytes() != old_generated + generated_collect,
         "n2z generated public-inline collector is not reconstructed exactly")
    addon = prep.repaired_addon(reqs, STAGE / "proof-references.json")
    fail((STAGE / "SnapshotGeneratedWithRefs.lean").read_bytes() != old_generated + generated_collect + addon,
         "n2z WithRefs source is not exact generated prefix plus source-bound collectors")
    return staging.sha(Path(staging.__file__))


def compiled(manifest):
    names = [Path(manifest["statement"]).name, Path(manifest["solution"]).name,
             "SnapshotOriginal.lean", "SnapshotGeneratedWithRefs.lean"]
    rows = {}
    prep_doc = read(STAGE / "preparation.json")
    definition = prep_doc["definition"]
    for name in names:
        source = STAGE / name
        if name.startswith("Thm_"):
            source = STAGE / "Theorems" / name
        elif name.startswith("Sol_"):
            source = STAGE / "Solutions" / name
        mp = TASK / prep_doc["compile_manifests"][name]["manifest"]
        module_name = ".".join(source.relative_to(STAGE).with_suffix("").parts)
        rec = context.record(source, mp, "modecheck", module_name, STAGE)
        if name != "SnapshotOriginal.lean":
            actual = {dep["module"]: dep["sha256_before"] for dep in rec["data"]["dependency_oleans"]}
            if actual.get(prep.PLATFORM) != definition["output_olean_sha256"]:
                raise ValueError("n2z imported actual normalizedLogWeights Definition OLean differs")
        rows[name] = rec
    return rows


def certify():
    manifest, _, definition, witness = prep.validate_inputs()
    preparation = read(STAGE / "preparation.json")
    reconstructed_sha = reconstruction(manifest, witness)
    rows = compiled(manifest)
    original_pf, generated_pf = rows["SnapshotOriginal.lean"], rows["SnapshotGeneratedWithRefs.lean"]
    original = kernel.kernel_rows(STAGE / "original-type.json", [prep.NAME], original_pf)
    generated = kernel.kernel_rows(STAGE / "generated-type.json", [prep.NAME, "solution"], generated_pf)
    for row in generated: kernel.same_type(original[0], row)
    source_helper_names = [row["source_graph_name"] for row in manifest["public_inline_ci_requests"]]
    generated_helper_names = [row["generated_name"] for row in manifest["public_inline_ci_requests"]]
    old_inline = kernel.kernel_rows(ROOT / manifest["public_inline_type_json_outputs"]["original"], source_helper_names, original_pf)
    new_inline = kernel.kernel_rows(ROOT / manifest["public_inline_type_json_outputs"]["generated"], generated_helper_names, generated_pf)
    for left, right in zip(old_inline, new_inline, strict=True):
        kernel.same_type(left, right)
    for side, pf in (("original", original_pf), ("generated", generated_pf)):
        empty = kernel.kernel_rows(ROOT / manifest["inline_type_json_outputs"][side], [], pf)
        fail(empty != [], "n2z has unexpected private inline CI output")
    audits = {
        "source_target": standalone.audit_axioms(file(original_pf["data"]["log"]), prep.NAME),
        "generated_solution": standalone.audit_axioms(file(generated_pf["data"]["log"]), "solution"),
        "exact_solution": standalone.audit_axioms(file(rows[Path(manifest["solution"]).name]["data"]["log"]), "solution"),
    }
    if any(not set(value) <= context.STD3 for value in audits.values()):
        raise ValueError("n2z proof/source axiom audit exceeds Std3")
    actual_refs = refs.checked_output(STAGE, manifest, generated_pf, STAGE / "proof-references.json")
    expect_names = ["solution", *generated_helper_names]
    fail([row["name"] for row in actual_refs] != expect_names,
         "n2z proof-reference output domain differs from theorem plus three AST helpers")
    fail(any(not set(row["axioms"]) <= context.STD3 for row in actual_refs),
         "n2z proof-reference axioms exceed Std3")
    graph = set(nodegen.ProviderNodeGenerator().g.graph)
    allowed = {"OAI.PiExponent.normalizedLogWeights", *generated_helper_names}
    project_by_name = {}
    ref_audit = []
    for row in actual_refs:
        fail(row["owner"] != {"kind": "OwnModule", "module": generated_pf["data"]["actual_module_identity"]},
             "n2z solution/helper is not owned by the generated module: " + row["name"])
        names = set(row["typeRefs"] + row["valueRefs"])
        fail(prep.NAME in names or row["name"] in names,
             "n2z proof self-references its statement/target: " + row["name"])
        project = {name for name in names if name in graph or name.startswith(
            ("OAI.", "Definitions.", "Theorems.", "Solutions.", "_private.OAI."))}
        fail(not project <= allowed, "n2z proof has unavailable project references: " + str(sorted(project - allowed)))
        project_by_name[row["name"]] = sorted(project)
        ref_audit.append({"name": row["name"], "project_refs": sorted(project),
                          "owner": row["owner"], "axioms": row["axioms"],
                          "closed_type_and_proof": row["closedType"] and row["closedValue"]})
    # Assert exact source proof expressions and generated declarations are all ordinary public theorem commands.
    zero = witness["helpers"][0]
    fail(zero["source_graph_name"] != "OAI.PiExponent.normalizedLogWeights_zero"
         or zero["raw_proof_suffix_utf8"] != ":= rfl"
         or zero["generated_companion"] is not False,
         "n2z zero helper is not the exact source simp-rfl theorem")
    outputs = [STAGE / "original-type.json", STAGE / "generated-type.json", STAGE / "proof-references.json"]
    outputs += [ROOT / manifest[key][side] for key in ("inline_type_json_outputs", "public_inline_type_json_outputs")
                for side in ("original", "generated")]
    implementations = [SELF, Path(prep.__file__), Path(staging.__file__), Path(refs_producer.__file__),
                       Path(nodegen.__file__), Path(kernel.__file__), Path(refs.__file__),
                       Path(context.__file__), Path(standalone.__file__)]
    generator, _, _ = staging.frontier.promoted_generator()
    report = {
        "schema_version": 1, "artifact_kind": "successive-approximations-n2z-kernel-certificate",
        "node": prep.KEY, "theorem_name": prep.NAME, "source_commit": manifest["source_commit"],
        "source_components": manifest["source_components"], "source_command_witness": kernel.source_command_witness(manifest, generator),
        "zero_helper_ast_witness": zero, "definition": definition,
        "stage_manifest_sha256": sha(STAGE / "manifest.json"),
        "preparation_sha256": sha(STAGE / "preparation.json"),
        "metadata_sha256": sha(STAGE / "academic-metadata.json"),
        "reconstruction_script_sha256": reconstructed_sha,
        "compiler_records": {name: {"record": row["record"], "record_sha256": row["record_sha256"],
                                     "seconds": row["data"]["seconds"], "mode": row["data"]["mode"],
                                     "actual_module_identity": row["data"]["actual_module_identity"],
                                     "dependency_oleans": row["data"]["dependency_oleans"]}
                              for name, row in rows.items()},
        "preflights": rows, "types_equal": True,
        "source_generated_inline_helper_types_equal": [row["source_graph_name"] for row in manifest["public_inline_ci_requests"]],
        "proof_references": actual_refs, "proof_reference_project_names": project_by_name,
        "axiom_audits": {key: sorted(value) for key, value in audits.items()},
        "proof_reference_axioms": "Std3", "proof_axioms": "Std3",
        "max_file_seconds": max(row["data"]["seconds"] for row in rows.values()),
        "output_json_sha256": {rel(path): sha(path) for path in outputs},
        "implementation_hashes": {rel(path): sha(path) for path in implementations},
        "input_hashes": manifest["input_hashes"], "validated": True,
        "Lean_started_by_validator": False, "API_used": False, "submission_ready": False,
    }
    raw = (json.dumps(report, indent=2, ensure_ascii=False) + "\n").encode()
    if CERT.exists() and CERT.read_bytes() != raw:
        raise ValueError("Existing n2z certificate differs; preserve it before retrying")
    if not CERT.exists(): CERT.write_bytes(raw)
    return report


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certify-existing", action="store_true", required=True)
    parser.parse_args()
    print(json.dumps(certify(), indent=2, ensure_ascii=False))
