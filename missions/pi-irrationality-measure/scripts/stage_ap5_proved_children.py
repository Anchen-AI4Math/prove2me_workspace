"""Stage actual proved successors of the successive-approximations nodes.

Pure Python only.  The imported producer supplies source and type-only snapshot
generation; this adapter checks the node-specific certified parent and exact
platform receipt before enabling it.  No Lean compiler or API is invoked.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil

import stage_parameter_proved_children as producer

TASK, ROOT, V = producer.TASK, producer.ROOT, producer.V
SPECS = {
    "c1": ("n1", "exists_successive_approximations", "publication-draft"),
    "c2": ("n2z", "exists_normalized_selection_of_selector", "publication-wire-1"),
}
HELPERS = (
    "OAI.PiExponent.normalizedLogWeights_zero",
    "OAI.PiExponent.normalizedLogWeights_succ",
    "OAI.PiExponent.reverse_logWeights_prod",
)


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def implementations():
    paths = (Path(__file__), TASK / "scripts/validate_ap5_proved_children.py",
             Path(producer.__file__))
    return {producer.task_rel(path): sha(path) for path in paths}


def archive_preimages(c):
    for key in ("source_manifest", "preparation", "source_snapshot",
                "source_snapshot_manifest"):
        path = c[key]
        before = path.with_name(path.name + ".before-ap5-hardening")
        if path.exists() and not before.exists():
            shutil.copyfile(path, before)
    catalog = V / "ap5" / c["stage"] / "source-helper-catalog.json"
    before = catalog.with_name(catalog.name + ".before-ap5-hardening")
    if catalog.exists() and not before.exists():
        shutil.copyfile(catalog, before)


def configure(stage: str):
    node, slug, pubdir = SPECS[stage]
    c = {"stage": stage, "slug": slug, "kind": "ap5",
         "theorem": "OAI.PiExponent." + slug,
         "module": "Theorems.Thm_OAI_PiExponent_" + slug}
    c["parent"] = V / "ap4" / node
    c["parent_manifest"] = c["parent"] / "manifest.json"
    c["parent_validation"] = c["parent"] / (node + "-validation.json")
    c["publication"] = c["parent"] / pubdir / "publication.json"
    c["accepted_capture"] = V / "ap5" / stage / "own-accepted-capture.json"
    c["source"] = V / "ap5" / stage / "Theorems" / ("Thm_OAI_PiExponent_" + slug + ".lean")
    child = V / "ap5" / stage
    for key, name in {
        "source_manifest": "child-module.json", "preparation": "child-source-preparation.json",
        "snapshot": "ChildSnapshot.lean", "snapshot_manifest": "child-snapshot.json",
        "snapshot_preparation": "child-snapshot-preparation.json", "child_type": "child-type.json",
        "child_refs": "child-proof-references.json", "source_snapshot": "SourceSnapshot.lean",
        "source_snapshot_manifest": "source-snapshot.json", "source_type": "source-type.json",
        "source_refs": "source-proof-references.json",
    }.items():
        c[key] = child / name
    c["kind"] = "ap5"
    c["runtime_sha256"] = read(c["parent_manifest"])["runtime_sha256"]
    return c


def accepted_pins(c):
    m, v, p = (read(c[key]) for key in ("parent_manifest", "parent_validation", "publication"))
    theorem = c["theorem"]
    if m.get("theorem_name") != theorem or v.get("theorem_name") != theorem or p.get("theorem_name") != theorem:
        raise ValueError("Parent theorem identity mismatch")
    if m.get("source_commit") != "adc7f1241b42e322a6451854ab7e4b4c146bf78a":
        raise ValueError("Unexpected source commit")
    if not (v.get("validated") is True and v.get("types_equal") is True and v.get("proof_axioms") == "Std3"):
        raise ValueError("Parent kernel/type/axiom certificate incomplete")
    if v.get("stage_manifest_sha256") != sha(c["parent_manifest"]):
        raise ValueError("Parent manifest changed since proof validation")
    if not isinstance(v.get("implementation_hashes"), dict) or not isinstance(v.get("output_json_sha256"), dict):
        raise ValueError("Parent implementation/output certificate domain missing")
    for relpath, digest in v["implementation_hashes"].items():
        if sha(TASK / relpath) != digest:
            raise ValueError("Certified parent implementation changed: " + relpath)
    for relpath, digest in v["output_json_sha256"].items():
        if sha(TASK / relpath) != digest:
            raise ValueError("Certified parent JSON output changed: " + relpath)
    for relpath, digest in v.get("input_hashes", {}).items():
        if sha(TASK / relpath) != digest:
            raise ValueError("Certified parent input changed: " + relpath)
    for component in m["source_components"]:
        for pathkey, hashkey in (("source", "source_sha256"),
                                 ("original_source", "original_source_sha256"),
                                 ("facts", "facts_sha256")):
            if sha(ROOT / component[pathkey]) != component[hashkey]:
                raise ValueError("Certified source component changed: " + pathkey)
    prep = p.get("preparation", {})
    pubdir = c["publication"].parent
    published_payload = pubdir / "publish-payload.json"
    verification_payload = pubdir / "verification-payload.json"
    multipart = pubdir / "verification-request.multipart"
    hashes = prep.get("payload_sha256", {})
    if (sha(published_payload) != hashes.get("publish-payload.json")
            or sha(verification_payload) != hashes.get("verification-payload.json")
            or sha(published_payload) != p.get("publish_intent", {}).get("payload_sha256")
            or sha(verification_payload) != p.get("verify_intent", {}).get("descriptor_sha256")
            or sha(multipart) != p.get("verify_intent", {}).get("multipart_sha256")
            or p.get("verify_intent", {}).get("solution_sha256") != m.get("solution_sha256")
            or prep.get("validation_sha256") != sha(c["parent_validation"])
            or (c["stage"] == "c1" and prep.get("manifest_sha256") != sha(c["parent_manifest"]))
            or (c["stage"] == "c2" and not isinstance(prep.get("manifest_sha256"), str))):
        raise ValueError("Frozen publish/verification payload pins differ")
    payload = read(published_payload)
    verify_payload = read(verification_payload)
    readback = p.get("target_readback", {}).get("body", {})
    if (len(payload.get("problems", [])) != 1
            or any(payload["problems"][0].get(k) != readback.get(k)
                   for k in ("formal_statement", "preamble", "source", "theorem_name"))
            or verify_payload.get("target_theorem_name") != theorem
            or verify_payload.get("file", {}).get("sha256") != m.get("solution_sha256")):
        raise ValueError("Published target/payload/solution bytes are not identical")
    solution = ROOT / m["solution"]
    if sha(solution) != m["solution_sha256"]:
        raise ValueError("Certified parent solution bytes changed")
    if p.get("confirmed_proved") is not True:
        raise ValueError("Own accepted and exact Proved platform receipt pending")
    submission = p.get("last_verify_verdict", {}).get("body", {})
    if (submission.get("status") != "ACCEPTED" or submission.get("id") != p.get("submission_id")
            or readback.get("status") != "Proved" or readback.get("theorem_id") != p.get("theorem_id")
            or p.get("proposal_status") != "Draft"):
        raise ValueError("Terminal receipt identity/status mismatch")
    row = {"theorem_name": theorem, "status": "ACCEPTED_AND_PROVED",
           "verification_record": producer.task_rel(c["publication"]),
           "verification_record_sha256": sha(c["publication"]),
           "theorem_id": p["theorem_id"], "submission_id": p["submission_id"]}
    if c["accepted_capture"].exists():
        captured = read(c["accepted_capture"])
        if captured.get("captured_own_accepted_row") != row or captured.get("publication_sha256") != sha(c["publication"]):
            raise ValueError("Captured own Accepted receipt changed")
    if c["stage"] == "c2":
        dpath = c["parent"] / "definition-input.json"
        d = read(dpath)
        if (d.get("validated") is not True or d.get("source_name") != "OAI.PiExponent.normalizedLogWeights"
                or d.get("platform_module") != "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_SuccessiveApproximations"
                or sha(TASK / d["certificate"]) != d["certificate_sha256"]
                or sha(TASK / d["publication"]) != d["publication_sha256"]
                or sha(TASK / d["output_olean"]) != d["output_olean_sha256"]
                or not all(d.get("checks", {}).values())):
            raise ValueError("Certified normalizedLogWeights definition dependency changed")
    return m, v, p, row


def augment_helper_snapshot(c, *, imported_child: bool):
    """Extend the type-only, actual-owner probe to all three n2z helpers."""
    if c["stage"] != "c2":
        return
    m = read(c["parent_manifest"])
    v = read(c["parent_validation"])
    original = read(c["parent"] / "original-public-inline-types.json")
    generated = read(c["parent"] / "generated-public-inline-types.json")
    if (set(v.get("source_generated_inline_helper_types_equal", [])) != set(HELPERS)
            or {x["name"] for x in original} != set(HELPERS)
            or {x["name"] for x in generated} != set(HELPERS)):
        raise ValueError("n2z source helper catalog is incomplete")
    for a, b in zip(sorted(original, key=lambda x: x["name"]), sorted(generated, key=lambda x: x["name"])):
        if a["name"] != b["name"] or a["type"] != b["type"] or a["levelParams"] != b["levelParams"]:
            raise ValueError("n2z source/generated helper kernel types differ")
        if a["value"] is not None or b["value"] is not None:
            raise ValueError("n2z helper catalog unexpectedly exports proof value")
    path = c["snapshot"] if imported_child else c["source_snapshot"]
    manifest_path = c["snapshot_manifest"] if imported_child else c["source_snapshot_manifest"]
    content = path.read_text(encoding="utf-8")
    single = "PiExponentInterfaceSnapshot.exportSnapshot #[`" + c["theorem"] + "]"
    all_names = "PiExponentInterfaceSnapshot.exportSnapshot #[`" + c["theorem"] + ", " + ", ".join("`" + name for name in HELPERS) + "]"
    if content.count(single) != 1:
        raise ValueError("Type-only snapshot anchor changed")
    content = content.replace(single, all_names, 1)
    function = "ParameterChildSnapshot.exportChild" if imported_child else "ParameterSourceSnapshot.exportSource"
    expected_owner = c["module"] if imported_child else m["source_components"][0]["source_module"]
    extra = ""
    for i, name in enumerate(HELPERS, 1):
        output = V / "ap5" / c["stage"] / (("child-helper-references-" if imported_child else "source-helper-references-") + str(i) + ".json")
        extra += "run_meta do\n  " + function + " `" + name + " " + json.dumps(expected_owner) + " " + json.dumps(str(output.resolve()).replace("\\", "/")) + "\n"
        extra += "#print axioms " + name + "\n"
    content += "\n" + extra
    path.write_text(content, encoding="utf-8", newline="\n")
    manifest = read(manifest_path)
    manifest["output_sha256"] = sha(path)
    producer.dump(manifest_path, manifest)
    if imported_child and c["snapshot_preparation"].exists():
        prep = read(c["snapshot_preparation"])
        prep["source_sha256"] = sha(path)
        prep["manifest_sha256"] = sha(manifest_path)
        producer.dump(c["snapshot_preparation"], prep)
    catalog = V / "ap5" / c["stage"] / ("child-helper-catalog.json" if imported_child else "source-helper-catalog.json")
    producer.dump(catalog, {"schema_version": 1, "source_validation_sha256": sha(c["parent_validation"]),
        "source_original_public_inline_types_sha256": sha(c["parent"] / "original-public-inline-types.json"),
        "source_generated_public_inline_types_sha256": sha(c["parent"] / "generated-public-inline-types.json"),
        "module": expected_owner, "theorem_name": c["theorem"], "provided_names": list(HELPERS),
        "normalizedLogWeights_definition_input": producer.task_rel(c["parent"] / "definition-input.json"),
        "normalizedLogWeights_definition_input_sha256": sha(c["parent"] / "definition-input.json"),
        "snapshot": producer.task_rel(path), "snapshot_sha256": sha(path),
        "type_only": True, "requires_actual_owner_and_proof_refs": True,
        "Lean_started": False, "validated": False})


def seal_stage(c, *, imported_child: bool):
    impl = implementations()
    catalog = V / "ap5" / c["stage"] / ("child-helper-catalog.json" if imported_child else "source-helper-catalog.json")
    if c["stage"] == "c2":
        content = read(catalog)
        content["implementation_hashes"] = impl
        producer.dump(catalog, content)
    if imported_child:
        manifest_path, prep_path = c["snapshot_manifest"], c["snapshot_preparation"]
    else:
        manifest_path, prep_path = c["source_manifest"], c["preparation"]
    manifest = read(manifest_path)
    pins = manifest["input_hashes"]
    pins.update(impl)
    manifest["implementation_hashes"] = impl
    manifest["parent_output_json_sha256"] = read(c["parent_validation"])["output_json_sha256"]
    if c["stage"] == "c2":
        pins[producer.task_rel(catalog)] = sha(catalog)
    producer.dump(manifest_path, manifest)
    if not imported_child:
        snapshot_manifest = read(c["source_snapshot_manifest"])
        snapshot_manifest["input_hashes"].update(impl)
        snapshot_manifest["implementation_hashes"] = impl
        snapshot_manifest["parent_output_json_sha256"] = read(c["parent_validation"])["output_json_sha256"]
        if c["stage"] == "c2":
            snapshot_manifest["input_hashes"][producer.task_rel(catalog)] = sha(catalog)
        producer.dump(c["source_snapshot_manifest"], snapshot_manifest)
    prep = read(prep_path)
    prep["implementation_hashes"] = impl
    prep["parent_output_json_sha256"] = read(c["parent_validation"])["output_json_sha256"]
    prep["manifest_sha256"] = sha(manifest_path)
    if not imported_child:
        prep["source_snapshot_manifest_sha256"] = sha(c["source_snapshot_manifest"])
    if c["stage"] == "c2":
        prep["helper_catalog_sha256"] = sha(catalog)
    producer.dump(prep_path, prep)


def verify_seal(c):
    impl = implementations()
    for path in (c["source_manifest"], c["source_snapshot_manifest"]):
        manifest = read(path)
        if (manifest.get("implementation_hashes") != impl
                or manifest.get("parent_output_json_sha256") != read(c["parent_validation"])["output_json_sha256"]):
            raise ValueError("Staged manifest implementation/output pin changed")
        for name, digest in impl.items():
            if manifest.get("input_hashes", {}).get(name) != digest:
                raise ValueError("Staged manifest misses its exact adapter implementation pin")
    prep = read(c["preparation"])
    if (prep.get("implementation_hashes") != impl
            or prep.get("manifest_sha256") != sha(c["source_manifest"])
            or prep.get("source_snapshot_manifest_sha256") != sha(c["source_snapshot_manifest"])
            or prep.get("parent_output_json_sha256") != read(c["parent_validation"])["output_json_sha256"]):
        raise ValueError("Staged source-preparation implementation/output pin changed")
    if c["stage"] == "c2":
        catalog = V / "ap5" / c["stage"] / "source-helper-catalog.json"
        doc = read(catalog)
        if (doc.get("implementation_hashes") != impl
                or prep.get("helper_catalog_sha256") != sha(catalog)
                or read(c["source_manifest"])["input_hashes"].get(producer.task_rel(catalog)) != sha(catalog)
                or read(c["source_snapshot_manifest"])["input_hashes"].get(producer.task_rel(catalog)) != sha(catalog)):
            raise ValueError("Source helper catalog implementation/pin changed")


def verify_child_seal(c):
    impl = implementations()
    manifest = read(c["snapshot_manifest"])
    prep = read(c["snapshot_preparation"])
    if (any(manifest.get("input_hashes", {}).get(name) != digest for name, digest in impl.items())
            or manifest.get("implementation_hashes") != impl
            or manifest.get("parent_output_json_sha256") != read(c["parent_validation"])["output_json_sha256"]
            or prep.get("implementation_hashes") != impl
            or prep.get("manifest_sha256") != sha(c["snapshot_manifest"])
            or prep.get("source_sha256") != sha(c["snapshot"])
            or prep.get("parent_output_json_sha256") != read(c["parent_validation"])["output_json_sha256"]):
        raise ValueError("Child snapshot manifest/preparation implementation pin changed")
    if c["stage"] == "c2":
        catalog = V / "ap5" / c["stage"] / "child-helper-catalog.json"
        if (read(catalog).get("implementation_hashes") != impl
                or read(catalog).get("snapshot_sha256") != sha(c["snapshot"])
                or prep.get("helper_catalog_sha256") != sha(catalog)
                or manifest["input_hashes"].get(producer.task_rel(catalog)) != sha(catalog)):
            raise ValueError("Child helper catalog implementation/pin changed")


producer.accepted_pins = accepted_pins


def main():
    ap = argparse.ArgumentParser()
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--prepare", action="store_true")
    g.add_argument("--check-only", action="store_true")
    g.add_argument("--bind", action="store_true")
    ap.add_argument("--stage", choices=SPECS, required=True)
    args = ap.parse_args()
    c = configure(args.stage)
    if args.prepare:
        archive_preimages(c)
        out = producer.prepare(c)
        augment_helper_snapshot(c, imported_child=False)
        seal_stage(c, imported_child=False)
    elif args.check_only:
        out = producer.check_only(c)
        verify_seal(c)
    else:
        verify_seal(c)
        out = producer.bind(c)
        augment_helper_snapshot(c, imported_child=True)
        seal_stage(c, imported_child=True)
    for key in ("compile_command", "source_snapshot_compile_command", "snapshot_compile_command"):
        if key in out:
            out[key] = out[key].replace("--root ap4/", "--root ap5/")
    print(json.dumps(out, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
