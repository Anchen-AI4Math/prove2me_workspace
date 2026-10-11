"""Pure-Python staging for three Accepted approximation/dimension proved children.

The frozen source proof is copied byte-for-byte except for the literal top-level
`solution` theorem name and its `#print axioms` target.  Root alone compiles.
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
    "c1": ("nodes-preview", "exists_uniform_weight_error_margin", "validation.json", "publication.json"),
    "c2": ("independent", "exists_minimum_weight", "validation.json", "publication.json"),
    "c3": ("provider-nodes-preview", "exists_dimension_margin", "dimension-margin-validation-complete.json",
           "dimension-margin-publication-v2/publication.json"),
}
HELPERS = {
    "c1": ("OAI.PiExponent.exists_weight_error_margin",
           "OAI.PiExponent.reciprocal_sum_le_common_bound"),
    "c2": (),
    "c3": ("OAI.PiExponent.tendsto_nat_add_one_div_pow",
           "OAI.PiExponent.tendsto_pow_div_nat_add_one",
           "OAI.PiExponent.dimensionK_div_W_le",
           "OAI.PiExponent.dimensionV_geometric_lower",
           "OAI.PiExponent.dimension_error_le",
           "OAI.PiExponent.tendsto_dimension_error_majorant",
           "OAI.PiExponent.tendsto_dimension_collision"),
}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def impl_hashes():
    paths = (Path(__file__), TASK / "scripts/validate_ap6_proved_children.py", Path(producer.__file__))
    return {producer.task_rel(p): sha(p) for p in paths}


def configure(which: str):
    kind, slug, validation_name, publication_name = SPECS[which]
    theorem = "OAI.PiExponent." + slug
    parent = V / kind / ("OAI_PiExponent_" + slug)
    d = V / "ap6" / which
    c = {"stage": which, "kind": "ap6", "slug": slug, "parent": parent,
         "parent_manifest": parent / "manifest.json", "parent_validation": parent / validation_name,
         "publication": parent / publication_name, "theorem": theorem,
         "module": "Theorems.Thm_OAI_PiExponent_" + slug,
         "accepted_capture": d / "own-accepted-capture.json",
         "source": d / "Theorems" / ("Thm_OAI_PiExponent_" + slug + ".lean"),
         "source_manifest": d / "child-module.json", "preparation": d / "child-source-preparation.json",
         "source_snapshot": d / "SourceSnapshot.lean", "source_snapshot_manifest": d / "source-snapshot.json",
         "source_type": d / "source-type.json", "source_refs": d / "source-proof-references.json",
         "snapshot": d / "ChildSnapshot.lean", "snapshot_manifest": d / "child-snapshot.json",
         "snapshot_preparation": d / "child-snapshot-preparation.json",
         "child_type": d / "child-type.json", "child_refs": d / "child-proof-references.json"}
    c["runtime_sha256"] = read(c["parent_manifest"])["runtime_sha256"]
    return c


def source_component(m):
    if m.get("source_components"):
        return m["source_components"][0]
    return m


def accepted_pins(c):
    m, v, p = (read(c[key]) for key in ("parent_manifest", "parent_validation", "publication"))
    name = c["theorem"]
    if (m.get("theorem_name") != name or p.get("theorem_name") != name
            or v.get("validated") is not True or v.get("kernel_types_equal") is not True
            or v.get("standard_axioms_only", v.get("Std3_only")) is not True
            or p.get("confirmed_proved") is not True
            or p.get("target_readback", {}).get("body", {}).get("status") != "Proved"
            or p.get("target_readback", {}).get("body", {}).get("theorem_id") != p.get("theorem_id")):
        raise ValueError("Certified parent/own Proved gate incomplete: " + name)
    progress = read(V / "verified-stage-progress.json")
    rows = [r for r in progress["proofs"] if r.get("theorem_name") == name]
    if len(rows) != 1:
        raise ValueError("Expected one verified own proof progress row")
    row = rows[0]
    if (row.get("status") != "ACCEPTED_AND_PROVED"
            or row.get("verification_record") != producer.task_rel(c["publication"])
            or row.get("verification_record_sha256") != sha(c["publication"])
            or row.get("theorem_id") != p.get("theorem_id")
            or row.get("submission_id") != p.get("submission_id")):
        raise ValueError("Own Accepted/Proved row and exact public receipt differ")
    solution = ROOT / m["solution"]
    if sha(solution) != m["solution_sha256"]:
        raise ValueError("Parent certified solution bytes changed")
    component = source_component(m)
    for pathkey, hashkey in (("source", "source_sha256"), ("original_source", "original_source_sha256")):
        if sha(ROOT / component[pathkey]) != component[hashkey]:
            raise ValueError("Parent source component changed: " + pathkey)
    if m.get("source_commit") != "adc7f1241b42e322a6451854ab7e4b4c146bf78a":
        raise ValueError("Source commit changed")
    if c["stage"] == "c3":
        if v.get("manifest_sha256") != sha(c["parent_manifest"]):
            raise ValueError("Dimension parent manifest differs from kernel certificate")
        for key in ("implementation_hashes", "output_json_sha256", "input_hashes"):
            for rel, digest in v[key].items():
                if sha(TASK / rel) != digest:
                    raise ValueError("Dimension parent certified input changed: " + rel)
    else:
        for key, filename in (("original_type_sha256", "original-type.json"),
                              ("generated_type_sha256", "generated-type.json")):
            if sha(c["parent"] / filename) != v[key]:
                raise ValueError("Legacy parent kernel type output changed")
    if c["accepted_capture"].exists():
        captured = read(c["accepted_capture"])
        if captured.get("captured_own_accepted_row") != row or captured.get("publication_sha256") != sha(c["publication"]):
            raise ValueError("Own Accepted capture changed")
    return m, v, p, row


producer.accepted_pins = accepted_pins


def archive_once(c):
    for key in ("source_manifest", "preparation", "source_snapshot", "source_snapshot_manifest",
                "snapshot", "snapshot_manifest", "snapshot_preparation"):
        path = c[key]
        old = path.with_name(path.name + ".before-ap6-regeneration")
        if path.exists() and not old.exists():
            shutil.copyfile(path, old)


def helper_catalog(c, *, imported_child: bool):
    helpers = HELPERS[c["stage"]]
    if not helpers:
        return
    source = c["snapshot"] if imported_child else c["source_snapshot"]
    manifest_path = c["snapshot_manifest"] if imported_child else c["source_snapshot_manifest"]
    text = source.read_text(encoding="utf-8")
    one = "PiExponentInterfaceSnapshot.exportSnapshot #[`" + c["theorem"] + "]"
    all_names = "PiExponentInterfaceSnapshot.exportSnapshot #[`" + c["theorem"] + ", " + ", ".join("`" + n for n in helpers) + "]"
    if text.count(one) != 1:
        raise ValueError("Type-only helper snapshot insertion anchor changed")
    text = text.replace(one, all_names, 1)
    m = read(c["parent_manifest"])
    owner = c["module"] if imported_child else source_component(m)["source_module"]
    function = "ParameterChildSnapshot.exportChild" if imported_child else "ParameterSourceSnapshot.exportSource"
    for i, name in enumerate(helpers, 1):
        output = V / "ap6" / c["stage"] / (("child" if imported_child else "source") + "-helper-references-" + str(i) + ".json")
        text += "\nrun_meta do\n  " + function + " `" + name + " " + json.dumps(owner) + " " + json.dumps(str(output.resolve()).replace("\\", "/")) + "\n"
        text += "#print axioms " + name + "\n"
    source.write_text(text, encoding="utf-8", newline="\n")
    manifest = read(manifest_path)
    manifest["output_sha256"] = sha(source)
    producer.dump(manifest_path, manifest)
    if imported_child and c["snapshot_preparation"].exists():
        prep = read(c["snapshot_preparation"])
        prep["source_sha256"] = sha(source)
        prep["manifest_sha256"] = sha(manifest_path)
        producer.dump(c["snapshot_preparation"], prep)
    catalog = V / "ap6" / c["stage"] / ("child-helper-catalog.json" if imported_child else "source-helper-catalog.json")
    data = {"schema_version": 1, "theorem_name": c["theorem"], "module": owner,
            "provided_names": list(helpers), "source_validation_sha256": sha(c["parent_validation"]),
            "snapshot": producer.task_rel(source), "snapshot_sha256": sha(source),
            "type_only": True, "actual_owner_and_proof_refs_required": True,
            "implementation_hashes": impl_hashes(), "Lean_started": False, "validated": False}
    if c["stage"] == "c3":
        data["parent_original_public_inline_types_sha256"] = sha(c["parent"] / "original-public-inline-types.json")
        data["parent_generated_public_inline_types_sha256"] = sha(c["parent"] / "generated-public-inline-types.json")
    producer.dump(catalog, data)


def seal(c, *, imported_child: bool):
    impl = impl_hashes()
    helpers = HELPERS[c["stage"]]
    catalog = V / "ap6" / c["stage"] / ("child-helper-catalog.json" if imported_child else "source-helper-catalog.json")
    manifest_path = c["snapshot_manifest"] if imported_child else c["source_manifest"]
    prep_path = c["snapshot_preparation"] if imported_child else c["preparation"]
    manifest = read(manifest_path)
    manifest["input_hashes"].update(impl)
    manifest["implementation_hashes"] = impl
    manifest["parent_validation_sha256"] = sha(c["parent_validation"])
    if helpers:
        manifest["input_hashes"][producer.task_rel(catalog)] = sha(catalog)
        manifest["helper_catalog_sha256"] = sha(catalog)
    producer.dump(manifest_path, manifest)
    if not imported_child:
        snap_manifest = read(c["source_snapshot_manifest"])
        snap_manifest["input_hashes"].update(impl)
        snap_manifest["implementation_hashes"] = impl
        snap_manifest["parent_validation_sha256"] = sha(c["parent_validation"])
        if helpers:
            snap_manifest["input_hashes"][producer.task_rel(catalog)] = sha(catalog)
            snap_manifest["helper_catalog_sha256"] = sha(catalog)
        producer.dump(c["source_snapshot_manifest"], snap_manifest)
    prep = read(prep_path)
    prep["implementation_hashes"] = impl
    prep["parent_validation_sha256"] = sha(c["parent_validation"])
    prep["manifest_sha256"] = sha(manifest_path)
    if not imported_child:
        prep["source_snapshot_manifest_sha256"] = sha(c["source_snapshot_manifest"])
        prep["legacy_parent_type_schema"] = c["stage"] in ("c1", "c2")
    if helpers:
        prep["helper_catalog_sha256"] = sha(catalog)
    producer.dump(prep_path, prep)


def check_seal(c):
    impl = impl_hashes()
    for path in (c["source_manifest"], c["source_snapshot_manifest"]):
        doc = read(path)
        if doc.get("implementation_hashes") != impl or doc.get("parent_validation_sha256") != sha(c["parent_validation"]):
            raise ValueError("ap6 staged source manifest pin changed")
        for rel, digest in impl.items():
            if doc.get("input_hashes", {}).get(rel) != digest:
                raise ValueError("ap6 staged source implementation pin changed")
    prep = read(c["preparation"])
    if (prep.get("implementation_hashes") != impl or prep.get("manifest_sha256") != sha(c["source_manifest"])
            or prep.get("source_snapshot_manifest_sha256") != sha(c["source_snapshot_manifest"])):
        raise ValueError("ap6 source preparation changed")
    if HELPERS[c["stage"]]:
        catalog = V / "ap6" / c["stage"] / "source-helper-catalog.json"
        if (prep.get("helper_catalog_sha256") != sha(catalog)
                or read(catalog).get("implementation_hashes") != impl
                or read(catalog).get("provided_names") != list(HELPERS[c["stage"]])):
            raise ValueError("ap6 source helper catalog changed")


def check_child_seal(c):
    impl = impl_hashes()
    manifest = read(c["snapshot_manifest"])
    prep = read(c["snapshot_preparation"])
    if (manifest.get("implementation_hashes") != impl
            or manifest.get("parent_validation_sha256") != sha(c["parent_validation"])
            or any(manifest.get("input_hashes", {}).get(rel) != digest for rel, digest in impl.items())
            or prep.get("implementation_hashes") != impl
            or prep.get("manifest_sha256") != sha(c["snapshot_manifest"])
            or prep.get("source_sha256") != sha(c["snapshot"])):
        raise ValueError("ap6 child snapshot manifest/preparation changed")
    if HELPERS[c["stage"]]:
        catalog = V / "ap6" / c["stage"] / "child-helper-catalog.json"
        if (manifest.get("helper_catalog_sha256") != sha(catalog)
                or manifest["input_hashes"].get(producer.task_rel(catalog)) != sha(catalog)
                or prep.get("helper_catalog_sha256") != sha(catalog)
                or read(catalog).get("implementation_hashes") != impl
                or read(catalog).get("provided_names") != list(HELPERS[c["stage"]])):
            raise ValueError("ap6 child helper catalog changed")


def main():
    ap = argparse.ArgumentParser()
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--prepare", action="store_true")
    g.add_argument("--check-only", action="store_true")
    g.add_argument("--bind", action="store_true")
    ap.add_argument("--stage", required=True, choices=SPECS)
    args = ap.parse_args()
    c = configure(args.stage)
    if args.prepare:
        archive_once(c)
        result = producer.prepare(c)
        helper_catalog(c, imported_child=False)
        seal(c, imported_child=False)
    elif args.check_only:
        result = producer.check_only(c)
        check_seal(c)
    else:
        check_seal(c)
        result = producer.bind(c)
        helper_catalog(c, imported_child=True)
        seal(c, imported_child=True)
    for key in ("compile_command", "source_snapshot_compile_command", "snapshot_compile_command"):
        if key in result:
            result[key] = result[key].replace("--root ap4/", "--root ap6/")
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
