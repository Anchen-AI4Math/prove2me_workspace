"""Isolated correction of ap6/c3's multi-module source snapshot (pure Python)."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import shutil

import stage_ap6_proved_children as old
import stage_parameter_proved_children as producer
import preflight_staged_module as runner

TASK, ROOT, V = old.TASK, old.ROOT, old.V
D = V / "ap6/c3e"
LIMITS = "OAI.NumberTheory.PiExponent.Analysis.DimensionLimits"
DIMENSION = "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension"
HELPERS = old.HELPERS["c3"]


def config():
    c = old.configure("c3")
    previous = V / "ap6/c3"
    for key, value in list(c.items()):
        if isinstance(value, Path) and value.is_relative_to(previous):
            c[key] = D / value.relative_to(previous)
    return c


def impl_hashes():
    paths = (Path(__file__), Path(old.__file__), Path(producer.__file__),
             TASK / "scripts/validate_ap6_c3e_dimension_child.py")
    return {producer.task_rel(p): old.sha(p) for p in paths}


def owners(c):
    m = old.read(c["parent_manifest"])
    components = m["source_components"]
    if ([x["source_module"] for x in components] != [LIMITS, DIMENSION]
            or m["theorem_name"] != c["theorem"]):
        raise ValueError("Certified source components no longer identify Dimension")
    requests = m["public_inline_ci_requests"]
    rows = {r["source_graph_name"]: r["source_module"] for r in requests}
    if (len(requests) != len(rows) or set(rows) != set(HELPERS)
            or [rows[n] for n in HELPERS] != [LIMITS, LIMITS, *([DIMENSION] * 5)]):
        raise ValueError("AST-selected public source helper owners changed")
    for component in components:
        for key, hashkey in (("source", "source_sha256"),
                             ("original_source", "original_source_sha256")):
            if old.sha(ROOT / component[key]) != component[hashkey]:
                raise ValueError("Certified source component bytes changed")
    return {c["theorem"]: DIMENSION, **rows}


def catalog(c, source: Path, *, child: bool):
    names = owners(c)
    out = D / ("child-helper-catalog.json" if child else "source-helper-catalog.json")
    producer.dump(out, {"schema_version": 1, "artifact_kind": "ap6-c3e-exact-provided-owner-catalog",
        "theorem_name": c["theorem"], "provided_names": list(HELPERS),
        "source_owner_by_name": names, "child_owner": c["module"],
        "source_components_sha256": old.sha(c["parent_manifest"]),
        "parent_validation_sha256": old.sha(c["parent_validation"]),
        "snapshot": producer.task_rel(source), "snapshot_sha256": old.sha(source),
        "type_only": True, "actual_imported_ci_required": True,
        "implementation_hashes": impl_hashes(), "validated": False})
    return out


def seal(c, *, child: bool, cat: Path):
    manifest_path = c["snapshot_manifest"] if child else c["source_snapshot_manifest"]
    manifest = old.read(manifest_path)
    manifest["input_hashes"].update(impl_hashes())
    manifest["input_hashes"][producer.task_rel(cat)] = old.sha(cat)
    manifest["implementation_hashes"] = impl_hashes()
    manifest["helper_catalog_sha256"] = old.sha(cat)
    manifest["parent_validation_sha256"] = old.sha(c["parent_validation"])
    producer.dump(manifest_path, manifest)
    prep_path = c["snapshot_preparation"] if child else c["preparation"]
    prep = old.read(prep_path)
    prep["implementation_hashes"] = impl_hashes()
    prep["helper_catalog_sha256"] = old.sha(cat)
    prep["manifest_sha256"] = old.sha(c["snapshot_manifest"] if child else c["source_manifest"])
    if not child:
        prep["source_snapshot_manifest_sha256"] = old.sha(c["source_snapshot_manifest"])
    producer.dump(prep_path, prep)


def check(c, *, child=False):
    old.accepted_pins(c)
    names = owners(c)
    producer.check_only(c)
    if c["source"].read_bytes() != old.configure("c3")["source"].read_bytes():
        raise ValueError("Corrected child proof differs from already emitted c3 source")
    source = c["source_snapshot"].read_text(encoding="utf-8")
    header = "import Lean\nimport " + LIMITS + "\nimport " + DIMENSION + "\n"
    if not source.startswith(header):
        raise ValueError("Corrected source snapshot lacks exact certified imports")
    for name, module in names.items():
        needle = "ParameterSourceSnapshot.exportSource `" + name + " " + json.dumps(module) + " "
        if source.count(needle) != 1:
            raise ValueError("Corrected source owner probe differs: " + name)
    for path, cat in ((c["source_snapshot_manifest"], D/"source-helper-catalog.json"),
                      (c["snapshot_manifest"], D/"child-helper-catalog.json")):
        if not path.exists():
            if child:
                raise ValueError("Expected child snapshot manifest missing")
            continue
        m = old.read(path)
        if (m.get("implementation_hashes") != impl_hashes()
                or m.get("helper_catalog_sha256") != old.sha(cat)
                or m["input_hashes"].get(producer.task_rel(cat)) != old.sha(cat)):
            raise ValueError("Corrected snapshot manifest/catalog pins differ")
        runner.verify_manifest_inputs(m)
        path_source = c["snapshot"] if path == c["snapshot_manifest"] else c["source_snapshot"]
        runner.verify_source_certificate(path_source.resolve(), m)
        runner.certified_imports(path_source.resolve(), m)
    m = old.read(c["source_manifest"])
    if m.get("implementation_hashes") != impl_hashes():
        raise ValueError("Corrected proved-child source implementation pins differ")
    runner.verify_manifest_inputs(m)
    runner.verify_source_certificate(c["source"].resolve(), m)
    runner.certified_imports(c["source"].resolve(), m)
    for path, key in ((c["preparation"], "source_manifest"),):
        if old.read(path)["manifest_sha256"] != old.sha(c[key]):
            raise ValueError("Corrected preparation manifest pin differs")
    return {"check_only": True, "stage": "ap6/c3e", "source_sha256": old.sha(c["source"]),
            "source_snapshot_sha256": old.sha(c["source_snapshot"]),
            "source_owner_by_name": names, "Lean_started": False, "API_used": False}


def prepare(c):
    if D.exists() and any(D.iterdir()):
        if c["source_snapshot_manifest"].exists() and (D / "source-helper-catalog.json").exists():
            raise ValueError("c3e already staged; use --check-only to preserve preimages")
        archive = D / "partial-preimage"
        archive.mkdir(exist_ok=True)
        for key in ("accepted_capture", "source", "source_manifest", "preparation",
                    "source_snapshot", "source_snapshot_manifest"):
            path = c[key]
            if path.exists():
                target = archive / (key + "-" + path.name)
                if not target.exists():
                    shutil.copy2(path, target)
    names = owners(c)
    producer.prepare(c)
    source = c["source_snapshot"].read_text(encoding="utf-8")
    source = source.replace("import " + LIMITS + "\n", "import " + LIMITS + "\nimport " + DIMENSION + "\n", 1)
    for name, module in ((c["theorem"], names[c["theorem"]]),):
        old_probe = "ParameterSourceSnapshot.exportSource `" + name + " " + json.dumps(LIMITS) + " "
        new_probe = "ParameterSourceSnapshot.exportSource `" + name + " " + json.dumps(module) + " "
        if source.count(old_probe) != 1:
            raise ValueError("Source probe template anchor missing: " + name)
        source = source.replace(old_probe, new_probe, 1)
    anchor = "PiExponentInterfaceSnapshot.exportSnapshot #[`" + c["theorem"] + "]"
    replacement = "PiExponentInterfaceSnapshot.exportSnapshot #[`" + c["theorem"] + ", " + ", ".join("`" + n for n in HELPERS) + "]"
    if source.count(anchor) != 1:
        raise ValueError("Source type export anchor missing")
    source = source.replace(anchor, replacement, 1)
    for i, name in enumerate(HELPERS, 1):
        output = D / ("source-helper-references-" + str(i) + ".json")
        source += ("\nrun_meta do\n  ParameterSourceSnapshot.exportSource `" + name + " "
                   + json.dumps(names[name]) + " " + json.dumps(output.resolve().as_posix())
                   + "\n#print axioms " + name + "\n")
    c["source_snapshot"].write_text(source, encoding="utf-8", newline="\n")
    cat = catalog(c, c["source_snapshot"], child=False)
    sm = old.read(c["source_snapshot_manifest"])
    sm["output_sha256"] = old.sha(c["source_snapshot"])
    sm["imports"] = ["Lean", LIMITS, DIMENSION]
    sm["module"] = DIMENSION
    second = old.read(c["parent_manifest"])["source_components"][1]
    for key in ("source", "original_source"):
        sm["input_hashes"][producer.task_rel(ROOT / second[key])] = second[key + "_sha256"]
    producer.dump(c["source_snapshot_manifest"], sm)
    source_manifest = old.read(c["source_manifest"])
    source_manifest["input_hashes"].update(impl_hashes())
    source_manifest["input_hashes"][producer.task_rel(cat)] = old.sha(cat)
    source_manifest["implementation_hashes"] = impl_hashes()
    source_manifest["helper_catalog_sha256"] = old.sha(cat)
    source_manifest["source_module"] = DIMENSION
    source_manifest["source_sha256"] = second["source_sha256"]
    producer.dump(c["source_manifest"], source_manifest)
    seal(c, child=False, cat=cat)
    result = check(c)
    result["source_compile_command"] = ("python scripts/preflight_staged_module.py ap6/c3e/Theorems/Thm_OAI_PiExponent_exists_dimension_margin.lean "
        "--root ap6/c3e --imports-manifest ap6/c3e/child-module.json --emit-olean")
    result["source_snapshot_compile_command"] = ("python scripts/preflight_staged_module.py ap6/c3e/SourceSnapshot.lean "
        "--root ap6/c3e --imports-manifest ap6/c3e/source-snapshot.json")
    return result


def bind(c):
    check(c)
    result = producer.bind(c)
    source = c["snapshot"].read_text(encoding="utf-8")
    anchor = "PiExponentInterfaceSnapshot.exportSnapshot #[`" + c["theorem"] + "]"
    replacement = "PiExponentInterfaceSnapshot.exportSnapshot #[`" + c["theorem"] + ", " + ", ".join("`" + n for n in HELPERS) + "]"
    if source.count(anchor) != 1:
        raise ValueError("Child type export anchor missing")
    source = source.replace(anchor, replacement, 1)
    for i, name in enumerate(HELPERS, 1):
        output = D / ("child-helper-references-" + str(i) + ".json")
        source += ("\nrun_meta do\n  ParameterChildSnapshot.exportChild `" + name + " "
                   + json.dumps(c["module"]) + " " + json.dumps(output.resolve().as_posix())
                   + "\n#print axioms " + name + "\n")
    c["snapshot"].write_text(source, encoding="utf-8", newline="\n")
    cat = catalog(c, c["snapshot"], child=True)
    sm = old.read(c["snapshot_manifest"])
    sm["output_sha256"] = old.sha(c["snapshot"])
    producer.dump(c["snapshot_manifest"], sm)
    seal(c, child=True, cat=cat)
    prep = old.read(c["snapshot_preparation"])
    prep["source_sha256"] = old.sha(c["snapshot"])
    prep["manifest_sha256"] = old.sha(c["snapshot_manifest"])
    producer.dump(c["snapshot_preparation"], prep)
    check(c, child=True)
    return {"bound": True, "stage": "ap6/c3e", "child_olean_sha256": sm["child_olean_sha256"],
            "snapshot_compile_command": result["snapshot_compile_command"].replace("--root ap4/", "--root ap6/"),
            "Lean_started": False, "API_used": False}


def main():
    ap = argparse.ArgumentParser()
    modes = ap.add_mutually_exclusive_group(required=True)
    for flag in ("prepare", "check-only", "bind"):
        modes.add_argument("--" + flag, action="store_true")
    args = ap.parse_args()
    c = config()
    if args.prepare:
        result = prepare(c)
    elif args.bind:
        result = bind(c)
    else:
        result = check(c, child=c["snapshot_manifest"].exists())
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
