"""Stage one additive source-CI probe for AP11's original helper owners/refs.

The four AP11 compiler inputs and their producer remain frozen. This is a
separate fifth, bounded, read-only Lean input; this script never runs Lean.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import stage_full_row_minor_node as ap8
import stage_grouped_collision_rate_node as ap11

TASK, ROOT, V, STAGE = ap11.TASK, ap11.ROOT, ap11.V, ap11.STAGE
SELF = Path(__file__).resolve()
FOLDER = STAGE / "source-helper-probe"
PROBE_FILE = "SourceHelperRefs.lean"
MANIFEST = "c5.json"
PREPARATION = "preparation.json"
OUTPUTS = "source-helper-refs"


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha_bytes(raw):
    return hashlib.sha256(raw).hexdigest()


def sha(path):
    return sha_bytes(Path(path).read_bytes())


def read(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def rel(path):
    return Path(path).resolve().relative_to(TASK.resolve()).as_posix()


def workspace_rel(path):
    return Path(path).resolve().relative_to(ROOT.resolve()).as_posix()


def verification_rel(path):
    return Path(path).resolve().relative_to(V.resolve()).as_posix()


def encode(doc):
    return (json.dumps(doc, ensure_ascii=False, indent=2) + "\n").encode()


def stage_files():
    plan_path = STAGE / "preparation.json"
    plan = read(plan_path)
    rows = plan["inline_exact_source_units"]
    need(len(rows) == 30 and len({r["name"] for r in rows}) == 30
         and set(r["module"] for r in rows) == set(ap11.HELPER_NAMES)
         and plan["source_name"] == ap11.TARGET,
         "Frozen AP11 30-helper preparation differs")
    main_files = [STAGE / name for name in
                  [ap11.SOURCE_SNAPSHOT, ap11.GENERATED_SNAPSHOT,
                   ap11.TARGET_OUTPUT, ap11.SOLUTION_OUTPUT,
                   *ap11.MANIFESTS]]
    pins = {rel(p): sha(p) for p in [SELF, Path(ap8.__file__),
            Path(ap11.__file__), ap11.SNAPSHOT_CORE, ap11.RUNTIME,
            TASK / "scripts/preflight_staged_module.py", plan_path, *main_files]}
    imports = ["Lean", ap11.TARGET_MODULE]
    probe = ap8.PROBE.replace("FullRowMinorProofSnapshot", "GroupedCollisionSourceHelperSnapshot")
    source = ("import Lean\nimport " + ap11.TARGET_MODULE + "\n\n" +
              ap11.SNAPSHOT_CORE.read_text(encoding="utf-8").rstrip() + "\n\n" + probe)
    records = []
    for row in rows:
        name, module = row["name"], row["module"]
        output = FOLDER / OUTPUTS / (name.replace(".", "_") + ".json")
        records.append({"name": name, "source_module": module,
                        "output": rel(output), "expected_owner": module})
        source += ("\nrun_meta do\n  GroupedCollisionSourceHelperSnapshot.exportEvidence " +
                   " ".join(json.dumps(x) for x in
                            ["source-helper", workspace_rel(output), name, module]) + "\n")
    raw = source.encode()
    manifest = {
        "schema_version": 1,
        "artifact_kind": "ap11-grouped-collision-source-helper-bounded-compiler-manifest",
        "output": workspace_rel(FOLDER / PROBE_FILE), "output_sha256": sha_bytes(raw),
        "imports": imports, "input_hashes": pins, "runtime_sha256": sha(ap11.RUNTIME),
        "mode": "modecheck", "emit_olean": False, "timeout_seconds": 300,
        "validated": False, "submission_ready": False,
    }
    prep = {
        "schema_version": 1, "artifact_kind": "ap11-additive-source-helper-CI-probe-preparation",
        "source_commit": ap11.COMMIT, "source_target": ap11.TARGET,
        "source_import_module": ap11.TARGET_MODULE,
        "frozen_primary_stage_preparation": rel(plan_path),
        "frozen_primary_stage_preparation_sha256": sha(plan_path),
        "helper_count": 30, "actual_CI_requests": records,
        "probe_sha256": sha_bytes(raw), "manifest_sha256": sha_bytes(encode(manifest)),
        "compile_command": ("python scripts/preflight_staged_module.py " +
            verification_rel(FOLDER / PROBE_FILE) +
            " --root ap11/collision-rate/source-helper-probe --imports-manifest " +
            verification_rel(FOLDER / MANIFEST) + " --timeout-seconds 300"),
        "Lean_started": False, "API_used": False, "validated": False,
        "submission_ready": False,
    }
    return {PROBE_FILE: raw, MANIFEST: encode(manifest), PREPARATION: encode(prep)}


def check_only(generated=None):
    generated = stage_files() if generated is None else generated
    need((FOLDER / OUTPUTS).is_dir(), "Source-helper compiler output directory is missing")
    for filename, raw in generated.items():
        need((FOLDER / filename).is_file() and (FOLDER / filename).read_bytes() == raw,
             "Additive source-helper stage differs: " + filename)
    manifest = read(FOLDER / MANIFEST)
    ap11.runner.verify_manifest_inputs(manifest)
    ap11.runner.verify_source_certificate(FOLDER / PROBE_FILE, manifest)
    return {"checked_files": len(generated), "helper_CIs": 30,
            "all_hashes_match": True, "Lean_started": False, "API_used": False,
            "validated": False, "submission_ready": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--prepare", action="store_true")
    mode.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    generated = None
    if args.prepare:
        generated = stage_files()
        (FOLDER / OUTPUTS).mkdir(parents=True, exist_ok=True)
        for filename, raw in generated.items():
            path = FOLDER / filename
            if path.exists():
                need(path.read_bytes() == raw, "Refusing to rewrite additive source-helper probe")
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(raw)
    print(json.dumps(check_only(generated), ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
