"""Root-granted, serial actual afb1 native author calls; retain every failure."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import time
from pathlib import Path

sys.dont_write_bytecode = True
TASK = Path(__file__).resolve().parents[1]
WORKSPACE = TASK.parents[1]
OUT = TASK / "verification/formalization-analytic-factorial-preparation-2026-10-07"
PROJECT = OUT / ".rt/afb1"
PYTHON = "C:/Users/anche/AppData/Local/Programs/Python/Python312/python.exe"
LAYOUT_SHA = "f2b45465770375bf49131450fa3d72b3d9646fd4f940bf17199bbc42ee317a94"
REV = "0df444a360eaa60ab8c11dca51a86af692955474"


def binding(path: Path) -> dict:
    data = path.read_bytes()
    base = TASK if path.is_relative_to(TASK) else WORKSPACE
    return {"task_relative" if base == TASK else "root_relative": path.relative_to(base).as_posix(),
            "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}


def load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def dump(path: Path, value: dict) -> None:
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def gate() -> dict:
    grant = load(OUT / "Root-author-lane1-grant.json")
    assert grant["Root_explicit_grant"] and grant["lane"] == 1
    assert grant["owner"] == "factorial_bound_author_1007"
    assert grant["private_project"] == PROJECT.relative_to(TASK).as_posix()
    layout_path = OUT / "native-inputs-layout-v2-audit.json"
    assert binding(layout_path)["sha256"] == LAYOUT_SHA
    layout = load(layout_path)
    rows = layout["new_sources"] + [layout["phase_fullpath_layout_copy"]]
    for copy in layout["actual_source_copy_order"]:
        rows.extend([copy["source"], copy["private_source_copy"]])
    for row in rows:
        path = (TASK if "task_relative" in row else WORKSPACE) / row.get("task_relative", row.get("root_relative"))
        actual = binding(path)
        assert all(actual[k] == row[k] for k in ("bytes", "sha256"))
    assert (PROJECT / ".lake/packages").resolve() == (WORKSPACE / ".lake/packages").resolve()
    return layout


def prepare_execution() -> None:
    config_receipt = OUT / "execution-config-v1.json"
    if config_receipt.exists():
        for row in load(config_receipt)["configs"]:
            assert binding(TASK / row["task_relative"]) == row
        return
    assert not list((PROJECT / "b/lib/lean").rglob("*.olean")), "Fresh own objects required."
    manifest = load(WORKSPACE / "lake-manifest.json")
    mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
    assert mathlib["rev"] == REV
    (PROJECT / "lake-manifest.json").write_bytes((WORKSPACE / "lake-manifest.json").read_bytes())
    (PROJECT / "lakefile.lean").write_text(f'''import Lake
open Lake DSL
package zeta9ActualUniformAnalyticAuthor where
  buildDir := "b"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "{REV}"
lean_lib ActualUniformAnalytic where
  srcDir := "src"
  roots := #[`AnalyticWeightedBound]
''', encoding="utf-8")
    (PROJECT / "leaf.py").write_text(r'''from pathlib import Path
import json, os, subprocess, sys
PROJECT=Path(__file__).resolve().parent
PACKAGES=Path(r"D:\users\self_projects\prove2me_workspace\.lake\packages").resolve()
env=dict(os.environ)
selected={}
for key in ['LEAN_PATH','LEAN_SRC_PATH']:
    original=[raw for raw in env.get(key,'').split(os.pathsep) if raw]
    allowed=[]
    for raw in original:
        resolved=(PROJECT/Path(raw)).resolve()
        if resolved.is_relative_to(PROJECT.resolve()) or resolved.is_relative_to(PACKAGES):
            allowed.append(str(resolved))
    own=str(PROJECT/'b/lib/lean') if key=='LEAN_PATH' else str(PROJECT/'src')
    if own not in allowed:allowed.insert(0,own)
    env[key]=os.pathsep.join(allowed)
    selected[key]=dict(original=original,filtered=allowed)
selected['actual_environment']={key:env.get(key) for key in ['LEAN_NUM_THREADS','LAKE_JOBS']}
Path(env['ACTUAL_ANALYTIC_PATH_RECEIPT']).write_text(json.dumps(selected,indent=2)+'\n',encoding='utf-8')
sys.exit(subprocess.run(sys.argv[1:],env=env).returncode)
''', encoding="utf-8")
    junction = PROJECT / ".lake/packages"
    junction.parent.mkdir(exist_ok=True)
    assert junction.resolve().is_relative_to(PROJECT.resolve())
    command = ["powershell", "-NoProfile", "-Command",
               "New-Item -ItemType Junction -Path '" + str(junction) +
               "' -Target '" + str(WORKSPACE / ".lake/packages") + "' | Out-Null"]
    result = subprocess.run(command, capture_output=True)
    (OUT / "execution-junction-stdout.log").write_bytes(result.stdout)
    (OUT / "execution-junction-stderr.log").write_bytes(result.stderr)
    assert result.returncode == 0, result.stderr.decode(errors="replace")
    assert junction.is_junction() and junction.resolve() == (WORKSPACE / ".lake/packages").resolve()
    dump(config_receipt, {"status": "execution_config_only_no_Lean_yet", "root_grant": binding(OUT / "Root-author-lane1-grant.json"),
                         "configs": [binding(PROJECT / n) for n in ("lakefile.lean", "lake-manifest.json", "lean-toolchain", "leaf.py")],
                         "junction": {"task_relative": junction.relative_to(TASK).as_posix(),
                                      "actual_resolved_root_relative": junction.resolve().relative_to(WORKSPACE).as_posix()},
                         "actual_lean_calls": 0, "foreign_proof_objects_copied": 0})


def run(label: str, module: str | None, source_root: Path | None = None) -> int:
    layout = gate()
    source_root = source_root or PROJECT / "src"
    assert source_root.resolve().is_relative_to(PROJECT.resolve())
    receipt_path = OUT / "author-compile-receipt.json"
    receipt = load(receipt_path) if receipt_path.exists() else {
        "role": "Actual 70-endpoint uniform analytic AUTHOR", "lane": 1, "project": PROJECT.relative_to(TASK).as_posix(),
        "foreign_math_proof_objects_borrowed": False, "Root_proof_fallback": False, "rows": []}
    index = len(receipt["rows"]) + 1
    folder = OUT / "actual-author-runs" / (str(index).zfill(3) + "-" + label)
    folder.mkdir(parents=True, exist_ok=False)
    inputs = [binding(TASK / row["task_relative"]) for row in load(OUT / "execution-config-v1.json")["configs"]]
    inputs.extend([binding(Path(__file__)), binding(OUT / "Root-author-lane1-grant.json"),
                   binding(OUT / "native-inputs-layout-v2-audit.json")])
    arguments = ["--version"]
    output = None
    if module:
        source = source_root / (module.replace(".", "/") + ".lean")
        assert source.is_file()
        inputs.append(binding(source))
        inputs.extend(binding(p) for p in sorted((PROJECT / "b/lib/lean").rglob("*.olean")))
        output = PROJECT / "b/lib/lean" / (module.replace(".", "/") + ".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        arguments = ["-o", str(output), str(source)]
    retained_inputs = []
    for i, row in enumerate(inputs):
        original = (TASK if "task_relative" in row else WORKSPACE) / row.get("task_relative", row.get("root_relative"))
        snapshot = folder / "inputs" / (str(i).zfill(3) + ".bin")
        snapshot.parent.mkdir(exist_ok=True)
        snapshot.write_bytes(original.read_bytes())
        retained_inputs.append({"original_binding": row, "snapshot_binding": binding(snapshot)})
    env = dict(os.environ)
    env.pop("LEAN_PATH", None)
    env.pop("LEAN_SRC_PATH", None)
    env["LEAN_NUM_THREADS"] = "1"
    env["LAKE_JOBS"] = "1"
    env["ACTUAL_ANALYTIC_PATH_RECEIPT"] = str(folder / "selected-paths.json")
    command = ["lake", "env", PYTHON, str(PROJECT / "leaf.py"), "lean", "-j1", "--root=" + str(source_root)] + arguments
    print(label + ": starting actual serial compiler", flush=True)
    start = time.monotonic()
    result = subprocess.run(command, cwd=PROJECT, env=env, capture_output=True)
    for name, data in (("stdout.log", result.stdout), ("stderr.log", result.stderr),
                       ("combined.log", result.stdout + result.stderr), ("exit.txt", (str(result.returncode) + "\n").encode())):
        (folder / name).write_bytes(data)
    output_bindings = []
    retained_outputs = []
    if output and output.exists():
        for i, path in enumerate(sorted(output.parent.glob(output.name + "*"))):
            snapshot = folder / "outputs" / (str(i).zfill(3) + ".bin")
            snapshot.parent.mkdir(exist_ok=True)
            snapshot.write_bytes(path.read_bytes())
            output_bindings.append(binding(path))
            retained_outputs.append({"original_binding": binding(path), "snapshot_binding": binding(snapshot)})
    paths_path = folder / "selected-paths.json"
    row = {"index": index, "label": label, "module": module, "command": command, "cwd": str(PROJECT),
           "elapsed_seconds": round(time.monotonic() - start, 3), "exit_code": result.returncode,
           "actual_environment": {k: env[k] for k in ("LEAN_NUM_THREADS", "LAKE_JOBS")},
           "input_bindings": inputs, "retained_inputs": retained_inputs,
           "output_bindings": output_bindings, "retained_outputs": retained_outputs,
           "stdout": binding(folder / "stdout.log"), "stderr": binding(folder / "stderr.log"),
           "log": binding(folder / "combined.log"), "exit_file": binding(folder / "exit.txt"),
           "selected_paths": binding(paths_path) if paths_path.exists() else None,
           "failed_attempt_retained": result.returncode != 0}
    receipt["rows"].append(row)
    dump(receipt_path, receipt)
    print(label + ": actual exit " + str(result.returncode), flush=True)
    if result.returncode:
        print((result.stdout + result.stderr).decode("utf-8", errors="replace"), flush=True)
    if paths_path.exists():
        actual = load(paths_path)
        for key in ("LEAN_PATH", "LEAN_SRC_PATH"):
            assert all(Path(raw).resolve().is_relative_to(PROJECT.resolve()) or
                       Path(raw).resolve().is_relative_to((WORKSPACE / ".lake/packages").resolve())
                       for raw in actual[key]["filtered"])
    gate()
    return result.returncode


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    q = argparse.ArgumentParser()
    q.add_argument("--lane-granted", action="store_true", required=True)
    q.add_argument("--phase", choices=("sources", "one"), default="sources")
    q.add_argument("--module")
    q.add_argument("--source-root")
    args = q.parse_args()
    prepare_execution()
    layout = gate()
    if args.phase == "one":
        assert args.module
        sys.exit(run("native-" + args.module.replace(".", "-") + "-repair", args.module,
                     Path(args.source_root) if args.source_root else None))
    if run("runtime-version", None):
        sys.exit(1)
    for row in layout["actual_source_copy_order"]:
        if run("native-" + row["module_name"].replace(".", "-"), row["module_name"]):
            sys.exit(1)
    print("All SOURCE calls succeeded; full type/kernel/definition/axiom/resolver audits remain.", flush=True)


if __name__ == "__main__":
    main()
