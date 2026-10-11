"""Actual serial Root-granted platform author calls in fresh aupa1 SOURCE context."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

sys.dont_write_bytecode = True
TASK = Path(__file__).resolve().parents[1]
WORKSPACE = TASK.parents[1]
OUT = TASK / "formalization/platform/analytic-uniform-weighted"
PROJECT = TASK / ".rt/aupa1"
POLICY_SHA = "a8749c3008e5d0b3fa3bb0d4cb1f91c1f304dafe56c1f34767506f3825207081"
PYTHON = "C:/Users/anche/AppData/Local/Programs/Python/Python312/python.exe"


def load(p):
    return json.loads(p.read_text(encoding="utf-8-sig"))


def binding(p):
    data = p.read_bytes()
    base = TASK if p.is_relative_to(TASK) else WORKSPACE
    return {"task_relative" if base == TASK else "root_relative": p.relative_to(base).as_posix(),
            "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}


def path_of(b):
    return (TASK if "task_relative" in b else WORKSPACE) / b.get("task_relative", b.get("root_relative"))


def gate():
    policy_path = OUT / "platform-native-inputs-v1.json"
    assert binding(policy_path)["sha256"] == POLICY_SHA
    policy = load(policy_path)
    for row in policy["sources"]:
        assert binding(path_of(row["candidate"])) == row["candidate"]
        assert binding(path_of(row["private_copy"])) == row["private_copy"]
    for row in policy["configs"]:
        assert binding(path_of(row)) == row
    grant_path = OUT / "Root-platform-author-lane1-grant.json"
    assert binding(grant_path) == policy["Root_grant"]
    grant = load(grant_path)
    assert grant["Root_explicit_grant"] and grant["lane"] == 1
    assert grant["owner"] == "factorial_bound_author_1007"
    assert grant["fresh_private_project"] == PROJECT.relative_to(TASK).as_posix()
    assert (PROJECT / ".lake/packages").is_junction()
    assert (PROJECT / ".lake/packages").resolve() == (WORKSPACE / ".lake/packages").resolve()
    assert binding(path_of(policy["frozen_source_handoff"])) == policy["frozen_source_handoff"]
    return policy


def run(module, source_root=None):
    policy = gate()
    source_root = source_root or PROJECT / "src"
    assert source_root.resolve().is_relative_to(PROJECT.resolve())
    receipt_path = OUT / "platform-author-compile-receipt.json"
    receipt = load(receipt_path) if receipt_path.exists() else {
        "role": "platform actual analytic uniform AUTHOR", "owner": "factorial_bound_author_1007",
        "lane": 1, "project": PROJECT.relative_to(TASK).as_posix(),
        "foreign_math_objects_borrowed": False, "Root_math_object_fallback": False, "rows": []}
    index = len(receipt["rows"]) + 1
    label = module.replace(".", "-") if module else "runtime-version"
    folder = OUT / "actual-platform-author-runs" / (str(index).zfill(3) + "-" + label)
    folder.mkdir(parents=True, exist_ok=False)
    input_bindings = policy["configs"] + [binding(Path(__file__)), binding(OUT / "platform-native-inputs-v1.json"), policy["Root_grant"], policy["frozen_source_handoff"]]
    output = None
    args = ["--version"]
    if module:
        source = source_root / (module.replace(".", "/") + ".lean")
        assert source.exists()
        input_bindings.append(binding(source))
        input_bindings += [binding(p) for p in sorted((PROJECT / "b/lib/lean").rglob("*")) if p.is_file()]
        output = PROJECT / "b/lib/lean" / (module.replace(".", "/") + ".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        args = ["-o", str(output), str(source)]
    retained_inputs = []
    for i, row in enumerate(input_bindings):
        snapshot = folder / "inputs" / (str(i).zfill(3) + ".bin")
        snapshot.parent.mkdir(exist_ok=True)
        snapshot.write_bytes(path_of(row).read_bytes())
        retained_inputs.append({"original_binding": row, "snapshot_binding": binding(snapshot)})
    env = dict(os.environ)
    for key in ("LEAN_PATH", "LEAN_SRC_PATH"):
        env.pop(key, None)
    env.update(LEAN_NUM_THREADS="1", LAKE_JOBS="1", AU_PLATFORM_PATH_RECEIPT=str(folder / "selected-paths.json"))
    command = ["lake", "env", PYTHON, str(PROJECT / "leaf.py"), "lean", "-j1", "--root=" + str(source_root)] + args
    print(str(index) + " " + label + ": starting actual -j1", flush=True)
    start = time.monotonic()
    result = subprocess.run(command, cwd=PROJECT, env=env, capture_output=True)
    for name, data in (("stdout.log", result.stdout), ("stderr.log", result.stderr),
                       ("combined.log", result.stdout + result.stderr), ("exit.txt", (str(result.returncode) + "\n").encode())):
        (folder / name).write_bytes(data)
    outputs, retained_outputs = [], []
    if output and output.exists():
        for i, p in enumerate(sorted(output.parent.glob(output.name + "*"))):
            outputs.append(binding(p))
            snapshot = folder / "outputs" / (str(i).zfill(3) + ".bin")
            snapshot.parent.mkdir(exist_ok=True)
            snapshot.write_bytes(p.read_bytes())
            retained_outputs.append({"original_binding": binding(p), "snapshot_binding": binding(snapshot)})
    row = {"index": index, "module": module, "command": command, "cwd": str(PROJECT),
           "elapsed_seconds": round(time.monotonic() - start, 3), "exit_code": result.returncode,
           "actual_environment": {k: env[k] for k in ("LEAN_NUM_THREADS", "LAKE_JOBS")},
           "input_bindings": input_bindings, "retained_inputs": retained_inputs,
           "output_bindings": outputs, "retained_outputs": retained_outputs,
           "stdout": binding(folder / "stdout.log"), "stderr": binding(folder / "stderr.log"),
           "combined": binding(folder / "combined.log"), "exit_file": binding(folder / "exit.txt"),
           "selected_paths": binding(folder / "selected-paths.json"), "failed_attempt_retained": result.returncode != 0}
    receipt["rows"].append(row)
    receipt_path.write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(str(index) + " " + label + ": actual exit " + str(result.returncode), flush=True)
    if result.returncode:
        print((result.stdout + result.stderr).decode("utf-8", errors="replace"), flush=True)
    selected = load(folder / "selected-paths.json")
    for key in ("LEAN_PATH", "LEAN_SRC_PATH"):
        for raw in selected[key]["filtered"]:
            p = Path(raw).resolve()
            assert p.is_relative_to(PROJECT.resolve()) or p.is_relative_to((WORKSPACE / ".lake/packages").resolve())
    gate()
    return result.returncode


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser()
    parser.add_argument("--lane-granted", action="store_true", required=True)
    parser.add_argument("--module")
    parser.add_argument("--source-root")
    parser.add_argument("--all", action="store_true")
    args = parser.parse_args()
    policy = gate()
    if args.all:
        assert not (OUT / "platform-author-compile-receipt.json").exists(), "Do not restart successful calls."
        if run(None):
            sys.exit(1)
        for module in policy["source_compile_order"]:
            if run(module):
                sys.exit(1)
        print("All initial SOURCE and complete control calls exited zero; final frozen audit remains.", flush=True)
    else:
        assert args.module
        sys.exit(run(args.module, Path(args.source_root) if args.source_root else None))


if __name__ == "__main__":
    main()
