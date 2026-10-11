"""Serial actual SOURCE compiler with complete per-call retained evidence."""
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import subprocess
import sys
import time

import initialize_author as p

PY = "C:/Users/anche/AppData/Local/Programs/Python/Python312/python.exe"


def gate():
    grant = p.load(p.OUT / "Root-platform-author-lane2-grant.json")
    assert grant["Root_explicit_grant"] is True and grant["lane"] == 2 and grant["serial_lean_j1_only"] is True
    assert p.sha(p.OUT / "pure-source-handoff.json") == grant["frozen_SOURCE_handoff_sha256"]
    return p.load(p.OUT / "author-context-preparation.json")


def configure(ctx):
    link = ctx / ".lake/packages"
    expected = p.ROOT / ".lake/packages"
    if not link.exists():
        link.parent.mkdir(parents=True, exist_ok=True)
        result = subprocess.run(["pwsh", "-NoProfile", "-Command", 'New-Item -ItemType Junction -Path "' + str(link) + '" -Target "' + str(expected) + '" | Out-Null'], capture_output=True)
        path = p.OUT / ("junction-" + ctx.name + ".log")
        assert not path.exists()
        path.write_bytes(result.stdout + result.stderr)
        assert result.returncode == 0
    assert link.is_junction() and link.resolve() == expected.resolve()


def replace_json(path, value):
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    temporary.replace(path)


def run(tag, label, module=None, source=None):
    gate()
    ctx = p.PROJECT / tag
    configure(ctx)
    receipt_path = p.OUT / "author-execution-receipt.json"
    receipt = p.load(receipt_path) if receipt_path.exists() else {"role": "Outputs platform AUTHOR", "rows": []}
    inputs = [p.bind(ctx / name) for name in ["lakefile.toml", "lean-toolchain", "lake-manifest.json", "lean_call.py"]]
    if source:
        inputs.append(p.bind(ctx / source))
    prior = next((row for row in reversed(receipt["rows"]) if row["tag"] == tag and row["label"] == label and row["exit_code"] == 0 and row["input_bindings"] == inputs), None)
    if prior:
        p.check(prior["input_bindings"] + prior["output_bindings"] + prior["evidence_bindings"])
        print(tag + "/" + label + ": own exact actual0 retained", flush=True)
        return
    run_root = p.OUT / "author-actual-runs"
    occupied = [int(path.name[1:5]) for path in run_root.glob("c[0-9][0-9][0-9][0-9]-*")] if run_root.exists() else []
    number = max([len(receipt["rows"])] + occupied) + 1
    folder = run_root / ("c" + str(number).zfill(4) + "-" + tag + "-" + label)
    folder.mkdir(parents=True, exist_ok=False)
    retained = []
    for i, binding in enumerate(inputs):
        target = folder / ("i" + str(i).zfill(2))
        target.write_bytes(p.resolve(binding).read_bytes())
        retained.append({"original": binding, "retained": p.bind(target)})
    obj = ctx / "b/lib/lean" / (module.replace(".", "/") + ".olean") if module else None
    if obj:
        obj.parent.mkdir(parents=True, exist_ok=True)
    args = ["lean", "-j1"] + (["-o", str(obj.relative_to(ctx)), source] if module else ["--version"])
    command = ["lake", "env", PY, "lean_call.py"] + args
    env = dict(os.environ)
    env.pop("LEAN_PATH", None)
    env.pop("LEAN_SRC_PATH", None)
    env["LEAN_NUM_THREADS"] = "1"
    env["LAKE_JOBS"] = "1"
    env["OUTPUTS_PLATFORM_PATH_RECEIPT"] = str(folder / "selected-paths.json")
    pending = {"tag": tag, "label": label, "module": module, "source": source, "command": command,
               "execution_CWD": str(ctx), "input_bindings": inputs, "retained_initial_inputs": retained,
               "actual_execution_started_at": datetime.now(timezone.utc).isoformat(), "folder_task_relative": folder.relative_to(p.TASK).as_posix(),
               "LEAN_NUM_THREADS": 1, "LAKE_JOBS": 1, "state": "ABOUT_TO_EXECUTE_ACTUAL_SOURCE"}
    p.dump(folder / "intent.json", pending)
    started = time.monotonic()
    with (folder / "stdout.log").open("wb") as stdout, (folder / "stderr.log").open("wb") as stderr:
        process = subprocess.Popen(command, cwd=ctx, env=env, stdout=stdout, stderr=stderr)
        replace_json(folder / "live-handle.json", {"pid": process.pid, "state": "ACTUAL_RUNNING", "tag": tag, "label": label})
        exit_code = process.wait()
    replace_json(folder / "live-handle.json", {"pid": process.pid, "state": "ACTUAL_TERMINAL", "exit_code": exit_code, "tag": tag, "label": label})
    with (folder / "combined.log").open("wb") as combined:
        for name in ["stdout.log", "stderr.log"]:
            with (folder / name).open("rb") as handle:
                while block := handle.read(1024 * 1024):
                    combined.write(block)
    (folder / "exit.txt").write_text(str(exit_code) + "\n", encoding="ascii")
    outputs = []
    if obj and obj.exists():
        for actual in sorted(obj.parent.glob(obj.name + "*")):
            binding = p.bind(actual)
            outputs.append(binding)
            target = folder / ("o" + str(len(outputs)).zfill(2))
            target.write_bytes(actual.read_bytes())
            retained.append({"original": binding, "retained": p.bind(target)})
    evidence = [p.bind(folder / name) for name in ["stdout.log", "stderr.log", "combined.log", "exit.txt", "selected-paths.json", "intent.json", "live-handle.json"] if (folder / name).exists()]
    row = {**pending, "state": "ACTUAL_TERMINAL", "exit_code": exit_code, "elapsed_seconds": round(time.monotonic() - started, 3),
           "output_bindings": outputs, "evidence_bindings": evidence, "immutable_snapshots": retained,
           "whole_failed_run_excluded": exit_code != 0, "all_actual_handles_terminal": True}
    receipt["rows"].append(row)
    replace_json(receipt_path, receipt)
    print(tag + "/" + label + ": actual " + str(exit_code) + " (" + str(row["elapsed_seconds"]) + "s)", flush=True)
    if exit_code:
        with (folder / "combined.log").open("rb") as handle:
            handle.seek(max(0, handle.seek(0, 2) - 9000))
            print(handle.read().decode("utf-8", errors="replace"), flush=True)
        raise RuntimeError("Failed actual call retained; repair append private versions only")


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    prepared = gate()
    selected = sys.argv[1:] or ["n", "d", "r", "c", "f", "m"]
    for tag in selected:
        context = next(row for row in prepared["contexts"] if row["tag"] == tag)
        run(tag, "runtime")
        for i, row in enumerate(context["math_sources"]):
            p.check([row["binding"]])
            run(tag, "s" + str(i).zfill(2), row["module"], row["path"])


if __name__ == "__main__":
    main()
