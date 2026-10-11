"""Serially build the seven new Phase modules, then run the official task build.

Lake has no LAKE_JOBS setting in the installed toolchain. New modules are
therefore built in dependency order before the aggregate scoped invocation.
The workspace launcher, source files, and frozen installation receipt stay
unchanged. No API calls or credentials are used.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import os
import subprocess
import sys

TASK = Path(__file__).resolve().parents[2]
WORKSPACE = TASK.parents[1]
OUT = TASK / "formalization/platform/analytic-phase/publications-for-new-mission-2026-10-07/root-scoped-build"
PY312 = Path(r"C:\Users\anche\AppData\Local\Programs\Python\Python312\python.exe")
LAKE = Path(r"C:\Users\anche\.elan\toolchains\leanprover--lean4---v4.33.1\bin\lake.exe")


def binding(p):
    b = p.read_bytes()
    return {"path": str(p), "bytes": len(b), "sha256": hashlib.sha256(b).hexdigest()}


def save(name, value):
    (OUT / name).write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def main():
    assert Path(sys.executable).resolve() == PY312.resolve()
    assert not OUT.exists(), "Preserve the original attempt and use a new output directory for a retry"
    OUT.mkdir()
    receipt_path = OUT.parent / "root-install-receipt.json"
    installed = json.loads(receipt_path.read_text(encoding="utf-8"))
    assert len(installed["files"]) == 7
    sources = []
    for row in installed["files"]:
        p = (WORKSPACE / row["root_relative"]).resolve()
        assert p.is_relative_to(WORKSPACE.resolve())
        actual = binding(p)
        assert (actual["bytes"], actual["sha256"]) == (row["bytes"], row["sha256"])
        sources.append(actual)
    scope = TASK / "scope.json"
    assert binding(scope)["sha256"] == installed["scope_after_sha256"]
    env = os.environ.copy()
    env.update(LEAN_NUM_THREADS="1", LAKE_JOBS="1", PYTHONIOENCODING="utf-8", PYTHONUNBUFFERED="1")
    rows = []
    save("input-gate.json", {"checked_at": datetime.now(timezone.utc).isoformat(),
         "installed_receipt": binding(receipt_path), "sources": sources,
         "scope": binding(scope), "executor": binding(Path(__file__)),
         "official_workspace_launcher": binding(WORKSPACE / "scripts/workspace.py"),
         "serial_new_module_prebuilds": True, "Lean_threads": 1,
         "LAKE_JOBS_is_not_an_installed_Lake_concurrency_control": True,
         "local_integration_only": True,
         "PNT_statement_mirror_limitation_retained": True,
         "independent_complete_source_and_platform_ACCEPTED_evidence_separate": True,
         "API_calls": 0})

    def run(label, command):
        row = {"label": label, "command": command, "cwd": str(WORKSPACE),
               "started_at": datetime.now(timezone.utc).isoformat()}
        log = OUT / (label + ".log")
        with log.open("wb") as out:
            result = subprocess.run(command, cwd=WORKSPACE, env=env, stdout=out, stderr=subprocess.STDOUT)
        row.update(exit_code=result.returncode, ended_at=datetime.now(timezone.utc).isoformat(), log=binding(log))
        rows.append(row)
        save("actual-build-receipt.json", {"rows": rows, "all_finished_calls_successful": all(r["exit_code"] == 0 for r in rows), "official_task_build_complete": label == "official-zeta9-task" and result.returncode == 0})
        print(json.dumps({"label": label, "exit_code": result.returncode}), flush=True)
        if result.returncode:
            raise SystemExit(result.returncode)

    for i, row in enumerate(installed["files"], 1):
        run(f"serial-new-phase-module-{i}", [str(LAKE), "build", row["root_relative"]])
    run("official-zeta9-task", [str(PY312), "scripts/workspace.py", "build", "zeta9"])
    assert all(binding(WORKSPACE / row["root_relative"])["sha256"] == row["sha256"] for row in installed["files"])
    save("final-input-readback.json", {"source_changes": 0, "scope_changes": 0, "scope": binding(scope), "formal_task_build_exit_code": 0, "new_Phase_platform_candidate_proof_count": 3, "all_goal_work_complete": False})


if __name__ == "__main__":
    main()
