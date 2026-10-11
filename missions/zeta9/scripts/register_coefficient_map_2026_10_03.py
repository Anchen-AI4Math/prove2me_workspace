"""Record the scoped task check/build for the genuine finite Z9.F entry."""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import shutil

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
OUT = TASK / "verification/formalization-coefficient-map-2026-10-03"
SOURCE = TASK / "formalization/CoefficientMap.lean"
EXPECTED = "e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03"


def main():
    assert hashlib.sha256(SOURCE.read_bytes()).hexdigest() == EXPECTED
    scope_path = TASK / "scope.json"
    scope = json.loads(scope_path.read_text(encoding="utf-8"))
    target = "missions/zeta9/formalization/CoefficientMap.lean"
    # The root lakefile registers only shared platform libraries. Native
    # mission sources are checked separately with Lean, never as lake targets.
    assert target not in scope["build"]
    previous_log = OUT / "task-build.log"
    if previous_log.exists() and "unknown module source path" in previous_log.read_text(encoding="utf-8"):
        preserved = OUT / "unsupported-direct-entry-build.log"
        if not preserved.exists():
            shutil.copyfile(previous_log, preserved)
            shutil.copyfile(OUT / "task-build-exit.txt", OUT / "unsupported-direct-entry-build-exit.txt")
    script_path = Path(__file__).resolve().relative_to(ROOT).as_posix()
    if script_path not in scope["sources"]:
        scope["sources"].append(script_path)
        scope_path.write_text(json.dumps(scope, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    results = {}
    for mode in ("check", "build"):
        command = [sys.executable, str(ROOT / "scripts/workspace.py"), mode]
        if mode == "build":
            command.append("zeta9")
        with (OUT / ("task-" + mode + ".log")).open("w", encoding="utf-8") as log:
            result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, check=False)
        (OUT / ("task-" + mode + "-exit.txt")).write_text(str(result.returncode) + "\n", encoding="utf-8")
        results[mode] = {"command": command, "exit": result.returncode,
            "log": str((OUT / ("task-" + mode + ".log")).relative_to(TASK))}
        print(f"Scoped task {mode}: exit {result.returncode}", flush=True)
    receipt = {"source_sha256": EXPECTED, "native_source": target, "results": results,
        "finite_highest_pole_entry_only": True, "full_F_closed": False,
        "native_entry_in_lake_targets": False, "platform_F_solutions_not_yet_installed": True,
        "native_proof_evidence": "compile-receipt.json",
        "root_PNT_statement_mirror_is_type_integration_only": True}
    (OUT / "task-registration-receipt.json").write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    if results["build"]["exit"]:
        raise SystemExit(results["build"]["exit"])


if __name__ == "__main__":
    main()
