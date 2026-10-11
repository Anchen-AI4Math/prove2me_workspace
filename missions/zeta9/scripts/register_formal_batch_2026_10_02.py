"""Register and build one reviewed zeta9 batch without changing other missions."""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser()
    parser.add_argument("batch", choices=("coefficient", "pnt"))
    args = parser.parse_args()
    out = TASK / "formalization/platform" / args.batch
    problems = json.loads((out / "problems-request.json").read_text(encoding="utf-8"))["problems"]
    definitions_path = out / "definitions-request.json"
    definitions = json.loads(definitions_path.read_text(encoding="utf-8")) if definitions_path.exists() else []
    scope_path = TASK / "scope.json"
    scope = json.loads(scope_path.read_text(encoding="utf-8"))
    sources = [item[key] for item in problems for key in ("local_solution", "local_reference")]
    sources += [item["local_path"] for item in definitions]
    sources += ["missions/zeta9/scripts/register_formal_batch_2026_10_02.py"]
    publisher = TASK / "scripts" / f"publish_{args.batch}_2026_10_02.py"
    if publisher.exists():
        sources.append(publisher.relative_to(ROOT).as_posix())
    for relative in sources:
        assert (ROOT / relative).is_file(), relative
        if relative not in scope["sources"]:
            scope["sources"].append(relative)
    for item in problems:
        relative = item["local_solution"]
        if relative not in scope["build"]:
            scope["build"].append(relative)
    scope_path.write_text(json.dumps(scope, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    refreshed = subprocess.run([sys.executable, str(TASK / "scripts/refresh_formal_scope_2026_10_02.py")], cwd=ROOT)
    assert refreshed.returncode == 0
    with (out / "scope-check.log").open("wb") as log:
        check = subprocess.run([sys.executable, "scripts/workspace.py", "check"], cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    (out / "scope-check-exit.txt").write_text(str(check.returncode) + "\n", encoding="utf-8")
    print("Scope check exit:", check.returncode, flush=True)
    print((out / "scope-check.log").read_text(encoding="utf-8", errors="replace")[-2000:], flush=True)
    with (out / "task-build.log").open("wb") as log:
        result = subprocess.run([sys.executable, "scripts/workspace.py", "build", "zeta9"], cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    (out / "task-build-exit.txt").write_text(str(result.returncode) + "\n", encoding="utf-8")
    print("Task build exit:", result.returncode, flush=True)
    print((out / "task-build.log").read_text(encoding="utf-8", errors="replace")[-2500:], flush=True)
    raise SystemExit(result.returncode)


if __name__ == "__main__":
    main()
