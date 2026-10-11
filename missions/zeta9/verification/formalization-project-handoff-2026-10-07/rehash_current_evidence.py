"""Root streaming rehash of the exact frozen current-task evidence reports."""
from pathlib import Path, PurePosixPath
from datetime import datetime, timezone
from concurrent.futures import ThreadPoolExecutor
import argparse
import hashlib
import json
import time

TASK = Path(__file__).resolve().parents[2]
ROOT = TASK.parents[1]
TOOLCHAIN = Path(r"C:\Users\anche\.elan\toolchains\leanprover--lean4---v4.33.1")
HANDOFF = Path(__file__).resolve().parent


def digest(path):
    h = hashlib.sha256()
    with path.open("rb") as f:
        for b in iter(lambda: f.read(1048576), b""):
            h.update(b)
    return h.hexdigest()


def verify(row):
    if row.get("task_relative") or row.get("root_relative"):
        key = "task_relative" if row.get("task_relative") else "root_relative"
        q = PurePosixPath(row[key])
        assert not q.is_absolute() and ".." not in q.parts
        p = (TASK if key == "task_relative" else ROOT).joinpath(*q.parts)
    else:
        p = Path(row["absolute_path"])
        assert p.is_absolute() and p.resolve().is_relative_to(TOOLCHAIN.resolve())
    assert p.name.lower() not in {"credentials.json", ".env"}
    if row.get("absolute_path"):
        assert Path(row["absolute_path"]).resolve() == p.resolve()
    size, actual = p.stat().st_size, digest(p)
    assert size == row["bytes"] and actual == row["sha256"], str(p)
    return {"path": str(p), "bytes": size, "sha256": actual, "pass": True}


def report(relative, expected, key, count):
    p = TASK / relative
    assert digest(p) == expected
    v = json.loads(p.read_text(encoding="utf-8"))
    assert len(v[key]) == count
    start = time.monotonic()
    with ThreadPoolExecutor(max_workers=2) as pool:
        rows = list(pool.map(verify, v[key]))
    return {"task_relative": relative, "report_sha256": expected,
            "bindings_rehashed": len(rows), "mismatches": 0,
            "total_bound_bytes": sum(r["bytes"] for r in rows),
            "elapsed_seconds": round(time.monotonic() - start, 3), "rows": rows}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=["pf-platform", "phase-author"])
    mode = parser.parse_args().mode
    if mode == "pf-platform":
        inputs = [
            ("formalization/platform/coefficient-map-numerator-pf/author-audit.json", "5a9491c73cbbb980b411a3389a4c5acd6f0e5ceb71149c8a508f9553660f0ebf", "stable_files", 1441),
            ("verification/formalization-coefficient-map-numerator-pf-platform-independent-2026-10-07/independent-review.json", "872b3d6527b6695ec4e3063a60516ad2d25144ef65c8aca13db54e59abd9b871", "stable_files", 2417),
            ("formalization/platform/coefficient-map-numerator-pf/publication-preparation-2026-10-07/final-v4-freeze.json", "0f9c5c788f1bb8880583d99f031a7fcd498719bf1cb400d3f8b40aeb5ff46346", "stable_files", 78),
        ]
    else:
        inputs = [("verification/formalization-analytic-phase-upper-bound-2026-10-07/author-audit.json", "a8f8cf52008b69f7b8e7e868a3c754ebc72c89f4f6f1aa89f9ca2bfdf1ff2647", "stable_bindings", 25818)]
    results = []
    for args in inputs:
        item = report(*args)
        results.append(item)
        print(json.dumps({k: v for k, v in item.items() if k != "rows"}), flush=True)
    value = {"checked_at": datetime.now(timezone.utc).isoformat(), "role": "Root full binding rehash; no additional Lean invocation",
             "mode": mode, "results": results, "API_calls": 0, "Lean_calls": 0}
    path = HANDOFF / ("root-" + mode + "-complete-binding-rehash.json")
    temporary = path.with_suffix(".tmp")
    temporary.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    temporary.replace(path)
    print("Root complete rehash report", digest(path), flush=True)


if __name__ == "__main__":
    main()
