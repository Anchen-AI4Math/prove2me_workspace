"""Root read-only verification of every frozen binding in a graph audit."""
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from pathlib import Path
import argparse
import hashlib
import json
import os
import time

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]


def load(path):
    return json.loads(path.read_bytes())


def digest(path):
    with path.open("rb") as stream:
        return path.stat().st_size, hashlib.file_digest(stream, "sha256").hexdigest()


def bindings(value):
    if isinstance(value, dict):
        if {"bytes", "sha256"} <= value.keys() and any(
            key in value for key in ("task_relative", "root_relative", "absolute_path")
        ):
            yield value
        else:
            for child in value.values():
                yield from bindings(child)
    elif isinstance(value, list):
        for child in value:
            yield from bindings(child)


def pathof(binding):
    for key, base in (("task_relative", TASK), ("root_relative", ROOT)):
        if key in binding:
            relative = Path(binding[key])
            assert not relative.is_absolute() and ".." not in relative.parts
            return base / relative
    path = Path(binding["absolute_path"])
    allowed = Path("C:/Users/anche/.elan/toolchains/leanprover--lean4---v4.33.1/lib/lean")
    assert path.is_absolute() and path.is_relative_to(allowed), str(path)
    return path


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("report")
    parser.add_argument("output")
    args = parser.parse_args()
    started = time.monotonic()
    report_path, output = TASK / args.report, TASK / args.output
    assert not output.exists(), "Preserve previous verification records"
    report = load(report_path)
    rows = list(bindings(report))
    assert rows and ("stable_files" in report or "stable_bindings" in report), "Complete frozen manifest required"
    unique = {}
    for row in rows:
        identity = os.path.normcase(str(pathof(row)))
        if identity in unique:
            assert (unique[identity]["bytes"], unique[identity]["sha256"]) == (row["bytes"], row["sha256"])
        else:
            unique[identity] = row

    def verify(row):
        path = pathof(row)
        assert digest(path) == (row["bytes"], row["sha256"]), str(path)

    with ThreadPoolExecutor(max_workers=2) as pool:
        list(pool.map(verify, unique.values()))
    size, sha = digest(report_path)
    result = {
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "report": {"task_relative": report_path.relative_to(TASK).as_posix(), "bytes": size, "sha256": sha},
        "Root_personally_stream_rehashed_all_frozen_report_bindings": True,
        "recorded_binding_occurrences": len(rows),
        "unique_bindings": len(unique),
        "stable_bytes": sum(row["bytes"] for row in unique.values()),
        "mismatches": [],
        "elapsed_seconds": time.monotonic() - started,
        "Lean_calls": 0,
        "API_calls": 0,
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in result.items() if key != "report"}))


if __name__ == "__main__":
    main()
