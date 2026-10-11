"""Append audit IO type annotation after actual call25; no math or DAG-body edits."""
import hashlib
import json
from pathlib import Path

TASK = Path(__file__).resolve().parents[1]
OUT = TASK / "verification/formalization-analytic-factorial-preparation-2026-10-07"
PROJECT = OUT / ".rt/afb1"


def binding(p):
    data = p.read_bytes()
    return {"task_relative": p.relative_to(TASK).as_posix(), "bytes": len(data),
            "sha256": hashlib.sha256(data).hexdigest()}


def main():
    old = '''  liftM <| do
    let stdout ← IO.getStdout
    stdout.putStrLn ("AF_RECORD|" ++ j.compress)
    stdout.flush'''
    new = '''  let action : IO Unit := do
    let stdout ← IO.getStdout
    stdout.putStrLn ("AF_RECORD|" ++ j.compress)
    stdout.flush
  liftM action'''
    rows = []
    for module in ("AFTypes", "AFKernel", "AFBoundary", "AFResolver"):
        source = PROJECT / "private-controls/v3/src" / (module + ".lean")
        text = source.read_text(encoding="utf-8")
        if module != "AFResolver":
            assert text.count(old) == 1, module
            text = text.replace(old, new)
        target = PROJECT / "private-controls/v4/src" / (module + ".lean")
        assert not target.exists()
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text, encoding="utf-8")
        rows.append({"module": module, "previous_v3": binding(source), "appended_v4": binding(target)})
    report = {"status": "PURE_SOURCE_IO_ANNOTATION_ONLY", "actual_failure_call": 25,
              "reason": "Lean inferred BaseIO at IO.getStdout; explicit IO Unit action matches IO putStrLn/flush",
              "all_DAG_complete_types_values_inferType_Std3_and_controls_unchanged": True,
              "actual_lean_calls": 0, "controls": rows}
    path = OUT / "private-controls-io-v4-preparation.json"
    assert not path.exists()
    path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"report": binding(path), "status": report["status"]}))


if __name__ == "__main__":
    main()
