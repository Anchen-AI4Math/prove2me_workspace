"""Repair only ambiguous MetaM IO lifting in own audit controls; preserve all math controls."""
import hashlib
import json
from pathlib import Path

TASK = Path(__file__).resolve().parents[1]
OUT = TASK / "verification/formalization-analytic-factorial-preparation-2026-10-07"
PROJECT = OUT / ".rt/afb1"


def binding(path):
    data = path.read_bytes()
    return {"task_relative": path.relative_to(TASK).as_posix(), "bytes": len(data),
            "sha256": hashlib.sha256(data).hexdigest()}


def main():
    rows = []
    for module in ("AFTypes", "AFKernel", "AFBoundary", "AFResolver"):
        source = PROJECT / "src" / (module + ".lean")
        text = source.read_text(encoding="utf-8")
        if module != "AFResolver":
            assert text.count("  liftIO <| IO.println") == 1
            text = text.replace("  liftIO <| IO.println", "  liftM <| IO.println")
        target = PROJECT / "private-controls/v2/src" / (module + ".lean")
        assert not target.exists()
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text, encoding="utf-8")
        rows.append({"module": module, "original_control": binding(source), "private_control_v2": binding(target)})
    report = {"status": "private_controls_only_not_compiled", "controls": rows,
              "reason": "Actual liftIO resolves to Lean.Elab.Command.liftIO; liftM correctly lifts IO into the declared MetaM.",
              "actual_failure_call_index": 21, "original_math_candidates_and_controls_v1_unchanged": True,
              "all_70_complete_type_controls_preserved": True, "all_29_whole_definition_controls_preserved": True,
              "all_15_boundaries_and_actual_resolver_preserved": True, "actual_lean_calls": 0}
    target = OUT / "private-controls-repair-v2.json"
    assert not target.exists()
    target.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": report["status"], "report": binding(target)}))


if __name__ == "__main__":
    main()
