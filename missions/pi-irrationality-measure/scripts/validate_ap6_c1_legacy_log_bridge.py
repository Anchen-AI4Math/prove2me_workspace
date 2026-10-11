"""Read-only legacy parent-log bridge for the compiled ap6/c1 uniform child.

Only the certified WeightErrorMargin SnapshotOriginal and Sol logs may cross
from historical workspace-relative spelling to current task-relative spelling.
All other lookups use the frozen consumer's original file resolver unchanged.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import shutil

import stage_ap6_proved_children as stage
import validate_ap6_proved_children as consumer

TASK, V = stage.TASK, stage.V
SELF = Path(__file__).resolve()
PREFIX = "missions/pi-irrationality-measure/"
C = stage.configure("c1")
PARENT_VALIDATION = C["parent_validation"]
BASE = V / "ap6/c1/actual-child-validation.base.json"
FINAL = V / "ap6/c1/actual-child-validation.json"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def build_bridge():
    parent = stage.read(PARENT_VALIDATION)
    keys = ("SnapshotOriginal.lean", "Sol_OAI_PiExponent_exists_uniform_weight_error_margin.lean")
    bridge = {}
    for key in keys:
        row = parent["preflights"][key]
        old = row["log"]
        if not isinstance(old, str) or not old.startswith(PREFIX) or old in bridge:
            raise ValueError("Parent legacy log path is outside the exact two-path allowlist")
        new = old[len(PREFIX):]
        path = (TASK / new).resolve()
        if (not path.is_relative_to(TASK.resolve()) or not path.is_file()
                or sha(path) != row["log_sha256"]):
            raise ValueError("Historical source/Sol log bytes differ from parent certificate")
        bridge[old] = {"old": old, "task_relative": new,
                       "certified_log_sha256": row["log_sha256"],
                       "actual_log_sha256": sha(path), "parent_preflight_key": key}
    if len(bridge) != 2:
        raise ValueError("Uniform bridge must cover exactly two certified parent logs")
    return bridge


def main():
    if BASE.exists() or FINAL.exists():
        raise ValueError("Refusing to overwrite existing ap6/c1 consumer evidence")
    bridge = build_bridge()
    original_file = consumer.context.file
    used = []

    def certified_file(value):
        raw = str(value).replace("\\", "/")
        if raw in bridge:
            entry = bridge[raw]
            path = original_file(entry["task_relative"])
            if sha(path) != entry["certified_log_sha256"]:
                raise ValueError("Certified uniform parent log changed during replay")
            used.append(raw)
            return path
        return original_file(value)

    consumer.context.file = certified_file
    try:
        consumer.validate("c1")
    finally:
        consumer.context.file = original_file
    if not FINAL.is_file():
        raise ValueError("Frozen ap6/c1 consumer did not emit its base report")
    shutil.copyfile(FINAL, BASE)
    if set(used) != set(bridge) or len(used) != 2:
        raise ValueError("Consumer did not use exactly the two SHA-pinned legacy logs")
    base = stage.read(BASE)
    if (base.get("validated") is not True or base.get("module") != C["module"]
            or base.get("provided_names") != list(stage.HELPERS["c1"])
            or len(base.get("helper_certificates", [])) != 2):
        raise ValueError("Frozen base consumer did not validate the genuine two-helper child")
    final = dict(base)
    final["legacy_log_bridge"] = {
        "schema_version": 1, "adapter": stage.producer.task_rel(SELF),
        "adapter_sha256": sha(SELF), "base_report": stage.producer.task_rel(BASE),
        "base_report_sha256": sha(BASE),
        "parent_validation": stage.producer.task_rel(PARENT_VALIDATION),
        "parent_validation_sha256": sha(PARENT_VALIDATION),
        "path_bridge": [bridge[x] for x in sorted(bridge)],
        "exact_two_parent_logs_replayed": True,
        "all_other_file_lookups_delegated_unchanged": True,
        "Lean_started": False, "API_used": False}
    stage.producer.dump(FINAL, final)
    print(json.dumps({"validated": True, "certificate": stage.producer.task_rel(FINAL),
        "certificate_sha256": sha(FINAL), "base_report": stage.producer.task_rel(BASE),
        "base_report_sha256": sha(BASE), "adapter_sha256": sha(SELF),
        "module": C["module"], "helper_count": 2, "legacy_log_paths": sorted(bridge),
        "max_file_seconds": final["max_file_seconds"], "Lean_started": False,
        "API_used": False}, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
