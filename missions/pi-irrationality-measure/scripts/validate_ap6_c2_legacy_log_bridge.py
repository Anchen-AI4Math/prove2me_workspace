"""Read-only legacy log-path bridge for the already compiled ap6/c2 child.

The frozen ap6 validator receives only task-relative log paths.  This adapter
recognizes two exact historical workspace-relative paths in the certified
minimum-weight parent, verifies their original log hashes, and strips the
mission prefix in memory.  Every other file lookup is delegated unchanged.
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
C = stage.configure("c2")
PARENT_VALIDATION = C["parent_validation"]
BASE = V / "ap6/c2/actual-child-validation.base.json"
FINAL = V / "ap6/c2/actual-child-validation.json"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def build_bridge():
    parent = stage.read(PARENT_VALIDATION)
    keys = ("SnapshotOriginal.lean", "Sol_OAI_PiExponent_exists_minimum_weight.lean")
    bridge = {}
    for key in keys:
        row = parent["preflights"][key]
        old = row["log"]
        if not isinstance(old, str) or not old.startswith(PREFIX) or old in bridge:
            raise ValueError("Parent legacy log path is not in the exact allowlist")
        new = old[len(PREFIX):]
        path = (TASK / new).resolve()
        if (not path.is_relative_to(TASK.resolve()) or not path.is_file()
                or sha(path) != row["log_sha256"]):
            raise ValueError("Legacy log bytes differ from parent certificate")
        bridge[old] = {"old": old, "task_relative": new,
                       "certified_log_sha256": row["log_sha256"],
                       "actual_log_sha256": sha(path), "parent_preflight_key": key}
    if len(bridge) != 2:
        raise ValueError("Legacy bridge must cover exactly two parent log paths")
    return bridge


def main():
    if BASE.exists() or FINAL.exists():
        raise ValueError("Refusing to overwrite an existing ap6/c2 consumer report")
    bridge = build_bridge()
    old_file = consumer.context.file
    used = []

    def certified_file(value):
        raw = str(value).replace("\\", "/")
        if raw in bridge:
            entry = bridge[raw]
            path = old_file(entry["task_relative"])
            if sha(path) != entry["certified_log_sha256"]:
                raise ValueError("Legacy parent log changed during replay")
            used.append(raw)
            return path
        return old_file(value)

    consumer.context.file = certified_file
    try:
        result = consumer.validate("c2")
    finally:
        consumer.context.file = old_file
    if not FINAL.is_file():
        raise ValueError("Base ap6/c2 consumer did not emit its report")
    shutil.copyfile(FINAL, BASE)
    if set(used) != set(bridge) or len(used) != 2:
        raise ValueError("Consumer did not replay exactly the two certified legacy logs")
    base = stage.read(BASE)
    if base.get("validated") is not True or base.get("module") != C["module"]:
        raise ValueError("Base ap6/c2 report is not the exact proved-child certificate")
    final = dict(base)
    final["legacy_log_bridge"] = {
        "schema_version": 1, "adapter": stage.producer.task_rel(SELF),
        "adapter_sha256": sha(SELF), "base_report": stage.producer.task_rel(BASE),
        "base_report_sha256": sha(BASE),
        "parent_validation": stage.producer.task_rel(PARENT_VALIDATION),
        "parent_validation_sha256": sha(PARENT_VALIDATION),
        "path_bridge": [bridge[x] for x in sorted(bridge)],
        "exact_two_legacy_logs_replayed": True,
        "all_other_file_lookups_delegated_unchanged": True,
        "Lean_started": False, "API_used": False}
    stage.producer.dump(FINAL, final)
    print(json.dumps({"validated": True, "certificate": stage.producer.task_rel(FINAL),
        "certificate_sha256": sha(FINAL), "base_report": stage.producer.task_rel(BASE),
        "base_report_sha256": sha(BASE), "adapter_sha256": sha(SELF),
        "module": C["module"], "legacy_log_paths": sorted(bridge),
        "max_file_seconds": final["max_file_seconds"], "Lean_started": False,
        "API_used": False}, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
