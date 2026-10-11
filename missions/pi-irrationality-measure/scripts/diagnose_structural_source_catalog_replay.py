#!/usr/bin/env python3
"""Report exact field differences in the structural source catalog replay.

Read-only diagnostic for comparing the frozen catalog with the catalog object
derived from current authenticated inputs.  Path differences are annotated;
no value is normalized and no artifact is written.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
from typing import Any

import generate_shared_source_snapshot as base
import generate_structural_kernel_source_snapshot as gen


def expected_catalog(basis: dict[str, Any]) -> dict[str, Any]:
    return {
        "schema_version": 1,
        "artifact_kind": "structural-kernel-source-catalog",
        "certificate_scope": "partial-source-only-two-atomic-structure-families",
        "source_version": 875,
        "partial": True,
        "platform_ready": False,
        "usable_as_full_source_certificate": False,
        "kernel_metadata_schema": "lean-4.33.1-ConstantInfo-complete-v1",
        "recursor_rule_rhs_required": True,
        "lean_declaration_source": basis["lean_declaration_source"],
        "lean_declaration_source_sha256": basis["lean_declaration_source_sha256"],
        "constant_info_fields": gen.CONSTANT_INFO_FIELDS,
        "full_owner_catalog": base.task_relative(gen.FULL_CATALOG),
        "full_owner_catalog_sha256": basis["full_catalog_sha256"],
        "full_owner_count": 6148,
        "row_count": gen.EXPECTED_ROWS,
        "unit_plan": base.task_relative(gen.UNIT_PLAN),
        "unit_plan_sha256": base.sha_file(gen.UNIT_PLAN),
        "artifact_plan": base.task_relative(gen.ARTIFACT_PLAN),
        "artifact_plan_sha256": base.sha_file(gen.ARTIFACT_PLAN),
        "decl_graph_sha256": basis["graph_sha256"],
        "families": basis["families"],
        "owners": basis["records"],
    }


def differences(left: Any, right: Any, path: str = "$.") -> list[dict[str, Any]]:
    if type(left) is not type(right):
        return [{"field": path, "recorded": left, "replayed": right,
                 "difference": "type"}]
    if isinstance(left, dict):
        rows: list[dict[str, Any]] = []
        for key in sorted(set(left) | set(right)):
            child = f"{path}{key}"
            if key not in left:
                rows.append({"field": child, "recorded": None, "replayed": right[key],
                             "difference": "missing-recorded"})
            elif key not in right:
                rows.append({"field": child, "recorded": left[key], "replayed": None,
                             "difference": "missing-replayed"})
            else:
                rows.extend(differences(left[key], right[key], child + "."))
        return rows
    if isinstance(left, list):
        if len(left) != len(right):
            return [{"field": path, "recorded_length": len(left),
                     "replayed_length": len(right), "difference": "length"}]
        rows = []
        for index, (old, new) in enumerate(zip(left, right, strict=True)):
            rows.extend(differences(old, new, f"{path}[{index}]."))
        return rows
    if left != right:
        return [{"field": path.removesuffix("."), "recorded": left,
                 "replayed": right, "difference": "value"}]
    return []


def path_diagnostic(recorded: str, replayed: str) -> dict[str, Any]:
    old, new = Path(recorded), Path(replayed)
    result: dict[str, Any] = {
        "recorded": recorded,
        "replayed": replayed,
        "os_name": os.name,
        "suffix_exact_after_drive": len(recorded) >= 2 and len(replayed) >= 2
            and recorded[1:] == replayed[1:],
        "drive_letters_equal_case_insensitive": len(recorded) >= 2 and len(replayed) >= 2
            and recorded[0].lower() == replayed[0].lower(),
        "recorded_exists": old.is_file(),
        "replayed_exists": new.is_file(),
    }
    if old.is_file() and new.is_file():
        result["samefile"] = os.path.samefile(old, new)
        result["recorded_sha256"] = base.sha_file(old)
        result["replayed_sha256"] = base.sha_file(new)
    return result


def main() -> int:
    recorded = json.loads(gen.CATALOG.read_text(encoding="utf-8"))
    basis = gen.build_basis()
    expected = expected_catalog(basis)
    diff = differences(recorded, expected)
    path_rows = []
    for row in diff:
        if row["field"] == "$.lean_declaration_source":
            path_rows.append(path_diagnostic(row["recorded"], row["replayed"]))
    report = {
        "schema_version": 1,
        "artifact_kind": "structural-source-catalog-replay-diagnostic",
        "read_only": True,
        "difference_count": len(diff),
        "differences": diff,
        "path_diagnostics": path_rows,
        "recorded_catalog": base.task_relative(gen.CATALOG),
        "recorded_catalog_sha256": base.sha_file(gen.CATALOG),
    }
    print(json.dumps(report, ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
