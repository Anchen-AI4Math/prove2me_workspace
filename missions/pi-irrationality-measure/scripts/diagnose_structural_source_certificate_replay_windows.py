#!/usr/bin/env python3
"""Read-only recursive diff for elevated structural source-cert replay."""

from __future__ import annotations

import json
import os
from pathlib import Path
from typing import Any

import certify_structural_kernel_source_snapshot as certifier
import diagnose_structural_source_catalog_replay as catalog_diag
import generate_shared_source_snapshot as base
import generate_structural_kernel_source_snapshot as source_gen
import structural_provider_certificate_evidence_windows as windows


TASK = Path(__file__).resolve().parents[1]
CERTIFICATE = (
    TASK / "verification" / "shared-source-snapshot" / "structural-kernel-74" /
    "StructuralKernelSource74.validation.json"
)


def path_diagnostic(field: str, recorded: Any, replayed: Any) -> dict[str, Any] | None:
    if not isinstance(recorded, str) or not isinstance(replayed, str):
        return None
    if not windows._drive_case_pair(recorded, replayed):
        return None
    old, new = Path(recorded), Path(replayed)
    row: dict[str, Any] = {
        "field": field,
        "recorded": recorded,
        "replayed": replayed,
        "suffix_exact_after_drive": recorded[1:] == replayed[1:],
        "drive_letters_equal_case_insensitive": recorded[0].lower() == replayed[0].lower(),
        "recorded_exists": old.exists(),
        "replayed_exists": new.exists(),
    }
    if old.exists() and new.exists():
        row["samefile"] = os.path.samefile(old, new)
        row["path_kind"] = "file" if old.is_file() and new.is_file() else "directory"
        if old.is_file() and new.is_file():
            row["recorded_sha256"] = base.sha_file(old)
            row["replayed_sha256"] = base.sha_file(new)
        else:
            row["sha256_not_applicable"] = "resolved search roots are directories"
    return row


def main() -> int:
    stored = json.loads(CERTIFICATE.read_text(encoding="utf-8"))
    original = source_gen.build_basis
    normalization: dict[str, Any] = {}

    def wrapped_build_basis() -> dict[str, Any]:
        return windows._reconciled_basis(original, normalization)

    source_gen.build_basis = wrapped_build_basis
    try:
        fresh, _ = certifier.validate()
    finally:
        source_gen.build_basis = original
    diff = catalog_diag.differences(stored, fresh)
    path_rows = []
    for row in diff:
        diagnostic = path_diagnostic(row["field"], row.get("recorded"), row.get("replayed"))
        if diagnostic is not None:
            path_rows.append(diagnostic)
    report = {
        "schema_version": 1,
        "artifact_kind": "structural-source-certificate-replay-diagnostic",
        "read_only": True,
        "catalog_path_reconciliation": normalization,
        "difference_count": len(diff),
        "differences": diff,
        "drive_case_path_diagnostics": path_rows,
        "all_differences_are_verified_drive_case_paths": len(diff) == len(path_rows),
        "stored_certificate": base.task_relative(CERTIFICATE),
        "stored_certificate_sha256": base.sha_file(CERTIFICATE),
    }
    print(json.dumps(report, ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
