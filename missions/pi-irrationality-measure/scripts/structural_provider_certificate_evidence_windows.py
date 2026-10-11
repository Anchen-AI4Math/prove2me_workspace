#!/usr/bin/env python3
"""Windows drive-letter adapter for structural provider certificate replay.

The elevated publisher and the sandbox spell the pinned Lean sysroot drive as
``C:`` and ``c:`` respectively.  This adapter changes only the replayed
``lean_declaration_source`` spelling after exact suffix, drive-letter,
``samefile``, and SHA-256 checks.  The frozen catalog, certificates, validators,
snapshot provenance, and import manifests are never changed.  All other
catalog fields remain subject to the original exact comparison.
"""

from __future__ import annotations

import argparse
import copy
import json
import os
from pathlib import Path
from typing import Any

import generate_shared_source_snapshot as base
import generate_structural_kernel_source_snapshot as source_gen
import diagnose_structural_source_catalog_replay as recursive_diff
import structural_provider_certificate_evidence as generic


TASK = Path(__file__).resolve().parents[1]
LEAN_OLEAN_SHA256 = "b6d86d9546713512afdbbaecee5fbc5355e06a30cd70a405f4fa061dce3d56a7"
SOURCE_PATH_FIELD = "$.actual_evidence.olean_resolution.dependency_oleans.[0].path"
SOURCE_ROOT_FIELD = "$.actual_evidence.olean_resolution.dependency_oleans.[0].resolved_search_root"


def _assert(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def _drive_case_pair(recorded: str, replayed: str) -> bool:
    return (
        os.name == "nt"
        and len(recorded) >= 3
        and len(replayed) >= 3
        and recorded[1] == replayed[1] == ":"
        and recorded[0].lower() == replayed[0].lower()
        and recorded[1:] == replayed[1:]
        and recorded != replayed
    )


def _reconciled_basis(original_build_basis, evidence: dict[str, Any]) -> dict[str, Any]:
    basis = original_build_basis()
    catalog = json.loads(source_gen.CATALOG.read_text(encoding="utf-8"))
    recorded = catalog.get("lean_declaration_source")
    replayed = basis.get("lean_declaration_source")
    expected_sha = catalog.get("lean_declaration_source_sha256")
    _assert(isinstance(recorded, str) and isinstance(replayed, str)
            and isinstance(expected_sha, str),
            "Structural catalog lacks the pinned Lean declaration source")
    if recorded == replayed:
        evidence.update({
            "normalization_applied": False,
            "recorded": recorded,
            "replayed_before": replayed,
            "sha256": expected_sha,
        })
        return basis
    _assert(_drive_case_pair(recorded, replayed),
            "Lean declaration source differs by more than Windows drive-letter case")
    old, new = Path(recorded), Path(replayed)
    _assert(old.is_file() and new.is_file(),
            "Lean declaration source path is absent")
    _assert(os.path.samefile(old, new),
            "Lean declaration source drive aliases are not the same file")
    old_sha, new_sha = base.sha_file(old), base.sha_file(new)
    _assert(old_sha == new_sha == expected_sha,
            "Lean declaration source drive aliases differ in bytes")
    basis["lean_declaration_source"] = recorded
    evidence.update({
        "normalization_applied": True,
        "field": "lean_declaration_source",
        "recorded": recorded,
        "replayed_before": replayed,
        "replayed_after": recorded,
        "suffix_exact_after_drive": True,
        "drive_letters_equal_case_insensitive": True,
        "samefile": True,
        "recorded_sha256": old_sha,
        "replayed_sha256": new_sha,
    })
    return basis


def _replay_source_certificate_windows(path: Path, evidence: dict[str, Any]):
    structural = generic.structural
    expected_path = structural.SOURCE_CERTIFICATE.resolve()
    _assert(Path(path).resolve() == expected_path,
            "Only the dedicated structural 74-row source certificate is accepted")
    supplied = json.loads(expected_path.read_text(encoding="utf-8"))
    replayed, rows = structural.source_certifier.validate()
    differences = recursive_diff.differences(supplied, replayed)
    fields = {row["field"] for row in differences}
    _assert(fields in (set(), {SOURCE_PATH_FIELD, SOURCE_ROOT_FIELD})
            and len(differences) == len(fields),
            "Structural source certificate differs outside the two authenticated Lean OLean path fields")
    normalized = copy.deepcopy(replayed)
    old_rows = supplied["actual_evidence"]["olean_resolution"]["dependency_oleans"]
    new_rows = normalized["actual_evidence"]["olean_resolution"]["dependency_oleans"]
    _assert(len(old_rows) == len(new_rows) and old_rows and new_rows,
            "Structural source OLean resolution row count differs")
    old, new = old_rows[0], new_rows[0]
    _assert(old.get("module") == new.get("module") == "Lean"
            and old.get("sha256") == new.get("sha256") == LEAN_OLEAN_SHA256,
            "Structural source first OLean row is not the fixed Lean dependency")
    path_changed = old["path"] != new["path"]
    root_changed = old["resolved_search_root"] != new["resolved_search_root"]
    _assert(path_changed == root_changed == bool(differences),
            "Lean OLean path and search-root drive spelling did not change together")
    path_evidence: dict[str, Any] = {
        "normalization_applied": bool(differences),
        "fields": [SOURCE_PATH_FIELD, SOURCE_ROOT_FIELD] if differences else [],
        "module": "Lean",
        "sha256": LEAN_OLEAN_SHA256,
    }
    if differences:
        old_path, new_path = Path(old["path"]), Path(new["path"])
        old_root, new_root = Path(old["resolved_search_root"]), Path(new["resolved_search_root"])
        _assert(_drive_case_pair(old["path"], new["path"])
                and _drive_case_pair(old["resolved_search_root"], new["resolved_search_root"]),
                "Lean OLean path fields differ by more than Windows drive-letter case")
        _assert(old_path.is_file() and new_path.is_file()
                and old_root.is_dir() and new_root.is_dir(),
                "Lean OLean file or search root is absent")
        _assert(os.path.samefile(old_path, new_path)
                and os.path.samefile(old_root, new_root),
                "Lean OLean drive aliases are not the same file/root")
        _assert(base.sha_file(old_path) == base.sha_file(new_path) == LEAN_OLEAN_SHA256,
                "Lean OLean drive aliases differ in bytes")
        _assert(os.path.samefile(old_root / "Lean.olean", old_path)
                and os.path.samefile(new_root / "Lean.olean", new_path),
                "Recorded Lean search roots do not resolve to the authenticated Lean.olean")
        path_evidence.update({
            "recorded_path": old["path"],
            "replayed_path_before": new["path"],
            "recorded_search_root": old["resolved_search_root"],
            "replayed_search_root_before": new["resolved_search_root"],
            "suffixes_exact_after_drive": True,
            "drive_letters_equal_case_insensitive": True,
            "file_samefile": True,
            "root_samefile": True,
            "root_resolves_authenticated_olean": True,
        })
        new["path"] = old["path"]
        new["resolved_search_root"] = old["resolved_search_root"]
    _assert(supplied == normalized
            and supplied.get("validated") is True
            and supplied.get("source_only_original_kernel_certificate") is True
            and supplied.get("certificate_scope") == "partial-source-only-two-atomic-structure-families"
            and supplied.get("partial") is True
            and supplied.get("platform_ready") is False
            and supplied.get("usable_as_full_source_certificate") is False
            and supplied.get("row_count") == source_gen.EXPECTED_ROWS,
            "Structural source certificate differs after exact Lean OLean path reconciliation")
    evidence.update(path_evidence)
    return supplied, rows


def struct_cert_evidence(module: str) -> dict[str, Any]:
    _assert(os.name == "nt", "Windows structural certificate adapter requires Windows")
    original = source_gen.build_basis
    original_source_replay = generic.structural.replay_source_certificate
    normalization: dict[str, Any] = {}
    source_certificate_normalization: dict[str, Any] = {}

    def wrapped_build_basis() -> dict[str, Any]:
        return _reconciled_basis(original, normalization)

    source_gen.build_basis = wrapped_build_basis
    generic.structural.replay_source_certificate = (
        lambda path: _replay_source_certificate_windows(path, source_certificate_normalization)
    )
    try:
        evidence = generic.struct_cert_evidence(module)
    finally:
        generic.structural.replay_source_certificate = original_source_replay
        source_gen.build_basis = original
    _assert("normalization_applied" in normalization,
            "Structural source replay did not exercise the catalog basis")
    return {
        **evidence,
        "windows_catalog_path_adapter": base.task_relative(Path(__file__).resolve()),
        "windows_catalog_path_adapter_sha256": base.sha_file(Path(__file__).resolve()),
        "windows_catalog_path_reconciliation": normalization,
        "windows_source_certificate_path_reconciliation": source_certificate_normalization,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--module", required=True)
    args = parser.parse_args()
    print(json.dumps(struct_cert_evidence(args.module), ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
