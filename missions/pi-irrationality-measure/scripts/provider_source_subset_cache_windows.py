#!/usr/bin/env python3
"""Windows-stable consumer for the frozen 174-row source-subset certificate.

The original consumer is an input to the already compiled source exporter and
therefore remains byte-frozen.  This wrapper repeats its fail-closed checks but
permits Windows drive-letter case differences in exactly two OLean provenance
fields.  The suffix must be byte-identical and both spellings must resolve via
``Path.samefile`` to the same existing filesystem object.
"""

from __future__ import annotations

import copy
import json
import os
from pathlib import Path
import re
from typing import Any

import generate_provider_source_subset_snapshot as gen
import provider_source_subset_cache as frozen_consumer
import validate_provider_source_subset_snapshot as validator
import validate_shared_source_snapshot as shared


EXPECTED_CERTIFICATE = frozen_consumer.EXPECTED_CERTIFICATE
DRIVE_PATH = re.compile(r"^[A-Za-z]:[\\/]")
NORMALIZED_FIELDS = ("path", "resolved_search_root")


def _assert(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def _drive_case_pair(left: Any, right: Any) -> tuple[Any, Any]:
    """Return a common spelling only for an actual Windows drive-case alias."""
    if left == right:
        return left, right
    _assert(os.name == "nt" and isinstance(left, str) and isinstance(right, str),
            "Source-subset certificate differs outside Windows path normalization")
    _assert(DRIVE_PATH.fullmatch(left[:3]) is not None
            and DRIVE_PATH.fullmatch(right[:3]) is not None,
            "Windows normalization requires absolute drive paths")
    _assert(left[0].lower() == right[0].lower() and left[1:] == right[1:],
            "Windows normalization permits only drive-letter case")
    left_path, right_path = Path(left), Path(right)
    _assert(left_path.exists() and right_path.exists() and left_path.samefile(right_path),
            "Windows drive-letter aliases do not identify the same existing file")
    canonical = left[0].lower() + left[1:]
    return canonical, canonical


def _normalize_certificate_pair(certificate: dict[str, Any],
                                recomputed: dict[str, Any]) -> tuple[dict[str, Any], dict[str, Any]]:
    """Normalize only shard/OLean dependency path and search-root drive case."""
    left, right = copy.deepcopy(certificate), copy.deepcopy(recomputed)
    left_shards, right_shards = left.get("shards"), right.get("shards")
    _assert(isinstance(left_shards, list) and isinstance(right_shards, list)
            and len(left_shards) == len(right_shards),
            "Source-subset certificate shard sets differ")
    for left_shard, right_shard in zip(left_shards, right_shards, strict=True):
        left_deps = (left_shard.get("olean_resolution") or {}).get("dependency_oleans")
        right_deps = (right_shard.get("olean_resolution") or {}).get("dependency_oleans")
        _assert(isinstance(left_deps, list) and isinstance(right_deps, list)
                and len(left_deps) == len(right_deps),
                "Source-subset OLean dependency sets differ")
        for left_dep, right_dep in zip(left_deps, right_deps, strict=True):
            for field in NORMALIZED_FIELDS:
                left_dep[field], right_dep[field] = _drive_case_pair(
                    left_dep.get(field), right_dep.get(field))
    return left, right


def drive_letter_negative_fixtures(existing_path: Path) -> dict[str, bool]:
    """Exercise the exact rejection boundary without changing certificate data."""
    actual = str(existing_path.resolve())
    _assert(DRIVE_PATH.fullmatch(actual[:3]) is not None and existing_path.is_file(),
            "Negative fixtures require an existing Windows drive file")
    opposite = actual[0].swapcase() + actual[1:]
    accepted = _drive_case_pair(actual, opposite)[0] == actual[0].lower() + actual[1:]

    def rejected(left: str, right: str) -> bool:
        try:
            _drive_case_pair(left, right)
        except ValueError:
            return True
        return False

    other_drive = ("Z" if actual[0].lower() != "z" else "Y") + actual[1:]
    return {
        "actual_drive_case_alias_accepted": accepted,
        "different_drive_rejected": rejected(actual, other_drive),
        "different_suffix_rejected": rejected(actual, actual + ".different"),
        "relative_path_rejected": rejected(actual, actual[3:]),
        "nonexistent_same_suffix_alias_rejected": rejected(
            "C:\\definitely-missing-provider-cache\\x.olean",
            "c:\\definitely-missing-provider-cache\\x.olean"),
    }


def validate_provider_source_subset_cache(
    certificate_path: Path, original_requests: list[dict[str, Any]],
) -> dict[str, Any]:
    certificate_path = certificate_path.resolve()
    _assert(certificate_path == EXPECTED_CERTIFICATE.resolve(),
            "Only the canonical provider source-subset certificate is accepted")
    certificate = shared.read_json(certificate_path, "provider source-subset certificate")
    recomputed, rows = validator.validate_subset(require_actual=True)
    left, right = _normalize_certificate_pair(certificate, recomputed)
    _assert(left == right,
            "Provider source-subset certificate differs from full live revalidation")
    _assert(certificate.get("validated") is True
            and certificate.get("source_only_original_kernel_certificate") is True
            and certificate.get("partial") is True
            and certificate.get("platform_ready") is False
            and certificate.get("usable_as_full_source_certificate") is False
            and certificate.get("consumer_requires_generated_kernel_comparison") is True
            and certificate.get("row_count") == 174
            and certificate.get("provider_bundle_count") == 29,
            "Provider source-subset scope flags are invalid")

    names = [request.get("source_graph_name") for request in original_requests]
    _assert(len(names) == len(set(names)), "Provider original requests repeat a source name")
    subset_catalog = shared.read_json(gen.SUBSET_CATALOG, "provider subset catalog")
    owners = {row["source_name"]: row for row in subset_catalog["owners"]}
    selected: list[dict[str, Any]] = []
    selected_evidence: list[dict[str, Any]] = []
    for request in original_requests:
        name = request.get("source_graph_name")
        row, owner = rows.get(name), owners.get(name)
        _assert(row is not None and owner is not None,
                f"Requested declaration is outside the certified 174-row subset: {name}")
        _assert(request.get("expected_module") == row["sourceModule"] == owner["source_module"]
                and request.get("expected_kind") == row["graphKind"] == owner["graph_kind"]
                and request.get("expected_public_name") == name
                and request.get("expected_user_name") == name
                and request.get("source_was_private") is False
                and owner.get("source_private") is False
                and request.get("command_unit") == row["commandUnit"] == owner["command_unit"]
                and request.get("decl_graph_sha256") == row["declGraphSha256"]
                and request.get("decl_graph_row_sha256") == row["declGraphRowSha256"],
                f"Provider request differs from certified subset owner: {name}")
        selected.append(row)
        selected_evidence.append({
            "source_name": name,
            "source_module": row["sourceModule"],
            "graph_kind": row["graphKind"],
            "command_unit": row["commandUnit"],
            "type_canonical_sha256": shared.sha_bytes(json.dumps(
                shared.normalize_kernel(row, "type"), separators=(",", ":"), ensure_ascii=False
            ).encode("utf-8")),
            "value_canonical_sha256": None if row["value"] is None else shared.sha_bytes(json.dumps(
                shared.normalize_kernel(row, "value"), separators=(",", ":"), ensure_ascii=False
            ).encode("utf-8")),
            "axioms": row["axioms"],
            "std3_only": set(row["axioms"]) <= shared.STD3,
        })
    return {
        "rows": selected,
        "evidence": {
            "strategy": "provider-source-subset-cache; original snapshot compile skipped",
            "certificate": shared.task_relative(certificate_path),
            "certificate_sha256": shared.sha(certificate_path),
            "certificate_scope": "partial-source-only-exact-provider-request-set",
            "source_version": 875,
            "source_commit": certificate["source_commit"],
            "authenticated_subset_rows": 174,
            "authenticated_provider_bundles": 29,
            "full_owner_catalog_rows_authenticated_as_metadata": 6148,
            "selected_rows": selected_evidence,
            "partial": True,
            "platform_readiness_claimed": False,
            "usable_as_full_source_certificate": False,
            "generated_kernel_comparison_still_required": True,
            "theorem_values_omitted": True,
            "definition_values_complete": True,
            "std3_only": True,
            "certificate_comparison_normalization": {
                "platform": "Windows only",
                "fields": [
                    "shards[*].olean_resolution.dependency_oleans[*].path",
                    "shards[*].olean_resolution.dependency_oleans[*].resolved_search_root",
                ],
                "rule": "drive-letter case only; suffix exact; Path.samefile required",
            },
        },
    }
