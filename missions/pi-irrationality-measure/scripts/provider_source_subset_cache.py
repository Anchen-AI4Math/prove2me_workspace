#!/usr/bin/env python3
"""Fail-closed consumer for the actual 174-row provider source-subset certificate."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import generate_provider_source_subset_snapshot as gen
import validate_provider_source_subset_snapshot as validator
import validate_shared_source_snapshot as shared


TASK = Path(__file__).resolve().parents[1]
EXPECTED_CERTIFICATE = validator.CERTIFICATE


def _assert(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def validate_provider_source_subset_cache(
    certificate_path: Path, original_requests: list[dict[str, Any]],
) -> dict[str, Any]:
    """Authenticate the whole partial certificate, then return only requested rows."""
    certificate_path = certificate_path.resolve()
    _assert(certificate_path == EXPECTED_CERTIFICATE.resolve(),
            "Only the canonical provider source-subset certificate is accepted")
    certificate = shared.read_json(certificate_path, "provider source-subset certificate")
    recomputed, rows = validator.validate_subset(require_actual=True)
    _assert(certificate == recomputed,
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
        row = rows.get(name)
        owner = owners.get(name)
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
        },
    }
