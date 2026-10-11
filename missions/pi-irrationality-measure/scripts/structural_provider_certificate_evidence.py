#!/usr/bin/env python3
"""Replay a structural provider certificate and return publisher evidence.

The publisher must not trust a stored ``validated`` flag.  This helper invokes
the frozen structural provider validator, intercepts its certificate write in
memory, requires the fully rebuilt report to equal the stored certificate, and
returns a compact evidence object.  It never runs Lean or contacts the API.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

import generate_shared_source_snapshot as base
import validate_structural_provider_bundle as structural


TASK = Path(__file__).resolve().parents[1]
PROVIDER_ROOT = TASK / "verification" / "providers-complete-preview"
SOURCE_CERTIFICATE = (
    TASK / "verification" / "shared-source-snapshot" / "structural-kernel-74" /
    "StructuralKernelSource74.validation.json"
)
FROZEN_STRUCTURAL_VALIDATOR_SHA256 = (
    "1815f5a932a66671ece570018d394e599ba134913713314f4d51eabbd554b085"
)


def _assert(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def _read(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def struct_cert_evidence(module: str) -> dict[str, Any]:
    validator_path = Path(structural.__file__).resolve()
    _assert(base.sha_file(validator_path) == FROZEN_STRUCTURAL_VALIDATOR_SHA256,
            "Frozen structural provider validator bytes changed")
    result = structural.structural_check(module)
    certificate_path = (
        result["snapshot_dir"] / "provider-validation-structural.json"
    ).resolve()
    _assert(certificate_path.is_file(), "Structural provider certificate is absent")
    before = certificate_path.read_bytes()
    stored = json.loads(before)
    captured: dict[str, Any] = {}
    original_write = structural.base.write_json

    def capture(path: Path, value: Any) -> None:
        _assert(Path(path).resolve() == certificate_path,
                "Structural replay attempted an unexpected write")
        _assert("report" not in captured, "Structural replay attempted multiple writes")
        captured["report"] = value

    structural.base.write_json = capture
    try:
        replay = structural.certify(result, SOURCE_CERTIFICATE)
    finally:
        structural.base.write_json = original_write
    _assert(captured.get("report") == stored,
            "Fresh structural provider report differs from stored certificate")
    _assert(certificate_path.read_bytes() == before,
            "Structural certificate bytes changed during read-only replay")
    _assert(all(replay.get(key) == value for key, value in stored.items()),
            "Structural replay return value differs from stored certificate")
    _assert(replay.get("certificate") == base.task_relative(certificate_path)
            and replay.get("certificate_sha256") == base.sha_file(certificate_path),
            "Structural replay certificate identity differs")
    _assert(stored.get("validated") is True
            and stored.get("row_count") == len(stored.get("compared_names", []))
            and stored.get("types_equal") is True
            and stored.get("definition_values_equal") is True
            and stored.get("axioms_equal_and_std3") is True
            and stored.get("inductive_constructor_recursor_metadata_equal") is True
            and stored.get("recursor_rule_nfields_and_rhs_equal") is True
            and stored.get("whole_atomic_graph_ci_coverage_equal") is True,
            "Structural certificate is missing a required kernel equality")
    return {
        "schema_version": 1,
        "artifact_kind": "structural-provider-certificate-replay-evidence",
        "validated": True,
        "module": module,
        "source_module": stored["source_module"],
        "platform_module": stored["platform_module"],
        "family_root": stored["family_root"],
        "certificate": base.task_relative(certificate_path),
        "certificate_sha256": base.sha_file(certificate_path),
        "certificate_schema_version": stored["schema_version"],
        "certificate_artifact_kind": stored["artifact_kind"],
        "source_certificate": stored["source_certificate"],
        "source_certificate_sha256": stored["source_certificate_sha256"],
        "source_certificate_replayed_exactly": True,
        "validator": base.task_relative(validator_path),
        "validator_sha256": FROZEN_STRUCTURAL_VALIDATOR_SHA256,
        "publisher_evidence_helper": base.task_relative(Path(__file__).resolve()),
        "publisher_evidence_helper_sha256": base.sha_file(Path(__file__).resolve()),
        "row_count": stored["row_count"],
        "compared_names": stored["compared_names"],
        "provider_preflight": stored["provider_preflight"],
        "generated_preflight": stored["generated_preflight"],
        "generated_provenance": stored["generated_provenance"],
        "generated_provenance_sha256": stored["generated_provenance_sha256"],
        "generated_jsonl": stored["generated_jsonl"],
        "generated_jsonl_sha256": stored["generated_jsonl_sha256"],
        "types_equal": True,
        "definition_values_equal": True,
        "axioms_equal_and_std3": True,
        "inductive_constructor_recursor_metadata_equal": True,
        "recursor_rule_nfields_and_rhs_equal": True,
        "whole_atomic_graph_ci_coverage_equal": True,
        "stored_certificate_equal_to_fresh_replay": True,
        "certificate_bytes_unchanged": True,
        "lean_started": False,
        "api_used": False,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--module", required=True)
    args = parser.parse_args()
    print(json.dumps(struct_cert_evidence(args.module), ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
