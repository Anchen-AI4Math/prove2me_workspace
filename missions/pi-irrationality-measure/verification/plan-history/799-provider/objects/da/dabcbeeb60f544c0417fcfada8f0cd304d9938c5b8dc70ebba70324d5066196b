#!/usr/bin/env python3
"""Preserve the complete 799-module provider-plan/publication lineage.

This is byte preservation only.  It never runs Lean and never upgrades the
archived preview plans into final plans.  Existing archive bytes are immutable.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
from typing import Any

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
DEST = TASK / "verification/plan-history/799-provider"
BASE_ARCHIVE = TASK / "verification/plan-history/799-publication/archive-manifest.json"
LEAF = "Def_OAI_NumberTheory_PiExponent_LocalAlgebra_LocalizedComponent"
LEAF_ROOT = TASK / "verification/providers-preview/all-shared-safe-leaves"
PUBLICATION_ID = "bdec8e94-fc3a-4f5a-9aef-c76bd32695d0"


def sha_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def task_relative(path: Path) -> str:
    return path.resolve().relative_to(TASK.resolve()).as_posix()


def normalize_task_path(value: str) -> Path | None:
    value = value.replace("\\", "/")
    path = Path(value)
    candidates = [path] if path.is_absolute() else [TASK / path, ROOT / path]
    for candidate in candidates:
        resolved = candidate.resolve()
        if resolved.is_relative_to(TASK.resolve()) and resolved.is_file():
            return resolved
    return None


def json_file(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def base_archive_index() -> dict[str, dict[str, Any]]:
    manifest = json_file(BASE_ARCHIVE)
    if manifest.get("indexed_modules") != 799:
        raise ValueError("The base publication archive is not the 799-module lineage")
    result = {}
    for relative, row in manifest["input_files"].items():
        archived = TASK / row["archive"]
        raw = archived.read_bytes()
        if sha_bytes(raw) != row["sha256"] or len(raw) != row["bytes"]:
            raise ValueError("Base archive byte check failed: " + relative)
        normalized = normalize_task_path(relative)
        canonical = task_relative(normalized) if normalized is not None else relative
        result[canonical] = {"path": archived, "sha256": row["sha256"]}
    return result


def referenced_paths(value: Any):
    """Yield task-local file strings from manifests and evidence records."""
    path_keys = {
        "path", "source", "original_source", "facts", "output", "record", "log",
        "output_olean", "manifest", "provider_source", "snapshot_dir",
        "provider_plan", "provider_artifact_plan", "snapshot_core",
        "snapshot_core_lineage", "original_exporter", "generated_exporter",
        "generated_bundle", "expected_original_jsonl", "expected_generated_jsonl",
        "validation", "publication", "payload",
    }
    if isinstance(value, dict):
        inputs = value.get("input_hashes")
        if isinstance(inputs, dict):
            for path, expected in inputs.items():
                if isinstance(path, str) and isinstance(expected, str):
                    yield path, expected
        for key, child in value.items():
            if key in path_keys and isinstance(child, str):
                expected = None
                for suffix in ("_sha256", "Sha256"):
                    candidate = value.get(key + suffix)
                    if isinstance(candidate, str):
                        expected = candidate
                yield child, expected
            yield from referenced_paths(child)
    elif isinstance(value, list):
        for child in value:
            yield from referenced_paths(child)


def main() -> None:
    base_archive = base_archive_index()
    old_plan = json_file(TASK / "verification/platform-unit-plan-preview.json")
    if old_plan.get("complete_extraction") or len(old_plan.get("source_declarations_pending_ast", [])) != 451:
        raise ValueError("Current preview plan is no longer the archived 799-module provider basis")

    seeds: set[Path] = {
        Path(__file__).resolve(),
        TASK / "scripts/plan_platform_units_providers.py",
        TASK / "scripts/generate_platform_provider_bundles.py",
        TASK / "scripts/audit_provider_residuals.py",
        TASK / "scripts/validate_provider_bundle.py",
        TASK / "scripts/platform_definition_certificate.py",
        TASK / "scripts/publish_provider_bundle.py",
        TASK / "scripts/preflight_staged_module.py",
        TASK / "verification/TypeOnlyTheoremSnapshotCore.inc",
        TASK / "verification/TypeOnlyTheoremSnapshotCore.lineage.json",
    }
    for root in (TASK / "verification/provider-plans",):
        seeds.update(path for path in root.rglob("*") if path.is_file())
    for path in (
        LEAF_ROOT / "Definitions" / f"{LEAF}.lean",
        LEAF_ROOT / "Definitions" / f"{LEAF}.manifest.json",
        LEAF_ROOT / "Definitions" / f"{LEAF}.lean.preflight.json",
    ):
        seeds.add(path)
    for directory in (
        LEAF_ROOT / "ledgers" / LEAF,
        LEAF_ROOT / "snapshots" / LEAF,
        LEAF_ROOT / "validation" / LEAF,
    ):
        seeds.update(path for path in directory.rglob("*") if path.is_file())

    validation = json_file(LEAF_ROOT / "validation" / LEAF / "provider-validation.json")
    publication = json_file(LEAF_ROOT / "validation" / LEAF / "publication.json")
    if not validation.get("validated") or publication.get("definition_id") != PUBLICATION_ID:
        raise ValueError("LocalizedComponent publication evidence is absent or mismatched")
    for row in validation["preflights"]:
        for key in ("record", "log", "output_olean"):
            if row.get(key):
                path = normalize_task_path(row[key])
                if path is not None:
                    seeds.add(path)

    expected_by_path: dict[str, set[str]] = {}
    queue = list(seeds)
    seen: set[Path] = set()
    while queue:
        path = queue.pop()
        if not path.exists() or not path.is_file() or not path.resolve().is_relative_to(TASK.resolve()):
            raise ValueError("Missing or external archive seed: " + str(path))
        path = path.resolve()
        if path in seen:
            continue
        seen.add(path)
        if path.suffix != ".json":
            continue
        try:
            value = json_file(path)
        except (UnicodeDecodeError, json.JSONDecodeError):
            continue
        for raw_path, expected in referenced_paths(value):
            referenced = normalize_task_path(raw_path)
            if referenced is None:
                continue
            relative = task_relative(referenced)
            if expected is not None:
                expected_by_path.setdefault(relative, set()).add(expected)
            queue.append(referenced)

    # Every provider manifest input must be represented even if the current
    # working copy has already moved on; matching bytes may come from the base
    # immutable archive.
    provider_manifests = [
        TASK / "verification/provider-plans/minimum/provider-plan-manifest.json",
        TASK / "verification/provider-plans/all-shared-public/provider-plan-manifest.json",
        LEAF_ROOT / "Definitions" / f"{LEAF}.manifest.json",
    ]
    for manifest_path in provider_manifests:
        for relative, expected in json_file(manifest_path).get("input_hashes", {}).items():
            normalized = normalize_task_path(relative)
            if normalized is not None:
                canonical = task_relative(normalized)
            else:
                canonical = relative.replace("\\", "/")
                prefix = "missions/pi-irrationality-measure/"
                if canonical.startswith(prefix):
                    canonical = canonical.removeprefix(prefix)
            expected_by_path.setdefault(canonical, set()).add(expected)

    records = {}
    all_relatives = {task_relative(path) for path in seen} | set(expected_by_path)
    for relative in sorted(all_relatives):
        expected_set = expected_by_path.get(relative, set())
        if len(expected_set) > 1:
            raise ValueError("Conflicting expected hashes for " + relative)
        expected = next(iter(expected_set), None)
        current = TASK / relative
        provenance = "current-799-provider-witness"
        source = current
        if expected is not None and (not current.is_file() or sha_bytes(current.read_bytes()) != expected):
            archived = base_archive.get(relative)
            if archived is None or archived["sha256"] != expected:
                raise ValueError("Expected provider input bytes are unavailable: " + relative)
            source = archived["path"]
            provenance = "preserved-799-publication-archive"
        if not source.is_file():
            raise ValueError("Archive input missing: " + relative)
        raw = source.read_bytes()
        digest = sha_bytes(raw)
        if expected is not None and digest != expected:
            raise ValueError("Archive input hash mismatch: " + relative)
        # Content-addressed storage avoids Windows' legacy path ceiling for
        # deeply nested snapshot/preflight filenames and deduplicates repeated
        # plan inputs.
        output = DEST / "objects" / digest[:2] / digest
        if output.exists() and output.read_bytes() != raw:
            raise ValueError("Refusing to change immutable provider archive file: " + relative)
        output.parent.mkdir(parents=True, exist_ok=True)
        if not output.exists():
            temporary = output.parent / f".__archive_{os.getpid()}.tmp"
            temporary.write_bytes(raw)
            os.replace(temporary, output)
        records[relative] = {
            "sha256": digest,
            "bytes": len(raw),
            "archive": task_relative(output),
            "provenance": provenance,
            "expected_by_manifest": expected is not None,
        }

    required = {
        "verification/provider-plans/minimum/platform-unit-plan-provider-variant.json",
        "verification/provider-plans/all-shared-public/platform-unit-plan-provider-variant.json",
        f"verification/providers-preview/all-shared-safe-leaves/Definitions/{LEAF}.lean",
        f"verification/providers-preview/all-shared-safe-leaves/Definitions/{LEAF}.manifest.json",
        f"verification/providers-preview/all-shared-safe-leaves/validation/{LEAF}/provider-validation.json",
        f"verification/providers-preview/all-shared-safe-leaves/validation/{LEAF}/publication.json",
    }
    missing = sorted(required - records.keys())
    if missing:
        raise ValueError("Archive coverage missing required witnesses: " + repr(missing))
    report = {
        "schema_version": 1,
        "lineage": "799-module provider preview and first published provider leaf",
        "base_indexed_modules": 799,
        "base_pending_source_declarations": 451,
        "source_commit": "adc7f1241b42e322a6451854ab7e4b4c146bf78a",
        "published_leaf": {
            "module": "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedComponent",
            "definition_id": PUBLICATION_ID,
            "provider_source_sha256": validation["provider_source_sha256"],
            "validated": True,
        },
        "coverage": {
            "file_count": len(records),
            "byte_count": sum(row["bytes"] for row in records.values()),
            "provider_variant_files": sum(path.startswith("verification/provider-plans/") for path in records),
            "localized_component_files": sum(LEAF in path for path in records),
            "manifest_expected_inputs": sum(row["expected_by_manifest"] for row in records.values()),
            "required_witnesses_present": True,
        },
        "files": records,
        "extraction_state_archived": False,
        "reason": "The append-only extraction state is not a deterministic provider input; exact source/facts and frozen 799 plan bytes are preserved instead.",
        "validated_as_new_proof": False,
        "lean_started": False,
        "api_used": False,
    }
    data = (json.dumps(report, indent=2, ensure_ascii=False) + "\n").encode("utf-8")
    manifest_path = DEST / "archive-manifest.json"
    if manifest_path.exists() and manifest_path.read_bytes() != data:
        raise ValueError("Refusing to change immutable provider archive manifest")
    manifest_path.parent.mkdir(parents=True, exist_ok=True)
    if not manifest_path.exists():
        manifest_path.write_bytes(data)
    print(json.dumps({"archived_files": len(records), "bytes": report["coverage"]["byte_count"],
                      "manifest": task_relative(manifest_path), "lean_started": False,
                      "api_used": False}))


if __name__ == "__main__":
    main()
