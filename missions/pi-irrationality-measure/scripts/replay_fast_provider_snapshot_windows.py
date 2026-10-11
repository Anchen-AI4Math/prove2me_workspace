"""Recheck frozen fast snapshot provenance across Windows drive-case aliases."""
from pathlib import Path
import prepare_fast_provider_snapshot as frozen
from provider_source_subset_cache_windows import _drive_case_pair


def checked_fast_generated_snapshot(result):
    stage, fast, jsonl, provenance, imports_manifest = frozen.layout(result)
    bundle, generated, edits, pins = frozen.check_base(result)
    document = frozen.read(provenance)
    evidence = frozen.provider_evidence(result)
    if evidence is None:
        raise ValueError("Fast snapshot actual provider OLean is pending")
    recorded = (document.get("actual_provider_evidence") or {}).get("actual_import_oleans")
    current = evidence.get("actual_import_oleans")
    if not isinstance(recorded, list) or not isinstance(current, list) or len(recorded) != len(current):
        raise ValueError("Fast snapshot exact OLean dependency lists differ")
    for prior, live in zip(recorded, current, strict=True):
        for field in ("path", "resolved_search_root"):
            _drive_case_pair(prior.get(field), live.get(field))
            # Only the same actual filesystem object with an exact suffix can
            # inherit its recorded spelling. All other fields remain live.
            live[field] = prior[field]
    if document != frozen.expected_provenance(result, generated, edits, pins, evidence):
        raise ValueError("Fast snapshot exact provenance reconstruction mismatch after drive-case check")
    if fast.read_bytes() != generated:
        raise ValueError("Fast snapshot source bytes differ from frozen exact reconstruction")
    if frozen.read(imports_manifest) != frozen.expected_imports_manifest(result, bundle, pins, evidence):
        raise ValueError("Fast snapshot exact import/source certificate differs")
    return {
        "source": fast.relative_to(frozen.VERIFICATION).as_posix(),
        "root": stage.relative_to(frozen.VERIFICATION).as_posix(),
        "manifest": imports_manifest, "module": "SnapshotGeneratedFast",
        "imports": ["Lean", result["platform_module"]], "mode": "modecheck",
        "role": "generated-snapshot", "generated_jsonl": jsonl,
        "fast_generated_provenance": frozen.rel(provenance),
        "fast_generated_provenance_sha256": frozen.sha(provenance), "runnable": True,
    }
