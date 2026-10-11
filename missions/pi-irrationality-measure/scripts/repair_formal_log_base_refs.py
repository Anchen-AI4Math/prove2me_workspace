"""Prepare the minimal reserved-keyword repair for the f1 WithRefs source."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import generate_formal_log_truncation_provider as formal
import stage_formal_log_base_node as base

TASK, ROOT, V = formal.TASK, formal.ROOT, formal.V
STAGE = V / "flp3/f1"
OLD = STAGE / "SnapshotGeneratedWithRefs.lean"
NEW = STAGE / "SnapshotGeneratedWithRefs2.lean"
OLD_MANIFEST = STAGE / "c4.json"
OLD_RECORD = Path(str(OLD) + ".preflight.json")
NEW_MANIFEST = STAGE / "c4b.json"
PREPARATION = STAGE / "refs-repair-preparation.json"
OLD_GENERATED = STAGE / "generated-type.json"
OLD_GENERATED_ARCHIVE = STAGE / "failed-withrefs-generated-type.json"
SELF = Path(__file__).resolve()
REPAIRS = [
    (b"def export (requests : Array Name)", b"def exportProofRefs (requests : Array Name)"),
    (b"FormalLogProofReferenceSnapshot.export #[", b"FormalLogProofReferenceSnapshot.exportProofRefs #["),
]


def prepare():
    before = OLD.read_bytes()
    after = before
    ledger = []
    for source, replacement in REPAIRS:
        if after.count(source) != 1 or after.count(replacement) != 0:
            raise ValueError("Reserved-keyword repair anchor is not unique and fresh")
        offset = after.index(source)
        after = after.replace(source, replacement, 1)
        ledger.append({"start": offset, "end": offset + len(source),
                       "source": source.decode(), "replacement": replacement.decode()})
    if after == before or len(after) - len(before) != 18:
        raise ValueError("Repair is not exactly the two expected identifier expansions")
    base.write_exact(NEW, after)
    old_manifest = formal.read(OLD_MANIFEST)
    if old_manifest["output"] != OLD.relative_to(ROOT).as_posix() or old_manifest["output_sha256"] != formal.sha(OLD):
        raise ValueError("Failed WithRefs source is not bound by c4.json")
    if not OLD_RECORD.is_file():
        raise ValueError("Failed WithRefs preflight record must be preserved")
    record = formal.read(OLD_RECORD)
    log = TASK / record["log"]
    if (record.get("exit_code") == 0 or record.get("timed_out") is not False
            or record.get("source_sha256_before") != formal.sha(OLD)
            or not log.is_file()):
        raise ValueError("Expected exact non-timeout failed fourth preflight evidence")
    if not OLD_GENERATED.is_file():
        raise ValueError("Failed prefix export did not preserve generated-type.json")
    base.write_exact(OLD_GENERATED_ARCHIVE, OLD_GENERATED.read_bytes())
    pins = dict(old_manifest["input_hashes"])
    pins.update({formal.rel(SELF): formal.sha(SELF), formal.rel(OLD): formal.sha(OLD),
                 formal.rel(OLD_MANIFEST): formal.sha(OLD_MANIFEST),
                 formal.rel(OLD_RECORD): formal.sha(OLD_RECORD), formal.rel(log): formal.sha(log),
                 formal.rel(OLD_GENERATED_ARCHIVE): formal.sha(OLD_GENERATED_ARCHIVE),
                 formal.rel(STAGE / "preparation.json"): formal.sha(STAGE / "preparation.json")})
    document = dict(old_manifest)
    document.update(output=NEW.relative_to(ROOT).as_posix(), output_sha256=formal.sha(NEW),
                    input_hashes=pins, repair_of=formal.rel(OLD), repair_of_sha256=formal.sha(OLD),
                    repair_ledger=ledger, prior_failed_preflight=formal.rel(OLD_RECORD),
                    prior_failed_preflight_sha256=formal.sha(OLD_RECORD), node_validated=False,
                    Lean_started=False, submission_ready=False)
    base.write_exact(NEW_MANIFEST, document)
    preparation = {"schema_version": 1, "artifact_kind": "formal-log-proof-ref-keyword-repair",
        "source": formal.rel(OLD), "source_sha256": formal.sha(OLD),
        "output": formal.rel(NEW), "output_sha256": formal.sha(NEW),
        "manifest": formal.rel(NEW_MANIFEST), "manifest_sha256": formal.sha(NEW_MANIFEST),
        "repair_ledger": ledger, "prior_failed_preflight": formal.rel(OLD_RECORD),
        "prior_failed_preflight_sha256": formal.sha(OLD_RECORD), "prior_failed_log": formal.rel(log),
        "prior_failed_log_sha256": formal.sha(log), "only_function_identifier_renamed": True,
        "prior_failed_generated_type_archive": formal.rel(OLD_GENERATED_ARCHIVE),
        "prior_failed_generated_type_archive_sha256": formal.sha(OLD_GENERATED_ARCHIVE),
        "old_source_and_evidence_preserved": True, "Lean_started": False,
        "validated": False, "submission_ready": False}
    base.write_exact(PREPARATION, preparation)
    return preparation


def check():
    preparation = formal.read(PREPARATION)
    before, after = OLD.read_bytes(), NEW.read_bytes()
    reconstructed = before
    for row in preparation["repair_ledger"]:
        source, replacement = row["source"].encode(), row["replacement"].encode()
        if reconstructed.count(source) != 1:
            raise ValueError("Repair ledger source anchor differs")
        reconstructed = reconstructed.replace(source, replacement, 1)
    if reconstructed != after or formal.sha(NEW) != preparation["output_sha256"]:
        raise ValueError("Repaired source differs from the exact two-edit reconstruction")
    manifest = formal.read(NEW_MANIFEST)
    formal.runner.verify_manifest_inputs(manifest)
    formal.runner.verify_source_certificate(NEW, manifest)
    imports = formal.runner.certified_imports(NEW, manifest)
    path_lengths = {str(path): len(str(path)) for path in [NEW.resolve(),
        Path(str(NEW.resolve()) + ".preflight.json"), NEW_MANIFEST.resolve()]}
    if max(path_lengths.values()) >= 240:
        raise ValueError("Repair compiler path exceeds the conservative Windows budget")
    return {"exact_two_identifier_edits": True, "imports": len(imports),
            "maximum_absolute_path_length": max(path_lengths.values()),
            "old_failed_evidence_preserved": True, "Lean_started": False,
            "validated": False, "submission_ready": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--prepare", action="store_true")
    group.add_argument("--check", action="store_true")
    args = parser.parse_args()
    print(json.dumps(prepare() if args.prepare else check(), indent=2))


if __name__ == "__main__":
    main()
