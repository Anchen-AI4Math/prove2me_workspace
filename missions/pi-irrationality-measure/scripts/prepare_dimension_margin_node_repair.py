"""Prepare a new fourth preflight after the retained `export` parser failure.

Only two exact identifier occurrences in the proof-reference addon change.
The frozen four files, failed WithRefs source/sidecar/log, c1-c4 manifests,
original preparation, and first three successful preflights remain untouched.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import prepare_dimension_margin_node as old
import preflight_staged_module as runner

STAGE, TASK, ROOT = old.STAGE, old.TASK, old.ROOT
SELF = Path(__file__).resolve()
OLD = STAGE / "SnapshotGeneratedWithRefs.lean"
NEW = STAGE / "SnapshotGeneratedWithRefsRepaired.lean"
OLD_RECORD = OLD.with_suffix(".lean.preflight.json")
MANIFEST = STAGE / "c4r.json"
PREP = STAGE / "preparation-repaired.json"


def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def read(path): return json.loads(path.read_text(encoding="utf-8"))
def rel(path): return path.relative_to(TASK).as_posix()


def need(value, message):
    if not value: raise ValueError(message)


def write_exact(path, raw):
    if path.exists():
        need(path.read_bytes() == raw, "Existing repair artifact differs: " + str(path))
    else:
        path.write_bytes(raw)


def source_bytes():
    m = old.inputs()
    old.check()
    base = (STAGE / "SnapshotGenerated.lean").read_bytes()
    failure = read(OLD_RECORD)
    failed_log = TASK / failure["log"]
    need(failure["exit_code"] == 1 and failure["timed_out"] is False
         and failure["source_sha256_before"] == sha(OLD)
         and failure["source_sha256_after"] == sha(OLD)
         and failure["manifest_sha256_before"] == sha(STAGE / "c4.json")
         and failure["log_sha256"] == sha(failed_log), "Retained c4 failure lineage differs")
    need(b"unexpected token 'export'; expected identifier" in failed_log.read_bytes(),
         "Retained c4 failure is not the exact reserved identifier error")
    old_bytes = OLD.read_bytes()
    need(old_bytes.startswith(base), "Failed c4 source lost original exact snapshot prefix")
    addon = old_bytes[len(base):]
    pairs = [(b"def export (", b"def exportProofRefs ("),
             (b"FormalLogProofReferenceSnapshot.export #[",
              b"FormalLogProofReferenceSnapshot.exportProofRefs #[")]
    for before, after in pairs:
        need(addon.count(before) == 1 and addon.count(after) == 0,
             "Exact once-only repair anchor differs: " + repr(before))
        addon = addon.replace(before, after, 1)
    return m, base + addon, failure, failed_log, pairs


def prepare():
    m, raw, failure, failed_log, pairs = source_bytes()
    write_exact(NEW, raw)
    old_prep = read(STAGE / "preparation.json")
    original_manifest = read(STAGE / "c4.json")
    pins = dict(original_manifest["input_hashes"])
    pins.update({rel(SELF): sha(SELF), rel(OLD): sha(OLD),
                 rel(OLD_RECORD): sha(OLD_RECORD), rel(failed_log): sha(failed_log),
                 rel(STAGE / "preparation.json"): sha(STAGE / "preparation.json"),
                 rel(STAGE / "c4.json"): sha(STAGE / "c4.json")})
    doc = {**original_manifest, "artifact_kind": "dimension-margin-repaired-reference-file-import-certificate",
           "output": NEW.relative_to(ROOT).as_posix(), "output_sha256": sha(NEW),
           "input_hashes": pins, "repair_of": rel(OLD), "failed_preflight": rel(OLD_RECORD),
           "repair_kind": "two_exact_identifier_occurrences_in_appended_reference_collector"}
    write_exact(MANIFEST, (json.dumps(doc, indent=2, ensure_ascii=False) + "\n").encode())
    note = {"schema_version": 1, "artifact_kind": "dimension-margin-reference-collector-repair",
            "frozen_manifest_sha256": sha(STAGE / "manifest.json"),
            "old_preparation": rel(STAGE / "preparation.json"),
            "old_preparation_sha256": sha(STAGE / "preparation.json"),
            "failed_source": rel(OLD), "failed_source_sha256": sha(OLD),
            "failed_manifest": rel(STAGE / "c4.json"), "failed_manifest_sha256": sha(STAGE / "c4.json"),
            "failed_preflight": rel(OLD_RECORD), "failed_preflight_sha256": sha(OLD_RECORD),
            "failed_log": rel(failed_log), "failed_log_sha256": sha(failed_log),
            "repaired_source": rel(NEW), "repaired_source_sha256": sha(NEW),
            "repaired_manifest": rel(MANIFEST), "repaired_manifest_sha256": sha(MANIFEST),
            "original_snapshot_prefix_sha256": sha(STAGE / "SnapshotGenerated.lean"),
            "prefix_bytes": len((STAGE / "SnapshotGenerated.lean").read_bytes()),
            "replacements": [{"before": a.decode(), "after": b.decode(), "count": 1} for a, b in pairs],
            "retained_successful_preflights": {name: sha(STAGE / (name + ".preflight.json")) for name in
                  [Path(m["statement"]).name, Path(m["solution"]).name, "SnapshotOriginal.lean"]},
            "Lean_started": False, "validated": False, "submission_ready": False}
    write_exact(PREP, (json.dumps(note, indent=2, ensure_ascii=False) + "\n").encode())
    return check()


def check():
    m, raw, failure, failed_log, pairs = source_bytes()
    need(NEW.read_bytes() == raw, "Repaired source differs from exact two-edits construction")
    doc = read(MANIFEST)
    need(doc["output"] == NEW.relative_to(ROOT).as_posix() and doc["output_sha256"] == sha(NEW)
         and doc["input_hashes"][rel(SELF)] == sha(SELF), "Repaired compiler manifest differs")
    runner.verify_manifest_inputs(doc)
    runner.verify_source_certificate(NEW, doc)
    need(runner.certified_imports(NEW, doc) == m["imports"], "Repaired import closure differs")
    note = read(PREP)
    need(note["repaired_manifest_sha256"] == sha(MANIFEST)
         and note["repaired_source_sha256"] == sha(NEW)
         and note["failed_preflight_sha256"] == sha(OLD_RECORD)
         and note["failed_log_sha256"] == sha(failed_log)
         and note["failed_manifest_sha256"] == sha(STAGE / "c4.json")
         and note["old_preparation_sha256"] == sha(STAGE / "preparation.json"),
         "Repair lineage changed")
    need(len(str(NEW.with_suffix(".lean.preflight.json").resolve())) < 240,
         "Repaired preflight path exceeds Windows budget")
    return {"prepared": True, "repaired_source": rel(NEW), "repaired_source_sha256": sha(NEW),
            "repaired_manifest": rel(MANIFEST), "repaired_manifest_sha256": sha(MANIFEST),
            "old_failed_source_preserved": True, "prior_three_runs_preserved": True,
            "Lean_started": False, "validated": False, "submission_ready": False}


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    mode = p.add_mutually_exclusive_group(required=True)
    mode.add_argument("--prepare", action="store_true")
    mode.add_argument("--check", action="store_true")
    a = p.parse_args()
    print(json.dumps(prepare() if a.prepare else check(), indent=2))
