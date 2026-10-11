#!/usr/bin/env python3
"""Offline prepare and at-most-once publication wrapper for normalizedLogWeights.

Preparation replays the frozen source/generated consumer in memory and compares
its serialized report bytes with the already stored certificate.  It does not
compile Lean or call the platform.  Explicit --advance reuses the audited
closed-definition publisher; --poll requires a previously recorded job intent
and can only GET that job and, on publication, its exact readback.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import sys
import tempfile
from typing import Any

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
V = TASK / "verification"
COMMIT = "adc7f1241b42e322a6451854ab7e4b4c146bf78a"
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"
API_ADAPTER = ROOT / "scripts/p2m_api.py"
MODULE = "OAI.NumberTheory.PiExponent.Approximation.SuccessiveApproximations"
PLATFORM_MODULE = "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_SuccessiveApproximations"
UNIT = MODULE + ":3411"
NAME = "OAI.PiExponent.normalizedLogWeights"
STEM = "Def_OAI_NumberTheory_PiExponent_Approximation_SuccessiveApproximations"
DEFINITION_NAME = STEM.removeprefix("Def_")
SOURCE = V / "ap3/s/Definitions" / (STEM + ".lean")
MANIFEST = SOURCE.with_suffix(".manifest.json")
METADATA_PATH = SOURCE.with_suffix(".metadata.json")
PROBES = V / "ap3/s/probes"
VALIDATION = PROBES / "provider-validation.json"
OWNER = PROBES / "source-owner.json"
STAGE_MANIFEST = V / "ap3/stage-manifest.json"
PUBLICATION = V / "ap3/publication" / STEM
MAX_SECONDS = 300
SCHEMA_ADAPTER_SHA = 'bb75b1315df40a8b4468b39134768fd52314488b886a7ebaa5eb5c0795cdddb2'
CLOSED_API_SHA = '4b525b2dc18f5f2bdbaba57eab1089ab4a6308644c625343df1e0d2444065d38'


def sha_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha(path: Path) -> str:
    return sha_bytes(path.read_bytes())


def read(path: Path) -> Any:
    if not path.is_file():
        raise ValueError(f"Required publication evidence is absent: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def write_json_lf(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes((json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode("utf-8"))


def task_path(relative: str, label: str) -> Path:
    path = (TASK / relative).resolve()
    if not path.is_relative_to(TASK.resolve()) or not path.is_file():
        raise ValueError(f"{label} is absent or escapes the task: {relative}")
    return path


def workspace_path(relative: str, label: str) -> Path:
    path = (ROOT / relative).resolve()
    if not path.is_relative_to(ROOT.resolve()) or not path.is_file():
        raise ValueError(f"{label} is absent or escapes the workspace: {relative}")
    return path


def verify_exact_single_ci(manifest: dict[str, Any], owner: dict[str, Any]) -> None:
    require = lambda ok, msg: (_ for _ in ()).throw(ValueError(msg)) if not ok else None
    require(manifest.get("source_module") == MODULE, "Provider source module differs")
    require(manifest.get("platform_module") == PLATFORM_MODULE, "Provider target module differs")
    require(manifest.get("source_commit") == COMMIT, "Provider source commit differs")
    require(manifest.get("selected_units") == [UNIT], "Provider must contain exactly the one unit 3411")
    require(owner.get("source_name") == NAME and owner.get("command_unit") == UNIT
            and owner.get("source_module") == MODULE and owner.get("graph_kind") == "def"
            and owner.get("owner_kind") == "definition" and owner.get("source_private") is False,
            "Authenticated owner is not the exact public normalizedLogWeights Definition")
    require(owner.get("source_line_range") is None or isinstance(owner.get("source_line_range"), dict),
            "Owner source range has an unexpected representation")
    require(manifest.get("imports") == sorted(set(manifest.get("imports", []))),
            "Definition bundle imports are not canonical")
    require(not any(name.startswith(("OAI.", "Definitions.", "Theorems.", "Solutions."))
                    for name in manifest.get("imports", [])),
            "Definition bundle unexpectedly imports a project/platform module")
    require(manifest.get("renames") == [] and manifest.get("elaboration_only_helpers") == []
            and manifest.get("kept_local_instances") == [],
            "Definition bundle contains unsupported renames/helpers/instances")


def replay_consumer_readonly() -> tuple[dict[str, Any], str]:
    """Replay complete evidence validation, capturing its report write in memory."""
    sys.path.insert(0, str(TASK / "scripts"))
    import validate_normalized_weights_provider as consumer
    import normalized_weights_consumer_adapter as adapter
    if sha(Path(adapter.__file__)) != SCHEMA_ADAPTER_SHA:
        raise ValueError('Frozen single-CI schema adapter changed')

    before = VALIDATION.read_bytes()
    before_sha = sha_bytes(before)
    captured: dict[str, Any] = {}
    original_write = consumer.write
    original_generator_dest = consumer.base_generator.DEST
    original_generate = consumer.base_generator.Generator.generate

    def capture(path: Path, value: Any) -> None:
        if Path(path).resolve() != VALIDATION.resolve() or "report" in captured:
            raise ValueError("Readonly consumer replay attempted an unexpected or duplicate write")
        captured["report"] = value

    scratch_parent = (TASK / ".pe").resolve()
    if not scratch_parent.is_relative_to(TASK.resolve()):
        raise ValueError('Private replay scratch escapes task')
    scratch_parent.mkdir(parents=True, exist_ok=True)
    consumer.write = capture
    try:
        # consumer.validate() reconstructs via the frozen base Generator. Route
        # that generator's default output into private scratch so replay cannot
        # rewrite verification/bundles-preview or any accepted/public stage.
        with tempfile.TemporaryDirectory(prefix="nw-pub-replay-", dir=scratch_parent) as scratch:
            target = Path(scratch).resolve()
            if not target.is_relative_to(scratch_parent):
                raise ValueError('Resolved replay scratch escapes task')
            def generate_in_scratch(generator, module):
                prior = consumer.base_generator.DEST
                consumer.base_generator.DEST = target
                try:
                    return original_generate(generator, module)
                finally:
                    consumer.base_generator.DEST = prior
            consumer.base_generator.Generator.generate = generate_in_scratch
            with adapter.installed():
                result = consumer.validate()
    finally:
        consumer.write = original_write
        consumer.base_generator.DEST = original_generator_dest
        consumer.base_generator.Generator.generate = original_generate
    if "report" not in captured:
        raise ValueError("Consumer replay did not produce its validation report")
    value = captured["report"]
    expected_lf = (json.dumps(value, indent=2, ensure_ascii=False) + "\n").encode("utf-8")
    expected_crlf = expected_lf.replace(b"\n", b"\r\n")
    after = VALIDATION.read_bytes()
    if after != before or sha_bytes(after) != before_sha:
        raise ValueError("Stored validation report changed during readonly replay")
    if after not in (expected_lf, expected_crlf):
        raise ValueError("Stored validation report bytes differ from fresh consumer replay")
    if result.get("report_sha256") != before_sha:
        raise ValueError("Consumer result does not pin the stored report bytes")
    return value, before_sha


def verify_no_sorry(source_bytes: bytes) -> None:
    # Fail closed on either active Lean syntax or a `sorry` token in uploaded bytes.
    if re.search(rb"\bsorry\b", source_bytes):
        raise ValueError("Public Definition source contains a sorry token")


def prepare() -> tuple[Path, dict[str, Any], dict[str, Any], dict[str, Any]]:
    source_bytes = SOURCE.read_bytes()
    source = source_bytes.decode("utf-8")
    if source.encode("utf-8") != source_bytes:
        raise ValueError("Definition source does not round-trip as exact UTF-8")
    verify_no_sorry(source_bytes)
    manifest = read(MANIFEST)
    metadata_raw = METADATA_PATH.read_bytes()
    metadata = json.loads(metadata_raw.decode("utf-8"))
    owner = read(OWNER)
    verify_exact_single_ci(manifest, owner)

    if (manifest.get("output") != SOURCE.relative_to(ROOT).as_posix()
            or manifest.get("output_sha256") != sha_bytes(source_bytes)
            or manifest.get("provisional") is not True
            or manifest.get("validated") is not False
            or manifest.get("submission_ready") is not False
            or manifest.get("source_skeleton_preserved") is not True
            or manifest.get("full_definition_proofs_preserved") is not True
            or manifest.get("independent_byte_reconstruction_equal") is not True
            or manifest.get("source_unchanged") is not True
            or manifest.get("source_commit") != COMMIT):
        raise ValueError("Definition manifest lineage, preview, or source identity differs")
    original = workspace_path(manifest["source"], "ported source")
    original_raw = original.read_bytes()
    if sha_bytes(original_raw) != manifest.get("source_sha256"):
        raise ValueError("Ported source hash differs from the exact provider manifest")
    original_lines = original_raw.decode("utf-8").splitlines()
    if (len(original_lines) < 76
            or not original_lines[73].strip().startswith("noncomputable def normalizedLogWeights (q : ℕ → ℕ)")
            or original_lines[74].strip() != "| 0 => 1"
            or original_lines[75].strip() != "| n + 1 => (Nat.ceil (Real.log (q n)) : ℝ)"):
        raise ValueError("Pinned source commit's cited lines 74-76 do not contain this exact Definition")
    for relative, expected in manifest.get("input_hashes", {}).items():
        path = task_path(relative, "provider generation input")
        if sha(path) != expected:
            raise ValueError("Provider generation input changed: " + relative)
    # Reconstruct the exact generated UTF-8 source bytes from the manifest edit ledger.
    from span_edits import Edit, apply_edits
    edits = manifest.get("edits")
    if not isinstance(edits, list):
        raise ValueError("Provider manifest has no byte-edit reconstruction ledger")
    parsed = []
    for row in edits:
        if (not isinstance(row, dict) or set(row) != {"start", "end", "reason", "replacement"}
                or not isinstance(row["start"], int) or not isinstance(row["end"], int)
                or not isinstance(row["replacement"], str)):
            raise ValueError("Provider edit ledger has an invalid row")
        parsed.append(Edit(row["start"], row["end"], row["replacement"].encode("utf-8"), row["reason"]))
    if apply_edits(original_raw, parsed, manifest["source_sha256"]) != source_bytes:
        raise ValueError("Definition provider is not the exact manifest-edit reconstruction")

    expected_meta_keys = {"theorem_title", "natural_language_statement", "explanation", "tags",
                          "source_commit", "source_url"}
    if set(metadata) != expected_meta_keys:
        raise ValueError("Academic metadata keys differ from the expected exact single-CI schema")
    expected_url = ("https://github.com/openai/math/blob/" + COMMIT
                    + "/lean/OAI/NumberTheory/PiExponent/Approximation/SuccessiveApproximations.lean#L74-L76")
    if (metadata.get("source_commit") != COMMIT or metadata.get("source_url") != expected_url
            or not metadata.get("theorem_title") or not metadata.get("natural_language_statement")
            or not metadata.get("explanation") or metadata.get("tags") !=
            ["openai-pi-exponent-017", "number-theory", "definition"]):
        raise ValueError("Definition metadata has an incorrect source citation, title, text, or tags")
    if ("asserts no existence" not in metadata["natural_language_statement"]
            or "no positivity condition" not in metadata["natural_language_statement"]):
        raise ValueError("Metadata does not explicitly delimit this definition from positivity/existence claims")

    # Require the prior consumer's stored proof certificate and replay it without
    # allowing its report writer to alter the frozen record.
    validation, validation_sha = replay_consumer_readonly()
    if (validation.get("validated") is not True or validation.get("source_name") != NAME
            or validation.get("source_module") != MODULE
            or validation.get("generated_module") != PLATFORM_MODULE
            or validation.get("exact_public_name") is not True
            or validation.get("kernel_type_equal") is not True
            or validation.get("complete_definition_value_equal") is not True
            or validation.get("axioms_equal_and_std3") is not True
            or validation.get("actual_module_owners_checked") is not True
            or validation.get("source174_certificate_used") is not False):
        raise ValueError("Fresh consumer replay is not a complete exact-Definition certificate")
    if (validation_sha != sha(VALIDATION)
            or validation.get("provider_preflight", {}).get("mode") != "emit-olean"
            or validation.get("provider_preflight", {}).get("actual_module_identity") != PLATFORM_MODULE
            or validation.get("source_probe_preflight", {}).get("actual_module_identity") != "SourceStructural"
            or validation.get("generated_probe_preflight", {}).get("actual_module_identity") != "GeneratedStructural"):
        raise ValueError("Consumer preflight identities or validation hash differ")
    for key in ("provider_preflight", "source_probe_preflight", "generated_probe_preflight"):
        evidence = validation[key]
        if not 0 < evidence.get("seconds", 0) <= MAX_SECONDS:
            raise ValueError("One of the three strict preflights exceeds the task budget")

    payload = {
        "definition_name": DEFINITION_NAME,
        "definition_title": metadata["theorem_title"],
        "definition": source,
        "natural_language_statement": metadata["natural_language_statement"],
        "source": metadata["source_url"],
        "tags": metadata["tags"],
        "env": ENV,
        "private": False,
    }
    payload_bytes = json.dumps(payload, ensure_ascii=False).encode("utf-8")
    if payload["definition"].encode("utf-8") != source_bytes:
        raise ValueError("Wire definition bytes differ from the exact staged UTF-8 source")

    consumer_script = TASK / "scripts/validate_normalized_weights_provider.py"
    prep = {
        "schema_version": 1,
        "prepared_at_utc": datetime.now(timezone.utc).isoformat(),
        "offline_prepare_only": True,
        "proposal_status": "Draft",
        "publisher_script_sha256": sha(Path(__file__).resolve()),
        "consumer_script_sha256": sha(consumer_script),
        "api_adapter_sha256": sha(API_ADAPTER),
        "definition_name": DEFINITION_NAME,
        "definition_module": PLATFORM_MODULE,
        "source_module": MODULE,
        "source_command_unit": UNIT,
        "environment": ENV,
        "visibility": "public",
        "source_commit": COMMIT,
        "metadata_sha256": sha_bytes(metadata_raw),
        "payload_sha256": sha_bytes(payload_bytes),
        "wire_body_sha256": sha_bytes(payload_bytes),
        "bundle_source_sha256": sha_bytes(source_bytes),
        "uploaded_definition_sha256": sha_bytes(payload["definition"].encode("utf-8")),
        "uploaded_definition_bytes": len(source_bytes),
        "definition_bytes_equal_bundle_source": True,
        "bundle_manifest_sha256": sha(MANIFEST),
        "stage_manifest_sha256": sha(STAGE_MANIFEST),
        "validation_sha256": validation_sha,
        "source_owner_witness_sha256": sha(OWNER),
        "source174_certificate_used": False,
        "preflight_count": 3,
        "max_preflight_seconds": max(validation[key]["seconds"] for key in
                                      ("provider_preflight", "source_probe_preflight", "generated_probe_preflight")),
        "provider_olean_sha256": validation["provider_preflight"]["output_olean_sha256"],
        "source_row_sha256": validation["source_row_sha256"],
        "generated_row_sha256": validation["generated_row_sha256"],
        "artifact_pins": {
            "bundle_source_sha256": sha_bytes(source_bytes),
            "bundle_manifest_sha256": sha(MANIFEST),
            "academic_metadata_sha256": sha_bytes(metadata_raw),
            "validation_certificate_sha256": validation_sha,
            "source_owner_witness_sha256": sha(OWNER),
            "stage_manifest_sha256": sha(STAGE_MANIFEST),
            "consumer_script_sha256": sha(consumer_script),
            "publisher_script_sha256": sha(Path(__file__).resolve()),
            "api_adapter_sha256": sha(API_ADAPTER),
        },
        "kernel_type_value_and_std3_comparison": {
            "kernel_type_equal": True, "complete_definition_value_equal": True,
            "axioms_equal_and_std3": True, "actual_module_owners_checked": True,
        },
    }
    if PUBLICATION.exists():
        old_record = PUBLICATION / "publication.json"
        if old_record.is_file():
            previous = read(old_record)
            if ((previous.get("publish_intent") or previous.get("definition_id")
                 or previous.get("publish_payload_sha256"))
                    and previous.get("publish_payload_sha256") != prep["payload_sha256"]):
                raise ValueError("Recorded publication intent is immutable; refusing a changed wire payload")
        old_prep = PUBLICATION / "prepare-record.json"
        if old_prep.is_file() and read(old_prep).get("publisher_script_sha256") != prep["publisher_script_sha256"]:
            raise ValueError("Prepared publisher bytes changed; refusing to rewrite the recorded preparation")
    PUBLICATION.mkdir(parents=True, exist_ok=True)
    # Pin the exact academic-metadata bytes as staged; payload carries only the
    # platform fields needed for this one public Definition.
    (PUBLICATION / "metadata.json").write_bytes(metadata_raw)
    (PUBLICATION / "publish-payload.json").write_bytes(payload_bytes)
    write_json_lf(PUBLICATION / "prepare-record.json", prep)
    return PUBLICATION, metadata, payload, prep


def load_prepared() -> tuple[Path, dict[str, Any], dict[str, Any], dict[str, Any]]:
    stage_dir = PUBLICATION
    prep = read(stage_dir / "prepare-record.json")
    metadata = read(stage_dir / "metadata.json")
    payload_raw = (stage_dir / "publish-payload.json").read_bytes()
    payload = json.loads(payload_raw.decode("utf-8"))
    require = lambda ok, msg: (_ for _ in ()).throw(ValueError(msg)) if not ok else None
    require(sha(Path(__file__).resolve()) == prep.get("publisher_script_sha256"),
            "Publisher script differs from the preparation pin")
    require(sha(TASK / "scripts/validate_normalized_weights_provider.py") == prep.get("consumer_script_sha256"),
            "Frozen consumer differs from the preparation pin")
    require(sha(API_ADAPTER) == prep.get("api_adapter_sha256"),
            "Platform API adapter differs from the preparation pin")
    require(sha(stage_dir / "metadata.json") == prep.get("metadata_sha256"),
            "Prepared metadata bytes differ")
    require(sha_bytes(payload_raw) == prep.get("wire_body_sha256") == prep.get("payload_sha256"),
            "Prepared wire payload bytes differ")
    require(payload.get("definition_name") == DEFINITION_NAME
            and payload.get("definition") is not None
            and sha_bytes(payload["definition"].encode("utf-8")) == prep.get("uploaded_definition_sha256")
            and payload.get("env") == ENV and payload.get("private") is False,
            "Prepared payload identity/environment/body differs")
    require(prep.get("bundle_source_sha256") == prep.get("uploaded_definition_sha256")
            and prep.get("source_commit") == COMMIT and prep.get("proposal_status") == "Draft",
            "Prepared source lineage or proposal state differs")
    pins = prep.get("artifact_pins")
    expected_pins = {
        "bundle_source_sha256": sha(SOURCE),
        "bundle_manifest_sha256": sha(MANIFEST),
        "academic_metadata_sha256": sha(TASK / "verification/ap3/s/Definitions" / (STEM + ".metadata.json")),
        "validation_certificate_sha256": sha(VALIDATION),
        "source_owner_witness_sha256": sha(OWNER),
        "stage_manifest_sha256": sha(STAGE_MANIFEST),
        "consumer_script_sha256": sha(TASK / "scripts/validate_normalized_weights_provider.py"),
        "publisher_script_sha256": sha(Path(__file__).resolve()),
        "api_adapter_sha256": sha(API_ADAPTER),
    }
    require(pins == expected_pins, "Current source/certificate/publisher/API pins differ from preparation")
    return stage_dir, metadata, payload, prep


def advance_or_poll(mode: str) -> dict[str, Any]:
    stage_dir, metadata, payload, prep = load_prepared()
    record_path = stage_dir / "publication.json"
    pins = prep["artifact_pins"]
    if record_path.exists():
        record_before = read(record_path)
        if record_before.get("preparation_pins") != pins:
            raise ValueError("Existing publication record has different preparation/certificate/API pins")
    else:
        if mode == "poll":
            raise ValueError("--poll requires a previously recorded publication intent/job")
        write_json_lf(record_path, {"definition_name": payload["definition_name"],
                                    "environment": ENV, "visibility": "public",
                                    "publish_payload_sha256": prep["payload_sha256"],
                                    "preparation_pins": pins})
    if mode == "poll":
        if not record_path.is_file():
            raise ValueError("--poll requires an already recorded publication intent/job")
        record = read(record_path)
        intent = record.get("publish_intent")
        if (not isinstance(intent, dict) or not record.get("job_id")
                or record.get("definition_id")
                or record.get("publish_payload_sha256") != prep["payload_sha256"]
                or record.get("preparation_pins") != pins
                or intent.get("payload_sha256") != prep["payload_sha256"]
                or intent.get("definition_name") != payload["definition_name"]
                or intent.get("environment") != ENV or intent.get("visibility") != "public"
                or intent.get("payload") != payload):
            raise ValueError("--poll is GET-only and requires a matching immutable existing job intent")
    sys.path.insert(0, str(TASK / "scripts"))
    import publish_closed_definition_bundle as closed
    if sha(Path(closed.__file__)) != CLOSED_API_SHA:
        raise ValueError('Frozen at-most-once API publisher changed')
    # This call is reachable only under explicit --advance or validated --poll.
    # In --poll the preconditions force advance() directly into its known-job GET path.
    return closed.advance(stage_dir, metadata, payload, prep)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--prepare-only", action="store_true")
    modes.add_argument("--advance", action="store_true",
                       help="Run the audited duplicate-check GETs and at most one POST")
    modes.add_argument("--poll", action="store_true",
                       help="GET only the already recorded job; never create an intent or POST")
    args = parser.parse_args()
    if args.prepare_only:
        stage, _, payload, prep = prepare()
        print(json.dumps({"prepared_offline": True, "stage": stage.relative_to(TASK).as_posix(),
                          "definition_name": payload["definition_name"],
                          "payload_sha256": prep["payload_sha256"],
                          "validated": True, "api_used": False}, ensure_ascii=False))
        return 0
    result = advance_or_poll("poll" if args.poll else "advance")
    print(json.dumps({"advanced": args.advance, "polled_existing_job": args.poll,
                      "definition_name": DEFINITION_NAME, "job_id": result.get("job_id"),
                      "definition_id": result.get("definition_id"),
                      "status": result.get("last_publish_verdict", {}).get("body", {}).get("status")},
                     ensure_ascii=False))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, KeyError, ValueError, TypeError, json.JSONDecodeError) as exc:
        print("normalizedLogWeights publisher refused to proceed: " + str(exc), file=sys.stderr)
        raise SystemExit(2)
