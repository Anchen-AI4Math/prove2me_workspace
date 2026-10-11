"""Publish the reviewed phase payloads through the existing guarded transport.

The adapter only changes batch paths and the pure preparation gate in its own
Python process. The frozen numerator-PF publisher remains byte unchanged.
No API operation is allowed before a complete Root publication pin exists.
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import argparse
import hashlib
import msvcrt
from contextlib import contextmanager
from email import policy
from email.parser import BytesParser
import json
import re
import sys

import publish_numerator_pf_new_mission_2026_10_07 as transport

TASK = transport.TASK
BATCH = TASK / "formalization/platform/analytic-phase"
PREP = BATCH / "publication-preparation-2026-10-07"
OUT = BATCH / "publications-for-new-mission-2026-10-07"
PIN = BATCH / "Root-reviewed-publication-pin-v2-2026-10-07.json"
_ORIGINAL_TRANSACT = transport.transact
_REVIEWED = None


def phase_binding(row):
    """Hash task/package bindings and only the pinned intrinsic Lean directory."""
    keys = [key for key in ("task_relative", "root_relative", "absolute_path") if row.get(key)]
    assert len(keys) == 1, "Ambiguous or missing binding path"
    if keys[0] != "absolute_path":
        return transport.binding(row)
    original = Path(row["absolute_path"])
    assert original.is_absolute() and ".." not in original.parts
    path = original.resolve(strict=True)
    intrinsic = Path("C:/Users/anche/.elan/toolchains/leanprover--lean4---v4.33.1/lib/lean").resolve(strict=True)
    assert path.is_relative_to(intrinsic), "Absolute binding outside pinned intrinsic Lean directory"
    assert path.name.lower() not in {"credentials.json", ".env"}
    assert path.is_file() and path.stat().st_size == row["bytes"] and transport.sha(path) == row["sha256"]
    return path


def reviewed_wire(operation, endpoint, body, content_type, metadata):
    """Validate the complete outgoing bytes against snapshots held by prepare."""
    if _REVIEWED is None:
        raise RuntimeError("No complete publication preparation; no business POST")
    kind, name = metadata["kind"], metadata["name"]
    assert operation == kind + "_" + name and metadata["env"] == transport.ENV
    if kind == "definition":
        assert endpoint == "/submit-definition" and content_type == "application/json"
        assert json.loads(body) == _REVIEWED["definitions"][name]
    elif kind == "problem":
        assert endpoint == "/submit-problem" and content_type == "application/json"
        assert json.loads(body) == {"env": transport.ENV, "private": False,
                                    "problems": [_REVIEWED["problems"][name]]}
    else:
        assert kind == "proof" and endpoint == "/verify"
        assert content_type.startswith("multipart/form-data; boundary=")
        assert not any(x in metadata["theorem_id"] for x in transport.OLD)
        message = BytesParser(policy=policy.default).parsebytes(
            b"Content-Type: " + content_type.encode("ascii") + b"\r\nMIME-Version: 1.0\r\n\r\n" + body)
        assert message.is_multipart() and not message.defects
        parts = list(message.iter_parts())
        assert len(parts) == 4 and all(not part.defects for part in parts)
        assert all(not part.get_all("Content-Transfer-Encoding") for part in parts)
        assert all(len(part.get_all("Content-Disposition", [])) == 1 for part in parts)
        assert all(len(part.get_all("Content-Type", [])) <= 1 for part in parts)
        names = [part.get_param("name", header="content-disposition") for part in parts]
        assert len(set(names)) == 4 and set(names) == {"theorem_id", "proof_type", "explanation", "file"}
        values = {name: part.get_payload(decode=True) for name, part in zip(names, parts)}
        assert values["theorem_id"].decode("utf-8") == metadata["theorem_id"]
        assert values["proof_type"] == b"prove"
        assert values["explanation"].decode("utf-8") == _REVIEWED["explanations"][name]
        expected = _REVIEWED["solutions"][name]
        assert parts[names.index("file")].get_filename() == expected["filename"]
        assert values["file"] == expected["bytes"]
        assert metadata["solution_sha256"] == expected["sha256"]


def valid_receipt(value, endpoint, row):
    assert isinstance(value, dict)
    if endpoint == "/submit-problem":
        assert not value.get("errors") and len(value.get("jobs", [])) == 1
        identifier = value["jobs"][0].get("job_id")
        assert isinstance(identifier, str) and identifier and row.get("job_id") == identifier
    else:
        key = "submission_id" if endpoint == "/verify" else "job_id"
        identifier = value.get(key)
        assert isinstance(identifier, str) and identifier and row.get(key) == identifier


def batch_post_barrier():
    journal_path = OUT / "business-post-journal.json"
    if not journal_path.exists():
        return
    journal = transport.load(journal_path)
    assert journal["new_proposal_id"] == transport.NEW
    operations = [row["operation"] for row in journal["attempts"]]
    assert len(operations) == len(set(operations)), "Duplicate operation in journal"
    for row in journal["attempts"]:
        if row.get("receipt_saved") is not True:
            raise RuntimeError("Unresolved POST in this phase batch; reconcile documented remote history before ANY further business POST")
        assert row["old_mission_write"] is False
        wire = TASK / row["wire_body_task_relative"]
        expected = OUT / "wire" / (hashlib.sha256(row["operation"].encode("utf-8")).hexdigest()[:16] + ".body")
        assert wire.resolve() == expected.resolve()
        body = wire.read_bytes()
        assert len(body) == row["wire_body_bytes"] and hashlib.sha256(body).hexdigest() == row["wire_body_sha256"]
        reviewed_wire(row["operation"], row["endpoint"], body, row["content_type"], row)
        kind, name = row["kind"], row["name"]
        expected_name = name if kind == "definition" else transport.helpers.slug(name)
        receipt = BATCH / f"{kind}-receipts/{expected_name}.json"
        assert (TASK / row["receipt_task_relative"]).resolve() == receipt.resolve()
        if not receipt.is_file():
            raise RuntimeError("Saved receipt is missing; stop all business POSTs in this batch")
        valid_receipt(transport.load(receipt), row["endpoint"], row)
        if row.get("receipt_sha256"):
            assert transport.sha(receipt) == row["receipt_sha256"]


@contextmanager
def batch_writer_lock():
    """Windows releases this exclusive byte lock if the owner process exits."""
    OUT.mkdir(parents=True, exist_ok=True)
    with (OUT / "business-writer.lock").open("a+b") as handle:
        if handle.seek(0, 2) == 0:
            handle.write(b"\0")
            handle.flush()
        handle.seek(0)
        try:
            msvcrt.locking(handle.fileno(), msvcrt.LK_NBLCK, 1)
        except OSError:
            raise RuntimeError("Another phase batch writer is live; do not duplicate business POSTs") from None
        try:
            yield
        finally:
            handle.seek(0)
            msvcrt.locking(handle.fileno(), msvcrt.LK_UNLCK, 1)


def phase_transact(remote, operation, endpoint, body, content_type, receipt, metadata):
    if _REVIEWED is None or transport.sha(PIN) != _REVIEWED["pin_sha256"]:
        raise RuntimeError("Complete unchanged phase preparation is required; no business POST")
    with batch_writer_lock():
        batch_post_barrier()
        reviewed_wire(operation, endpoint, body, content_type, metadata)
        result = _ORIGINAL_TRANSACT(remote, operation, endpoint, body, content_type, receipt, metadata)
        journal_path = OUT / "business-post-journal.json"
        journal = transport.load(journal_path)
        row = next(row for row in journal["attempts"] if row["operation"] == operation)
        valid_receipt(result, endpoint, row)
        row["receipt_sha256"] = transport.sha(receipt)
        row["phase_complete_wire_binding_verified"] = True
        transport.save(journal_path, journal)
        return result


def prepare():
    global _REVIEWED
    if not PIN.is_file():
        raise RuntimeError("Awaiting complete Root phase publication pin; no API operation or credentials access")
    pin_sha256 = transport.sha(PIN)
    pin = transport.load(PIN)
    assert pin["new_proposal_id"] == transport.NEW and pin["environment"] == transport.ENV
    for key in ["Root_rehashed_all_platform_author_bindings", "Root_rehashed_all_platform_independent_bindings",
                "all_original_34_forall_types_verified", "all_seven_definition_types_and_whole_values_verified",
                "whole_function_rfl_verified", "all_reachable_helpers_Std3_and_full_values_verified",
                "independent_fresh_source_no_foreign_objects", "exact_seven_payloads_independently_compiled",
                "complete_source_reachability_verified", "native_independent_verified"]:
        assert pin[key] is True, key
    reports = []
    for key in ["platform_author_report", "platform_independent_report"]:
        path = phase_binding(pin[key])
        report = transport.load(path)
        assert report["verdict"] == "PASS"
        with ThreadPoolExecutor(max_workers=2) as pool:
            list(pool.map(phase_binding, report["stable_files"]))
        reports.append(report)
    for row in pin["publication_metadata_bindings"]:
        phase_binding(row)
    manifest = transport.load(PREP / "prepared-publication-v2.json")
    assert manifest["new_proposal_id"] == transport.NEW and manifest["environment"] == transport.ENV
    assert not manifest["proposal_mutation_permitted"] and not manifest["mission_link_permitted"]
    assert len(manifest["seven_payloads"]) == 7
    phase_binding(manifest["native_independent_report"])
    phase_binding(manifest["Root_native_full_rehash"])
    payload_bytes = {}
    for row in manifest["seven_payloads"]:
        a, b = phase_binding(row["staged_source"]), phase_binding(row["publication_source_copy"])
        data, copy = a.read_bytes(), b.read_bytes()
        assert data == copy and len(data) == row["staged_source"]["bytes"]
        assert hashlib.sha256(data).hexdigest() == row["staged_source"]["sha256"]
        payload_bytes[a.relative_to(BATCH / "staged").as_posix()] = data
    for row in manifest["metadata"]:
        phase_binding(row)
    definitions = transport.load(PREP / "definitions-request-v2.json")
    request = transport.load(PREP / "problems-request-v2.json")
    explanations = transport.load(PREP / "proof-explanations-v1.json")
    plan = transport.load(BATCH / "target-plan.json")
    assert len(definitions) == 1 and len(request["problems"]) == 3
    assert request["env"] == transport.ENV and request["private"] is False
    assert definitions[0]["definition_name"] == plan["definition"]
    assert definitions[0]["env"] == transport.ENV and definitions[0]["private"] is False
    assert definitions[0]["definition"].encode("utf-8") == payload_bytes[plan["local_definition"]]
    target_by_name = {r["theorem_name"]: r for r in plan["targets"]}
    assert set(target_by_name) == {
        "ZetaNine.AnalyticPhase.phase_strictAntiOn_right",
        "ZetaNine.AnalyticPhase.phase_global_lt_certified",
        "ZetaNine.AnalyticPhase.phase_global_upper_bound"}
    assert len({item["theorem_name"] for item in request["problems"]}) == 3
    assert {item["theorem_name"] for item in request["problems"]} == set(target_by_name)
    problems = []
    for item in request["problems"]:
        target = target_by_name[item["theorem_name"]]
        source = BATCH / "staged" / target["local_solution"]
        code = transport.helpers.without_lean_comments(payload_bytes[target["local_solution"]].decode("utf-8"))
        assert re.search(r"(?m)^theorem solution\b", code)
        assert not re.search(r"\b(sorry|admit|axiom|unsafe|native_decide)\b", code)
        assert "import Theorems." not in code
        reference = payload_bytes[target["local_reference"]].decode("utf-8")
        line_ending = "\r\n" if "\r\n" in reference else "\n"
        assert reference == item["preamble"] + line_ending * 2 + item["formal_statement"] + line_ending
        assert item["formal_statement"].startswith("theorem " + item["theorem_name"])
        assert item["formal_statement"].endswith(" := by sorry")
        assert target["exact_original_header"].replace("theorem " + item["theorem_name"].rsplit(".", 1)[1], "theorem " + item["theorem_name"], 1) + " := by sorry" == item["formal_statement"].replace("\r\n", "\n")
        problems.append({**item, "local_solution": target["local_solution"], "explanation": explanations[item["theorem_name"]]})
    assert transport.sha(PIN) == pin_sha256
    _REVIEWED = {"pin_sha256": pin_sha256, "definitions": {x["definition_name"]: x for x in definitions},
                 "problems": {x["theorem_name"]: {k: v for k, v in x.items() if k not in {"local_solution", "explanation"}} for x in problems},
                 "explanations": explanations, "solutions": {x["theorem_name"]: {"filename": Path(x["local_solution"]).name,
                     "bytes": payload_bytes[x["local_solution"]], "sha256": hashlib.sha256(payload_bytes[x["local_solution"]]).hexdigest()} for x in problems}}
    transport.save(OUT / "offline-gate.json", {"checked_at": datetime.now(timezone.utc).isoformat(),
        "Root_pin_sha256": transport.sha(PIN), "platform_author_bindings": len(reports[0]["stable_files"]),
        "platform_independent_bindings": len(reports[1]["stable_files"]), "seven_exact_payloads": True,
        "all_three_original_headers_exact": True, "Lean_calls": 0, "credentials_access": False})
    print("All phase publication inputs rehashed; no Lean calls", flush=True)
    return definitions, problems, plan


def audit(require_accepted=False):
    definitions, problems, _ = prepare()
    remote = transport.client()
    detail = transport.proposal(remote)
    referenced = {row["theorem_id"] for row in detail["items"]}
    rows = []
    for item in problems:
        name = item["theorem_name"]
        path = BATCH / f"proof-receipts/{transport.helpers.slug(name)}.json"
        if not path.exists():
            continue
        receipt = transport.load(path)
        verdict = remote.call("GET", "/verify?submission_id=" + receipt["submission_id"])
        transport.save(BATCH / f"proof-verdicts/{transport.helpers.slug(name)}.json", verdict)
        canonical = transport.published(remote, "problem", item)
        assert verdict["theorem_id"] == canonical["theorem_id"]
        rows.append({"theorem_name": name, "theorem_id": canonical["theorem_id"], "status": canonical["status"],
                    "proof_status": verdict["status"], "submission_id": receipt["submission_id"],
                    "referenced_by_new_proposal": canonical["theorem_id"] in referenced})
        print(name, verdict["status"], canonical["status"], flush=True)
    if require_accepted:
        assert len(rows) == 3 and all(r["proof_status"] == "ACCEPTED" and r["status"] == "Proved" for r in rows)
        for item in definitions:
            transport.published(remote, "definition", item)
        root = remote.call("GET", "/theorems/" + transport.ROOT_ID)
        transport.save(OUT / "root-current.json", root)
        assert root["status"] == "Open"
        transport.save(OUT / "publication-audit.json", {"checked_at": datetime.now(timezone.utc).isoformat(),
            "new_proposal_id": transport.NEW, "proposal_status": detail["status"], "proposal_visibility": detail["visibility"],
            "new_global_complete_phase_proofs": rows, "all_three_Accepted_public_Proved": True,
            "new_proposal_reference_count": len(referenced), "phase_proofs_not_referenced": sum(not r["referenced_by_new_proposal"] for r in rows),
            "mission_link_writes": 0, "old_mission_operations": 0, "whole_Z9_A_or_irrationality_proved": False, "Lean_calls": 0})


def install_transport_adapter():
    transport.PF = BATCH
    transport.OUT = OUT
    transport.prepare = prepare
    transport.transact = phase_transact


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=["prepare", "definitions", "problems", "poll-jobs", "verify", "poll-proofs", "audit"])
    mode = parser.parse_args().mode
    install_transport_adapter()
    try:
        if mode == "prepare": prepare()
        elif mode in {"definitions", "problems"}: transport.registration(mode)
        elif mode == "poll-jobs": transport.poll_jobs()
        elif mode == "verify": transport.verify()
        else: audit(mode == "audit")
    except RuntimeError as error:
        raise SystemExit(str(error)) from None
