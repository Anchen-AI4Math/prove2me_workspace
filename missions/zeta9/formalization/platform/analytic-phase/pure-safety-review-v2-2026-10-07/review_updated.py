"""Offline regression of Phase wrappers using fabricated pins and fake POSTs.

Actual publication metadata is read, never changed. All writes and locking are
confined to own fixture tree. Publisher modules are never imported or started.
"""
import ast
import base64
from concurrent.futures import ThreadPoolExecutor
from contextlib import contextmanager
from datetime import datetime, timezone
from email import policy
from email.parser import BytesParser
import hashlib
import json
import msvcrt
from pathlib import Path
import re
import subprocess
import sys
import threading
from types import SimpleNamespace
import uuid

from review_fixture import HERE, TASK, SCRIPTS, PF_NAME, PHASE_NAME, digest, extract, fixture, pure_save

PY312 = Path("C:/Users/anche/AppData/Local/Programs/Python/Python312/python.exe")
FUNCTIONS = ["reviewed_wire", "valid_receipt", "batch_post_barrier", "batch_writer_lock", "phase_transact"]


def actual_inputs():
    batch = TASK / "formalization/platform/analytic-phase"
    prep = batch / "publication-preparation-2026-10-07"
    definitions = json.loads((prep / "definitions-request-v1.json").read_text(encoding="utf-8"))
    problems = json.loads((prep / "problems-request-v1.json").read_text(encoding="utf-8"))["problems"]
    explanations = json.loads((prep / "proof-explanations-v1.json").read_text(encoding="utf-8"))
    plan = json.loads((batch / "target-plan.json").read_text(encoding="utf-8"))
    solutions = {}
    targets = {t["theorem_name"]: t for t in plan["targets"]}
    for item in problems:
        source = batch / "staged" / targets[item["theorem_name"]]["local_solution"]
        b = source.read_bytes()
        solutions[item["theorem_name"]] = {"filename": source.name, "bytes": b, "sha256": digest(b)}
    return definitions, problems, explanations, solutions, plan


def new_case(pf_source, phase_source, case):
    base, ns = fixture(pf_source, "updated-" + case)
    definitions, problems, explanations, solutions, plan = actual_inputs()
    helpers = SimpleNamespace(slug=lambda name: re.sub(r"[^A-Za-z0-9._-]", "_", name))
    transport = SimpleNamespace(load=ns["load"], save=ns["save"], sha=ns["sha"], NEW=ns["NEW"],
                                ENV=problems and definitions[0]["env"], OLD={"old-fixture-mission", "old-fixture-proposal"}, helpers=helpers)
    pin = base / "FAKE-PIN-NOT-AUTHORIZATION.json"
    pure_save(pin, {"fake": True, "no_platform_permission": True})
    ns.update({"transport": transport, "BATCH": ns["PF"], "PIN": pin, "_ORIGINAL_TRANSACT": ns["transact"],
               "_REVIEWED": {"pin_sha256": digest(pin.read_bytes()),
                             "definitions": {x["definition_name"]: x for x in definitions},
                             "problems": {x["theorem_name"]: x for x in problems}, "explanations": explanations, "solutions": solutions},
               "contextmanager": contextmanager, "msvcrt": msvcrt, "BytesParser": BytesParser, "policy": policy})
    ns["ENV"] = transport.ENV
    extract(phase_source, FUNCTIONS, ns)
    return base, ns, definitions, problems, explanations, solutions, plan


def operation(ns, kind, item, proof_bytes=None, content_transfer_encoding=None):
    name = item["definition_name" if kind == "definition" else "theorem_name"]
    metadata = {"kind": kind, "name": name, "env": ns["transport"].ENV}
    path_name = name if kind == "definition" else ns["transport"].helpers.slug(name)
    receipt = ns["BATCH"] / f"{kind}-receipts/{path_name}.json"
    if kind == "definition":
        return kind + "_" + name, "/submit-definition", json.dumps(item, ensure_ascii=False).encode(), "application/json", receipt, metadata
    if kind == "problem":
        payload = {"env": ns["transport"].ENV, "private": False, "problems": [item]}
        return kind + "_" + name, "/submit-problem", json.dumps(payload, ensure_ascii=False).encode(), "application/json", receipt, metadata
    identifier = "fake-canonical-" + name.rsplit(".", 1)[-1]
    expected = ns["_REVIEWED"]["solutions"][name]
    metadata.update({"theorem_id": identifier, "solution_sha256": expected["sha256"]})
    boundary = "offlinefixture" + uuid.uuid4().hex
    chunks = []
    for field, value in {"theorem_id": identifier, "proof_type": "prove", "explanation": ns["_REVIEWED"]["explanations"][name]}.items():
        chunks.append(f'--{boundary}\r\nContent-Disposition: form-data; name="{field}"\r\n\r\n{value}\r\n'.encode())
    extra = "" if content_transfer_encoding is None else "Content-Transfer-Encoding: " + content_transfer_encoding + "\r\n"
    chunks.append(f'--{boundary}\r\nContent-Disposition: form-data; name="file"; filename="{expected["filename"]}"\r\nContent-Type: text/plain; charset=utf-8\r\n{extra}\r\n'.encode())
    chunks.append(expected["bytes"] if proof_bytes is None else proof_bytes)
    chunks.append(f"\r\n--{boundary}--\r\n".encode())
    return kind + "_" + name, "/verify", b"".join(chunks), "multipart/form-data; boundary=" + boundary, receipt, metadata


class FakeRemote:
    def __init__(self, ns, uncertain=False, invalid=False, entered=None, release=None):
        self.ns, self.calls = ns, []
        self.uncertain, self.invalid = uncertain, invalid
        self.entered, self.release = entered, release

    def post_public(self, endpoint, body, content_type):
        journal = self.ns["transport"].load(self.ns["OUT"] / "business-post-journal.json")
        row = journal["attempts"][-1]
        assert row["receipt_saved"] is False
        assert (self.ns["TASK"] / row["wire_body_task_relative"]).read_bytes() == body
        self.calls.append({"endpoint": endpoint, "operation": row["operation"], "wire_sha256": digest(body), "WAL_and_wire_first": True})
        if self.entered is not None:
            self.entered.set()
            assert self.release.wait(timeout=15)
        if self.uncertain:
            raise RuntimeError("FAKE outcome uncertain")
        if self.invalid:
            return {"unexpected": "FAKE invalid receipt"}
        identifier = "fake-id-" + str(len(self.calls))
        if endpoint == "/submit-problem":
            return {"jobs": [{"job_id": identifier}], "errors": []}
        return {"submission_id" if endpoint == "/verify" else "job_id": identifier}


def blocked(fn):
    try:
        fn()
    except (RuntimeError, AssertionError, KeyError) as error:
        return {"exception": type(error).__name__, "message": str(error)}
    raise AssertionError("Expected to reject before any fake POST")


def run(pf_source, phase_source, snapshot):
    results = {}
    base, ns, defs, probs, _, solutions, _ = new_case(pf_source, phase_source, "normal-seven")
    remote = FakeRemote(ns)
    args = [operation(ns, "definition", defs[0])] + [operation(ns, "problem", x) for x in probs] + [operation(ns, "proof", x) for x in probs]
    receipts = [ns["phase_transact"](remote, *a) for a in args]
    assert len(remote.calls) == 7
    # Fresh multipart boundaries on resume must preserve semantics without another POST.
    resume = [operation(ns, "definition", defs[0])] + [operation(ns, "problem", x) for x in probs] + [operation(ns, "proof", x) for x in probs]
    resumed = [ns["phase_transact"](remote, *a) for a in resume]
    assert resumed == receipts and len(remote.calls) == 7
    journal_path = ns["OUT"] / "business-post-journal.json"
    journal = ns["transport"].load(journal_path)
    assert len(journal["attempts"]) == 7 and all(r["receipt_saved"] and r["receipt_sha256"] and r["phase_complete_wire_binding_verified"] for r in journal["attempts"])
    results["normal_seven_and_resume"] = {"fake_POSTs": remote.calls, "resume_additional_fake_POSTs": 0, "all_seven_receipt_hashes_and_wire_bindings": True}
    proof_receipt = args[-1][4]
    saved_receipt = proof_receipt.read_bytes()
    pure_save(proof_receipt, {"submission_id": "different-fake-id"})
    results["invalid_receipt_blocks"] = blocked(lambda: ns["phase_transact"](remote, *resume[0]))
    assert len(remote.calls) == 7
    proof_receipt.write_bytes(saved_receipt)
    saved_journal = journal_path.read_bytes()
    bad_journal = json.loads(saved_journal)
    bad_journal["attempts"].append(bad_journal["attempts"][0])
    pure_save(journal_path, bad_journal)
    results["duplicate_journal_blocks"] = blocked(lambda: ns["phase_transact"](remote, *resume[0]))
    assert len(remote.calls) == 7
    journal_path.write_bytes(saved_journal)
    row = journal["attempts"][0]
    wire = base / row["wire_body_task_relative"]
    saved_wire = wire.read_bytes()
    wire.write_bytes(b"FAKE changed wire")
    results["changed_saved_wire_blocks"] = blocked(lambda: ns["phase_transact"](remote, *resume[0]))
    assert len(remote.calls) == 7
    wire.write_bytes(saved_wire)
    ns["PIN"].write_bytes(b"changed fake pin")
    results["changed_PIN_blocks"] = blocked(lambda: ns["phase_transact"](remote, *resume[0]))
    assert len(remote.calls) == 7
    base, ns, defs, probs, _, _, _ = new_case(pf_source, phase_source, "unknown-barrier")
    remote = FakeRemote(ns, uncertain=True)
    first = operation(ns, "definition", defs[0])
    results["first_unknown"] = blocked(lambda: ns["phase_transact"](remote, *first))
    results["unknown_same_operation_blocks"] = blocked(lambda: ns["phase_transact"](remote, *first))
    results["unknown_other_operation_blocks"] = blocked(lambda: ns["phase_transact"](remote, *operation(ns, "proof", probs[0])))
    assert len(remote.calls) == 1
    results["unknown_fake_POST_count"] = 1
    base, ns, defs, probs, _, _, _ = new_case(pf_source, phase_source, "invalid-first-response")
    remote = FakeRemote(ns, invalid=True)
    results["invalid_response_first"] = blocked(lambda: ns["phase_transact"](remote, *operation(ns, "definition", defs[0])))
    results["invalid_response_all_other_POSTs_block"] = blocked(lambda: ns["phase_transact"](remote, *operation(ns, "problem", probs[0])))
    assert len(remote.calls) == 1
    results["invalid_response_fake_POST_count"] = 1
    base, ns, defs, probs, _, _, _ = new_case(pf_source, phase_source, "concurrent-exclusive")
    entered, release = threading.Event(), threading.Event()
    remote = FakeRemote(ns, entered=entered, release=release)
    first = operation(ns, "definition", defs[0])
    with ThreadPoolExecutor(max_workers=1) as pool:
        handle = pool.submit(ns["phase_transact"], remote, *first)
        assert entered.wait(timeout=10)
        try:
            results["concurrent_second_writer_blocks"] = blocked(lambda: ns["phase_transact"](remote, *first))
        finally:
            release.set()
        handle.result(timeout=20)
    ns["phase_transact"](remote, *first)
    assert len(remote.calls) == 1
    results["concurrent_same_operation_fake_POST_count"] = 1
    with ns["batch_writer_lock"]():
        denied = subprocess.run([str(PY312), str(Path(__file__).resolve()), "--child-lock", str(ns["OUT"]), str(snapshot)], capture_output=True, text=True, timeout=15)
    allowed = subprocess.run([str(PY312), str(Path(__file__).resolve()), "--child-lock", str(ns["OUT"]), str(snapshot)], capture_output=True, text=True, timeout=15)
    assert denied.returncode == allowed.returncode == 0
    assert json.loads(denied.stdout)["lock_acquired"] is False and json.loads(allowed.stdout)["lock_acquired"] is True
    results["cross_process_exclusive_lock"] = {"held_parent_child": json.loads(denied.stdout), "released_parent_child": json.loads(allowed.stdout)}
    base, ns, defs, probs, _, solutions, _ = new_case(pf_source, phase_source, "proof-wire-binding")
    remote = FakeRemote(ns)
    changed = operation(ns, "proof", probs[0], proof_bytes=b"FAKE unreviewed replacement")
    results["changed_file_bytes_before_POST_blocks"] = blocked(lambda: ns["phase_transact"](remote, *changed))
    assert len(remote.calls) == 0
    changed_definition = {**defs[0], "definition": "FAKE unreviewed Definition"}
    results["changed_definition_before_POST_blocks"] = blocked(lambda: ns["phase_transact"](remote, *operation(ns, "definition", changed_definition)))
    changed_problem = {**probs[0], "formal_statement": "FAKE unreviewed formal statement"}
    results["changed_problem_before_POST_blocks"] = blocked(lambda: ns["phase_transact"](remote, *operation(ns, "problem", changed_problem)))
    assert len(remote.calls) == 0
    # Distinguish MIME-decoded data from the literal bytes an HTTP upload carries.
    expected = solutions[probs[0]["theorem_name"]]["bytes"]
    encoded = operation(ns, "proof", probs[0], proof_bytes=base64.b64encode(expected), content_transfer_encoding="base64")
    try:
        ns["reviewed_wire"](encoded[0], encoded[1], encoded[2], encoded[3], encoded[5])
    except (RuntimeError, AssertionError, KeyError) as error:
        results["MIME_transfer_encoding"] = {"rejected": True, "exception": type(error).__name__}
    else:
        results["MIME_transfer_encoding"] = {"rejected": False, "literal_file_bytes_differ": True,
                                             "expected_file_sha256": digest(expected), "literal_wire_file_sha256": digest(base64.b64encode(expected)),
                                             "fake_or_actual_POSTs_for_this_probe": 0}
    return results


def child_lock(out, snapshot):
    out, snapshot = Path(out).resolve(), Path(snapshot).resolve()
    assert out.is_relative_to(HERE.resolve()) and snapshot.is_relative_to(HERE.resolve())
    ns = {"OUT": out, "contextmanager": contextmanager, "msvcrt": msvcrt}
    extract(snapshot.read_text(encoding="utf-8"), ["batch_writer_lock"], ns)
    try:
        with ns["batch_writer_lock"]():
            result = {"lock_acquired": True}
    except RuntimeError as error:
        result = {"lock_acquired": False, "exception": str(error)}
    print(json.dumps(result))


def main():
    report = HERE / "updated-fixture-results.json"
    assert not report.exists()
    b = (SCRIPTS / PHASE_NAME).read_bytes()
    snapshot = HERE / "source-snapshots" / (digest(b) + "-" + PHASE_NAME)
    snapshot.write_bytes(b)
    pf = (SCRIPTS / PF_NAME).read_bytes()
    assert digest(pf) == "dda7b66a1dcc8b07d4f059aa026fdbcaee600d0d59ebef587dd87ada124f8ecb"
    result = {"checked_at": datetime.now(timezone.utc).isoformat(), "phase_SOURCE_sha256": digest(b), "frozen_PF_SOURCE_sha256": digest(pf),
              "scope": "Pure wrapper safety fixtures, hypothetical legitimate prepared-cache state; fabricated PINs give no authorization.",
              "checks": run(pf.decode(), b.decode(), snapshot), "Lean_calls": 0, "network_calls": 0, "credentials_reads": 0,
              "mathematical_independent_PASS_not_claimed": True}
    pure_save(report, result)
    print(json.dumps({"report": str(report), "sha256": digest(report.read_bytes()), "phase_SOURCE_sha256": digest(b),
                      "checks": len(result["checks"]), "MIME_transfer_encoding": result["checks"]["MIME_transfer_encoding"],
                      "Lean_calls": 0, "network_calls": 0, "credentials_reads": 0}, indent=2))


if __name__ == "__main__":
    if len(sys.argv) == 4 and sys.argv[1] == "--child-lock":
        child_lock(sys.argv[2], sys.argv[3])
    else:
        main()
