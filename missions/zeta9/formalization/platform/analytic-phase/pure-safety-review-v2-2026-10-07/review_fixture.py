"""Pure offline SOURCE review: AST-extracted functions, fixture files, fake remote.

Never imports publisher modules, reads credentials, runs Lean, or uses a network.
The original transport function bodies execute only against this directory.
"""
import ast
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import threading
import uuid

HERE = Path(__file__).resolve().parent
TASK = HERE.parents[3]
SCRIPTS = TASK / "scripts"
PF_NAME = "publish_numerator_pf_new_mission_2026_10_07.py"
PHASE_NAME = "publish_analytic_phase_new_mission_2026_10_07.py"
PREP_NAME = "prepare_analytic_phase_publication_2026_10_07.py"


def digest(b):
    return hashlib.sha256(b).hexdigest()


def pure_save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def extract(source, names, namespace):
    tree = ast.parse(source)
    nodes = [n for n in tree.body if isinstance(n, (ast.FunctionDef, ast.ClassDef)) and n.name in names]
    assert {n.name for n in nodes} == set(names)
    exec(compile(ast.Module(body=nodes, type_ignores=[]), "<AST-extracted-reviewed-SOURCE>", "exec"), namespace)
    return {n.name: [n.lineno, n.end_lineno] for n in nodes}


def fixture(source, name):
    base = HERE / "fixtures" / name
    assert not base.exists(), "Preserve prior fixture evidence"
    base.mkdir(parents=True)
    ns = {"hashlib": hashlib, "json": json, "datetime": datetime, "timezone": timezone,
          "TASK": base, "OUT": base / "out", "PF": base / "batch", "NEW": "offline-new",
          "ENV": "offline-env", "uuid": uuid}
    extract(source, ["load", "save", "sha", "transact"], ns)
    return base, ns


class FakeRemote:
    def __init__(self, ns, uncertain_first=False):
        self.ns = ns
        self.uncertain_first = uncertain_first
        self.calls = []

    def post_public(self, endpoint, body, content_type):
        journal = self.ns["load"](self.ns["OUT"] / "business-post-journal.json")
        row = journal["attempts"][-1]
        wire = self.ns["TASK"] / row["wire_body_task_relative"]
        assert wire.read_bytes() == body
        assert row["wire_body_sha256"] == digest(body) and row["receipt_saved"] is False
        self.calls.append({"endpoint": endpoint, "body_sha256": digest(body),
                           "operation": row["operation"], "WAL_and_wire_present_before_fake_POST": True})
        if self.uncertain_first and len(self.calls) == 1:
            raise RuntimeError("FAKE response lost after FAKE POST: unknown result")
        return {"submission_id": "fake-submission-" + str(len(self.calls))}


def test_unknown(source):
    base, ns = fixture(source, "unknown-result")
    remote = FakeRemote(ns, uncertain_first=True)
    try:
        ns["transact"](remote, "problem_2", "/verify", b"fake reviewed problem-2", "offline/type",
                       base / "receipt-problem-2.json", {"kind": "proof", "name": "problem_2"})
    except RuntimeError as error:
        uncertain_error = str(error)
    else:
        raise AssertionError("Fixture must produce unknown result")
    try:
        ns["transact"](remote, "problem_2", "/verify", b"fake reviewed problem-2", "offline/type",
                       base / "receipt-problem-2.json", {"kind": "proof", "name": "problem_2"})
    except RuntimeError:
        same_operation_retry_blocked = True
    else:
        same_operation_retry_blocked = False
    ns["transact"](remote, "proof_1", "/verify", b"fake reviewed proof-1", "offline/type",
                   base / "receipt-proof-1.json", {"kind": "proof", "name": "proof_1"})
    assert same_operation_retry_blocked and len(remote.calls) == 2
    return {"uncertain_error": uncertain_error, "same_operation_retry_blocked": same_operation_retry_blocked,
            "different_operation_permitted_after_unknown": True, "fake_POSTs": remote.calls,
            "journal": ns["load"](ns["OUT"] / "business-post-journal.json")}


def test_concurrency(source):
    base, ns = fixture(source, "concurrent-writers")
    ns["save"](ns["OUT"] / "business-post-journal.json", {"new_proposal_id": ns["NEW"], "attempts": []})
    original_load, original_save = ns["load"], ns["save"]
    both_read = threading.Barrier(2)
    first_done = threading.Event()
    journal_path = ns["OUT"] / "business-post-journal.json"
    read_seen = set()

    def scheduled_load(path):
        value = original_load(path)
        label = threading.current_thread().name
        if path == journal_path and label in {"fixture-A", "fixture-B"} and label not in read_seen:
            read_seen.add(label)
            both_read.wait(timeout=10)
        return value

    def scheduled_save(path, value):
        if path == journal_path and threading.current_thread().name == "fixture-B":
            assert first_done.wait(timeout=10)
        original_save(path, value)

    ns["load"], ns["save"] = scheduled_load, scheduled_save
    remote = FakeRemote(ns)

    def worker(label):
        threading.current_thread().name = label
        try:
            return ns["transact"](remote, "proof_same", "/verify", b"same pinned fake bytes", "offline/type",
                                  base / "same-receipt.json", {"kind": "proof", "name": "same"})
        finally:
            if label == "fixture-A":
                first_done.set()

    with ThreadPoolExecutor(max_workers=2) as pool:
        handles = [pool.submit(worker, label) for label in ["fixture-A", "fixture-B"]]
        receipts = [h.result(timeout=20) for h in handles]
    assert len(remote.calls) == 2
    return {"same_operation_fake_POST_count": len(remote.calls), "fake_POSTs": remote.calls,
            "receipts": receipts,
            "schedule": "Both exact transact invocations read the empty journal. B's original save is delayed until A completes. Original save/load values are unchanged; scheduling wrappers add no decision logic.",
            "journal": original_load(journal_path)}


def test_proof_reread(source):
    base, ns = fixture(source, "proof-read-after-gate")
    extract(source, ["verify"], ns)
    source_path = ns["PF"] / "staged/Solutions/Sol_Fake.lean"
    source_path.parent.mkdir(parents=True)
    expected = b"theorem solution : True := by trivial\n"
    changed = b"FAKE unreviewed replacement, never compiled or sent to any network\n"
    source_path.write_bytes(expected)
    remote = FakeRemote(ns)
    target = {"theorem_name": "Fake.target", "local_solution": "Solutions/Sol_Fake.lean", "explanation": "fake"}

    def prepare():
        assert source_path.read_bytes() == expected
        return [], [target], {"existing_definitions": []}

    def published(_remote, kind, _item):
        assert kind == "problem"
        source_path.write_bytes(changed)
        return {"theorem_id": "fake-canonical-target"}

    class Helpers:
        @staticmethod
        def slug(_name):
            return "Fake_target"

    ns.update({"prepare": prepare, "client": lambda: remote, "proposal": lambda _: None,
               "dependency_check": lambda *_: None, "published": published, "helpers": Helpers})
    ns["verify"]()
    wire_row = ns["load"](ns["OUT"] / "business-post-journal.json")["attempts"][0]
    wire = (base / wire_row["wire_body_task_relative"]).read_bytes()
    assert changed in wire and expected not in wire
    return {"prepare_pinned_solution_sha256": digest(expected), "later_wire_file_sha256": digest(changed),
            "recorded_solution_sha256": wire_row["solution_sha256"], "unreviewed_fixture_bytes_permitted": True,
            "fake_POSTs": remote.calls,
            "scope": "Only a fabricated solution in this pure fixture is changed; no real staged/frozen bytes are changed."}


def check_actual_metadata():
    batch = TASK / "formalization/platform/analytic-phase"
    prep = batch / "publication-preparation-2026-10-07"
    manifest = json.loads((prep / "prepared-publication-v1.json").read_text(encoding="utf-8"))
    plan = json.loads((batch / "target-plan.json").read_text(encoding="utf-8"))
    checked = []
    for row in manifest["seven_payloads"]:
        pairs = []
        for field in ["staged_source", "publication_source_copy"]:
            binding = row[field]
            b = (TASK / binding["task_relative"]).read_bytes()
            assert len(b) == binding["bytes"] and digest(b) == binding["sha256"]
            pairs.append(b)
        assert pairs[0] == pairs[1]
        checked.append({"kind": row["kind"], "path": row["root_relative"], "sha256": digest(pairs[0]), "bytes": len(pairs[0])})
    request = json.loads((prep / "problems-request-v1.json").read_text(encoding="utf-8"))
    definitions = json.loads((prep / "definitions-request-v1.json").read_text(encoding="utf-8"))
    targets = {row["theorem_name"]: row for row in plan["targets"]}
    names = [item["theorem_name"] for item in request["problems"]]
    assert len(names) == 3 and len(set(names)) == 3 and set(names) == set(targets)
    headers = []
    for item in request["problems"]:
        target = targets[item["theorem_name"]]
        reference = (batch / "staged" / target["local_reference"]).read_text(encoding="utf-8")
        assert reference == item["preamble"] + "\n\n" + item["formal_statement"] + "\n"
        expected = target["exact_original_header"].replace("theorem " + item["theorem_name"].rsplit(".", 1)[1], "theorem " + item["theorem_name"], 1) + " := by sorry"
        assert item["formal_statement"] == expected
        headers.append({"theorem_name": item["theorem_name"], "full_original_formal_statement": item["formal_statement"], "double_newline_reference_exact": True})
    assert definitions[0]["definition"] == (batch / "staged" / plan["local_definition"]).read_text(encoding="utf-8")
    return {"exact_seven_payloads": checked, "all_three_full_original_headers": headers,
            "all_three_unique_names": True, "public_definition": definitions[0]["private"] is False,
            "public_problems": request["private"] is False, "environment": request["env"],
            "proposal_mutation_permitted": manifest["proposal_mutation_permitted"],
            "mission_link_permitted": manifest["mission_link_permitted"],
            "definition_metadata": {k: v for k, v in definitions[0].items() if k != "definition"},
            "problem_metadata": [{k: v for k, v in item.items() if k not in {"preamble", "formal_statement"}} for item in request["problems"]]}


def main():
    destination = HERE / "baseline-fixture-results.json"
    assert not destination.exists()
    snapshots = {}
    for name in [PF_NAME, PHASE_NAME, PREP_NAME]:
        b = (SCRIPTS / name).read_bytes()
        snapshot = HERE / "source-snapshots" / name
        snapshot.parent.mkdir(parents=True, exist_ok=True)
        snapshot.write_bytes(b)
        snapshots[name] = {"sha256": digest(b), "bytes": len(b), "snapshot": snapshot.relative_to(HERE).as_posix()}
    source = (HERE / "source-snapshots" / PF_NAME).read_text(encoding="utf-8")
    result = {"checked_at": datetime.now(timezone.utc).isoformat(), "review_kind": "pure offline publishing safety; no mathematical independent certification",
              "SOURCE_snapshots": snapshots, "Lean_calls": 0, "network_calls": 0, "credentials_reads": 0,
              "baseline_unknown_result": test_unknown(source), "baseline_concurrent_writers": test_concurrency(source),
              "baseline_proof_reread": test_proof_reread(source), "actual_metadata": check_actual_metadata()}
    pure_save(destination, result)
    print(json.dumps({"results": str(destination), "sha256": digest(destination.read_bytes()),
                      "baseline_unknown_different_operation_permitted": True, "baseline_concurrent_duplicate_fake_POSTs": 2,
                      "baseline_unreviewed_fixture_proof_bytes_permitted": True,
                      "actual_seven_payloads_and_full_original_headers_exact": True,
                      "Lean_calls": 0, "network_calls": 0, "credentials_reads": 0}, indent=2))


if __name__ == "__main__":
    main()
