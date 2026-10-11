"""Final SOURCE regression and freeze; every remote is fake, all writes own."""
from datetime import datetime, timezone
import json
from pathlib import Path
import sys
import traceback

import review_updated as u

HERE, TASK = u.HERE, u.TASK
EXPECTED_PHASE_SHA = "3b36cc7787dc0a2f348a5dd1037f3f9189cf4b0a15bf291a11d8e523b35ebf2b"
EXPECTED_PF_SHA = "dda7b66a1dcc8b07d4f059aa026fdbcaee600d0d59ebef587dd87ada124f8ecb"
original_fixture = u.fixture
u.fixture = lambda source, name: original_fixture(source, "final-" + name)


def additional_checks(pf_source, phase_source):
    base, ns, defs, probs, explanations, solutions, plan = u.new_case(pf_source, phase_source, "headers")
    remote = u.FakeRemote(ns)
    expected = solutions[probs[0]["theorem_name"]]["bytes"]
    import base64
    original = u.operation(ns, "proof", probs[0])
    probes = {"base64_CTE": u.operation(ns, "proof", probs[0], proof_bytes=base64.b64encode(expected), content_transfer_encoding="base64")}
    for name, extra in [("duplicate_Content_Disposition", b'Content-Disposition: form-data; name="different-file"\r\n'),
                        ("duplicate_Content_Type", b"Content-Type: application/octet-stream\r\n")]:
        body = original[2].replace(b"Content-Type: text/plain; charset=utf-8\r\n", b"Content-Type: text/plain; charset=utf-8\r\n" + extra, 1)
        probes[name] = (*original[:2], body, *original[3:])
    results = {}
    for name, args in probes.items():
        results[name] = u.blocked(lambda args=args: ns["phase_transact"](remote, *args))
    assert not remote.calls
    results["header_probes_fake_POSTs"] = 0
    base, ns, defs, probs, explanations, solutions, plan = u.new_case(pf_source, phase_source, "original_verify_integration")
    u.extract(pf_source, ["verify"], ns)
    first = probs[0]
    target = next(t for t in plan["targets"] if t["theorem_name"] == first["theorem_name"])
    path = ns["PF"] / "staged" / target["local_solution"]
    path.parent.mkdir(parents=True)
    path.write_bytes(solutions[first["theorem_name"]]["bytes"])
    remote = u.FakeRemote(ns)
    item = {**first, "local_solution": target["local_solution"], "explanation": explanations[first["theorem_name"]]}

    def fake_published(_remote, kind, _item):
        assert kind == "problem"
        path.write_bytes(b"FAKE post-gate changed solution bytes, no Lean or API")
        return {"theorem_id": "fake-canonical-integration"}

    ns.update({"prepare": lambda: ([], [item], {"existing_definitions": []}), "client": lambda: remote,
               "proposal": lambda _: None, "dependency_check": lambda *_: None, "published": fake_published,
               "helpers": ns["transport"].helpers, "transact": ns["phase_transact"]})
    results["original_verify_post_gate_file_mutation_blocks"] = u.blocked(ns["verify"])
    assert not remote.calls
    results["original_verify_integration_fake_POSTs"] = 0
    return results


def main():
    final_report = HERE / "pure-safety-review.json"
    assert not final_report.exists(), "Preserve frozen report"
    phase_path = u.SCRIPTS / u.PHASE_NAME
    phase_bytes = phase_path.read_bytes()
    pf_bytes = (u.SCRIPTS / u.PF_NAME).read_bytes()
    assert u.digest(phase_bytes) == EXPECTED_PHASE_SHA and u.digest(pf_bytes) == EXPECTED_PF_SHA
    snapshot = HERE / "source-snapshots" / (EXPECTED_PHASE_SHA + "-" + u.PHASE_NAME)
    assert not snapshot.exists()
    snapshot.write_bytes(phase_bytes)
    checks = u.run(pf_bytes.decode(), phase_bytes.decode(), snapshot)
    assert checks["MIME_transfer_encoding"]["rejected"] is True
    additional = additional_checks(pf_bytes.decode(), phase_bytes.decode())
    result = {"checked_at": datetime.now(timezone.utc).isoformat(), "phase_SOURCE_sha256": EXPECTED_PHASE_SHA,
              "frozen_PF_SOURCE_sha256": EXPECTED_PF_SHA, "checks": checks, "additional_checks": additional,
              "Lean_calls": 0, "network_calls": 0, "credentials_reads": 0,
              "scope": "Offline publication safety only. Fabricated fixture PIN/cache assumes a legitimately prepared state and confers no real publication authorization."}
    u.pure_save(HERE / "final-fixture-results.json", result)
    assert u.digest(phase_path.read_bytes()) == EXPECTED_PHASE_SHA
    assert u.digest((u.SCRIPTS / u.PF_NAME).read_bytes()) == EXPECTED_PF_SHA
    baseline = json.loads((HERE / "baseline-fixture-results.json").read_text(encoding="utf-8"))
    static = json.loads((HERE / "static-review-results.json").read_text(encoding="utf-8"))
    assert len(baseline["actual_metadata"]["exact_seven_payloads"]) == 7
    report = {"reviewed_at": datetime.now(timezone.utc).isoformat(), "verdict": "PASS_FOR_REVIEWED_PUBLICATION_SAFETY_SCOPE",
              "phase_SOURCE": {"task_relative": phase_path.relative_to(TASK).as_posix(), "sha256": EXPECTED_PHASE_SHA, "bytes": len(phase_bytes)},
              "preparer_SOURCE": {"task_relative": (u.SCRIPTS / "prepare_analytic_phase_publication_2026_10_07.py").relative_to(TASK).as_posix(),
                                  "sha256": u.digest((u.SCRIPTS / "prepare_analytic_phase_publication_2026_10_07.py").read_bytes())},
              "frozen_PF_SOURCE_sha256_unchanged": EXPECTED_PF_SHA,
              "resolved_findings": [
                  {"problem": "Unknown POST only blocked the same operation", "repair": "Phase batch barrier stops every further business POST until Root reconciles documented history", "fixture": "baseline_unknown_result -> final unknown_other_operation_blocks"},
                  {"problem": "Concurrent writers could both POST the same operation", "repair": "Exclusive Windows byte writer lock serializes batch writers", "fixture": "baseline_concurrent_writers -> final concurrent and real Python cross-process lock checks"},
                  {"problem": "Proof bytes could be re-read after preparation and differ from reviewed bytes", "repair": "Full outgoing Definition/Problem/multipart file bytes checked against in-memory reviewed snapshots", "fixture": "baseline_proof_reread -> final changed payloads and original verify integration"},
                  {"problem": "MIME transfer decoding could hide different literal upload bytes", "repair": "Reject Content-Transfer-Encoding and duplicate disposition/type headers", "fixture": "updated MIME transfer-encoding permissive -> final base64/duplicate header prePOST rejection"}],
              "guard_results": {"complete_Root_PIN_before_normal_credentials_or_API_entrypoints": True,
                                "missing_PIN_actual_expected_RuntimeError": True, "official_v0_12_1_docs_six_exact_pins": True,
                                "official_health_version_before_credentials_SOURCE_order": True,
                                "old_mission_and_frozen_proposal_writes_blocked_in_fake_guard_cases": True,
                                "normal_business_POSTs_exactly_seven": True, "successful_resume_additional_POSTs": 0,
                                "unknown_result_blocks_entire_batch": True, "concurrent_same_operation_POSTs_exactly_one": True,
                                "cross_process_lock_blocks_held_and_allows_released": True,
                                "invalid_receipt_or_journal_or_wire_or_PIN_blocks_before_POST": True,
                                "actual_seven_payloads_and_copies_exact": True,
                                "actual_three_complete_original_headers_and_double_newline_references_exact": True,
                                "metadata_describes_phase_component": True, "whole_Z9_A_or_irrationality_claimed": False},
              "scope_limits": ["No real credentials or network were read/used", "No Lean compilation performed", "Does not certify independent mathematical PASS; the reviewer authored Phase platform payloads",
                               "Real publication still requires complete Root native/platform author/platform independent pins and their full binding gates",
                               "Unknown result is deliberately not auto-reconciled; Root must use documented remote history before modifying/recovering WAL state"],
              "Lean_calls": 0, "network_calls": 0, "credentials_reads": 0, "mathematical_independent_PASS_not_claimed": True,
              "fixtures": {name: {"task_relative": (HERE / name).relative_to(TASK).as_posix(), "sha256": u.digest((HERE / name).read_bytes())}
                           for name in ["baseline-fixture-results.json", "static-review-results.json", "updated-fixture-results.json", "final-fixture-results.json"]}}
    bindings = []
    for path in sorted(HERE.rglob("*")):
        if path.is_file() and "__pycache__" not in path.parts and path.name not in {"pure-safety-review.json", "post-freeze-check.json"}:
            b = path.read_bytes()
            bindings.append({"task_relative": path.relative_to(TASK).as_posix(), "bytes": len(b), "sha256": u.digest(b)})
    report["stable_files"] = bindings
    report["stable_files_count"] = len(bindings)
    report["stable_bytes"] = sum(row["bytes"] for row in bindings)
    u.pure_save(final_report, report)
    for row in bindings:
        b = (TASK / row["task_relative"]).read_bytes()
        assert len(b) == row["bytes"] and u.digest(b) == row["sha256"]
    post = {"checked_at": datetime.now(timezone.utc).isoformat(), "report_sha256": u.digest(final_report.read_bytes()),
            "stable_files_count": len(bindings), "differences": 0, "phase_SOURCE_sha256": u.digest(phase_path.read_bytes()),
            "frozen_PF_SOURCE_sha256": u.digest((u.SCRIPTS / u.PF_NAME).read_bytes()), "actual_this_cell_exit_expected": 0,
            "Lean_calls": 0, "network_calls": 0, "credentials_reads": 0}
    u.pure_save(HERE / "post-freeze-check.json", post)
    print(json.dumps({"report": str(final_report), **post}, indent=2))


if __name__ == "__main__":
    try:
        main()
    except BaseException:
        path = HERE / ("final-review-failure-" + datetime.now(timezone.utc).strftime("%H%M%S") + ".json")
        u.pure_save(path, {"at": datetime.now(timezone.utc).isoformat(), "traceback": traceback.format_exc(),
                           "Lean_calls": 0, "network_calls": 0, "credentials_reads": 0})
        raise
