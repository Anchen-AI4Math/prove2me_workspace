"""Pure review of v2 line-ending metadata and publishing SOURCE, no real API."""
import ast
import copy
from datetime import datetime, timezone
import difflib
import hashlib
import json
from pathlib import Path
import sys
import traceback

sys.dont_write_bytecode = True
import review_updated as u
import review_final as f

HERE, TASK = u.HERE, u.TASK
BATCH = TASK / "formalization/platform/analytic-phase"
PREP = BATCH / "publication-preparation-2026-10-07"
V2_NAME = "publish_analytic_phase_new_mission_v2_2026_10_07.py"
V2_SHA = "fb2d3ef7bf25a8c0f6d6b53967da0a4a14f1fd910cc6216423cf1484c68dd749"
V1_SHA = "3b36cc7787dc0a2f348a5dd1037f3f9189cf4b0a15bf291a11d8e523b35ebf2b"
PF_SHA = "dda7b66a1dcc8b07d4f059aa026fdbcaee600d0d59ebef587dd87ada124f8ecb"


def load(path):
    return json.loads(path.read_bytes())


def norm(text):
    return text.replace("\r\n", "\n")


def inputs_v2():
    definitions = load(PREP / "definitions-request-v2.json")
    problems = load(PREP / "problems-request-v2.json")["problems"]
    explanations = load(PREP / "proof-explanations-v1.json")
    plan = load(BATCH / "target-plan.json")
    solutions = {}
    targets = {row["theorem_name"]: row for row in plan["targets"]}
    for item in problems:
        path = BATCH / "staged" / targets[item["theorem_name"]]["local_solution"]
        b = path.read_bytes()
        solutions[item["theorem_name"]] = {"filename": path.name, "bytes": b, "sha256": u.digest(b)}
    return definitions, problems, explanations, solutions, plan


u.actual_inputs = inputs_v2


def metadata_checks():
    v1, v2 = load(PREP / "prepared-publication-v1.json"), load(PREP / "prepared-publication-v2.json")
    assert v2["seven_payloads"] == v1["seven_payloads"]
    assert v2["metadata_v2_only_line_endings_preserved"] is True
    assert v2["seven_reviewed_payload_bytes_changed"] is False
    assert v2["Definition_wire_code_bytes_equal_actual_compiled_Source"] is True
    assert v2["catalog_header_comparison_only_CRLF_to_LF_normalization"] is True
    assert v2["proposal_mutation_permitted"] is False and v2["mission_link_permitted"] is False
    payloads = []
    for row in v2["seven_payloads"]:
        contents = []
        for key in ["staged_source", "publication_source_copy"]:
            binding = row[key]
            path = TASK / binding["task_relative"]
            b = path.read_bytes()
            assert len(b) == binding["bytes"] and u.digest(b) == binding["sha256"]
            contents.append(b)
        installed = TASK.parents[1] / row["root_relative"]
        assert installed.read_bytes() == contents[0] == contents[1]
        payloads.append({"root_relative": row["root_relative"], "sha256": u.digest(contents[0]), "bytes": len(contents[0]),
                         "staged_copy_and_installed_bytes_identical": True, "CRLF_count": contents[0].count(b"\r\n")})
    definitions, problems, _, _, plan = inputs_v2()
    old_defs = load(PREP / "definitions-request-v1.json")
    old_probs = load(PREP / "problems-request-v1.json")["problems"]
    assert definitions[0]["definition"].encode("utf-8") == (BATCH / "staged" / plan["local_definition"]).read_bytes()
    before, after = copy.deepcopy(old_defs[0]), copy.deepcopy(definitions[0])
    after["definition"] = norm(after["definition"])
    assert before == after
    headers = []
    targets = {row["theorem_name"]: row for row in plan["targets"]}
    assert len(problems) == len({p["theorem_name"] for p in problems}) == 3
    for old, item in zip(old_probs, problems):
        compare = copy.deepcopy(item)
        for key in ["preamble", "formal_statement"]:
            compare[key] = norm(compare[key])
        assert compare == old
        target = targets[item["theorem_name"]]
        raw = (BATCH / "staged" / target["local_reference"]).read_bytes()
        text = raw.decode("utf-8")
        ending = "\r\n" if "\r\n" in text else "\n"
        assert (item["preamble"] + ending * 2 + item["formal_statement"] + ending).encode("utf-8") == raw
        original = target["exact_original_header"].replace("theorem " + item["theorem_name"].rsplit(".", 1)[1], "theorem " + item["theorem_name"], 1) + " := by sorry"
        assert norm(item["formal_statement"]) == original
        headers.append({"name": item["theorem_name"], "line_ending": repr(ending), "full_original_header_only_CRLF_normalization": True,
                        "reference_reconstruction_byte_exact": True, "statement": item["formal_statement"]})
    metadata = []
    for row in v2["metadata"]:
        b = (TASK / row["task_relative"]).read_bytes()
        assert len(b) == row["bytes"] and u.digest(b) == row["sha256"]
        metadata.append(row)
    return {"seven_original_hashes_unchanged": True, "payloads": payloads, "definition_JSON_field_UTF8_bytes_exact": True,
            "v1_v2_code_only_CRLF_difference_and_other_fields_exact": True, "all_three_references": headers,
            "manifest_metadata_bindings_rehashed": metadata, "only_explicit_CRLF_to_LF_header_comparison": True}


def source_checks(old_source, new_source):
    old, new = ast.parse(old_source), ast.parse(new_source)
    a = {n.name: n for n in old.body if isinstance(n, ast.FunctionDef)}
    b = {n.name: n for n in new.body if isinstance(n, ast.FunctionDef)}
    changed = [name for name in a if ast.dump(a[name], include_attributes=False) != ast.dump(b[name], include_attributes=False)]
    assert set(changed) == {"prepare", "install_transport_adapter"}
    assert set(b) - set(a) == {"phase_validate_canonical"}
    for name in ["reviewed_wire", "valid_receipt", "batch_post_barrier", "batch_writer_lock", "phase_transact"]:
        assert ast.dump(a[name], include_attributes=False) == ast.dump(b[name], include_attributes=False)
    ns = {"PIN": HERE / "fixtures/ABSENT-PIN-v2.json"}
    u.extract(new_source, ["prepare"], ns)
    rejected = u.blocked(ns["prepare"])
    assert rejected["exception"] == "RuntimeError" and "no API operation or credentials access" in rejected["message"]
    return {"changed_functions": changed, "new_function": "phase_validate_canonical", "all_five_business_safety_functions_AST_identical_to_reviewed_v1": True,
            "missing_PIN_actual_expected_RuntimeError": rejected, "credentials_or_network_before_PIN": False}


def canonical_checks(pf_source, new_source):
    ns = {"ENV": inputs_v2()[0][0]["env"]}
    u.extract(pf_source, ["validate_canonical"], ns)
    ns["_ORIGINAL_VALIDATE_CANONICAL"] = ns["validate_canonical"]
    u.extract(new_source, ["phase_validate_canonical"], ns)
    validate = ns["phase_validate_canonical"]
    definitions, problems, _, _, _ = inputs_v2()
    positives, negatives = [], []
    for kind, item in [("definition", definitions[0])] + [("problem", row) for row in problems]:
        name = item["definition_name" if kind == "definition" else "theorem_name"]
        value = {"theorem_name": name, "visibility": "public", "mathlib_rev": ns["ENV"], "deprecated_at": None,
                 "theorem_title": item["definition_title" if kind == "definition" else "theorem_title"],
                 "status": "Definition" if kind == "definition" else "Open", "natural_language_statement": item["natural_language_statement"], "source": item["source"]}
        fields = ["definition"] if kind == "definition" else ["formal_statement", "preamble"]
        for key in fields:
            value[key] = norm(item[key])
        frozen_item, frozen_value = copy.deepcopy(item), copy.deepcopy(value)
        result = validate(value, item, kind)
        assert result is value and result == frozen_value and item == frozen_item and value == frozen_value
        positives.append({"name": name, "LF_only_canonical_allowed": True, "raw_value_identity_returned": True, "input_dicts_unmodified": True})
        changes = {"name": {"theorem_name": name + "_different"}, "ENV": {"mathlib_rev": "different-environment"},
                   "private": {"visibility": "private"}, "deprecated": {"deprecated_at": "date"},
                   "title": {"theorem_title": "Different title"}, "source": {"source": "Different source"},
                   "natural_language": {"natural_language_statement": "Different statement"}}
        if kind == "definition":
            changes["definition_symbols"] = {"definition": value["definition"].replace("10 *", "11 *", 1)}
            assert changes["definition_symbols"]["definition"] != value["definition"]
            changes["definition_status"] = {"status": "Proved"}
        else:
            changes["formal_math"] = {"formal_statement": value["formal_statement"].replace("phase", "changedPhase", 1)}
            changes["preamble_import"] = {"preamble": value["preamble"] + "\nimport Theorems.Fake"}
            if "10564011" in value["formal_statement"]:
                changes["certified_number"] = {"formal_statement": value["formal_statement"].replace("10564011", "10564012")}
            if "1 < x" in value["formal_statement"]:
                changes["domain"] = {"formal_statement": value["formal_statement"].replace("1 < x", "1 ≤ x")}
        for label, patch in changes.items():
            altered = {**copy.deepcopy(value), **patch}
            rejected = u.blocked(lambda altered=altered: validate(altered, item, kind))
            negatives.append({"name": name, "changed_field": label, "rejected": rejected})
    return {"positive_LF_only_cases": positives, "other_field_or_math_change_rejections": negatives,
            "only_code_field_CRLF_to_LF_normalized": True, "raw_canonical_and_request_not_modified": True, "fake_or_real_POSTs": 0}


def main():
    report_path = HERE / "pure-safety-review-v2.json"
    assert not report_path.exists()
    v2_path = TASK / "scripts" / V2_NAME
    v1_path = TASK / "scripts/publish_analytic_phase_new_mission_2026_10_07.py"
    pf_path = TASK / "scripts" / u.PF_NAME
    v2, v1, pf = v2_path.read_bytes(), v1_path.read_bytes(), pf_path.read_bytes()
    assert u.digest(v2) == V2_SHA and u.digest(v1) == V1_SHA and u.digest(pf) == PF_SHA
    snapshot = HERE / "source-snapshots/publisher-final-v2.py"
    snapshot.write_bytes(v2)
    (HERE / "source-snapshots/frozen-PF.py").write_bytes(pf)
    (HERE / "source-minimal-diff-final.patch").write_text("".join(difflib.unified_diff(v1.decode().splitlines(True), v2.decode().splitlines(True), fromfile=V1_SHA, tofile=V2_SHA)), encoding="utf-8")
    result = {"checked_at": datetime.now(timezone.utc).isoformat(), "metadata": metadata_checks(),
              "SOURCE_minimal_difference": source_checks(v1.decode(), v2.decode()),
              "safety_fixtures": u.run(pf.decode(), v2.decode(), snapshot),
              "MIME_and_original_verify_integration": f.additional_checks(pf.decode(), v2.decode()),
              "canonical_readback_boundary": canonical_checks(pf.decode(), v2.decode()),
              "Lean_calls": 0, "network_calls": 0, "credentials_reads": 0}
    assert result["safety_fixtures"]["MIME_transfer_encoding"]["rejected"] is True
    u.pure_save(HERE / "v2-fixture-results.json", result)
    assert u.digest(v2_path.read_bytes()) == V2_SHA and u.digest(v1_path.read_bytes()) == V1_SHA and u.digest(pf_path.read_bytes()) == PF_SHA
    rows = []
    for path in sorted(HERE.rglob("*")):
        if path.is_file() and "__pycache__" not in path.parts and path.name not in {"pure-safety-review-v2.json", "post-freeze-v2-check.json"}:
            b = path.read_bytes()
            rows.append({"task_relative": path.relative_to(TASK).as_posix(), "bytes": len(b), "sha256": u.digest(b)})
    report = {"frozen_at": datetime.now(timezone.utc).isoformat(), "verdict": "PASS_FOR_REVIEWED_V2_PUBLICATION_SAFETY_SCOPE",
              "publisher_v2": {"task_relative": v2_path.relative_to(TASK).as_posix(), "sha256": V2_SHA},
              "frozen_publisher_v1_sha256_unchanged": V1_SHA, "frozen_PF_sha256_unchanged": PF_SHA,
              "v2_fixture_report_sha256": u.digest((HERE / "v2-fixture-results.json").read_bytes()), "stable_files": rows,
              "stable_files_count": len(rows), "stable_bytes": sum(row["bytes"] for row in rows),
              "seven_actual_source_copy_installed_and_metadata_bytes_exact": True,
              "complete_original_three_formal_statements_preserved": True,
              "metadata_v1_v2_only_explicit_line_endings_changed": True,
              "all_normal7_resume0_unknown_concurrency_WAL_wire_MIME_proof_snapshot_fixtures_passed": True,
              "canonical_readback_only_code_CRLF_LF_allowed_others_strict": True,
              "raw_readback_preserved_and_request_not_mutated": True,
              "new_PIN_required_before_actual_credentials_API": True,
              "old_mission_and_frozen_proposal_writes_remain_blocked_by_unchanged_transport": True,
              "metadata_phase_component_only_not_whole_Z9A_or_irrationality": True,
              "scope": "Pure SOURCE/API-payload safety review. Does not certify mathematical independent PASS; reviewer authored platform Phase payloads. Fabricated fixture PIN/cache confers no real publication authorization.",
              "Lean_calls": 0, "API_calls": 0, "network_calls": 0, "credentials_reads": 0,
              "old_frozen_safety_reports_or_stage_modified": False}
    u.pure_save(report_path, report)
    for row in rows:
        b = (TASK / row["task_relative"]).read_bytes()
        assert len(b) == row["bytes"] and u.digest(b) == row["sha256"]
    post = {"checked_at": datetime.now(timezone.utc).isoformat(), "report_sha256": u.digest(report_path.read_bytes()),
            "stable_files_count": len(rows), "differences": 0, "v2_SOURCE_sha256": V2_SHA,
            "positive_readback_LF_cases": len(result["canonical_readback_boundary"]["positive_LF_only_cases"]),
            "negative_readback_cases": len(result["canonical_readback_boundary"]["other_field_or_math_change_rejections"]),
            "Lean_calls": 0, "API_calls": 0, "credentials_reads": 0}
    u.pure_save(HERE / "post-freeze-v2-check.json", post)
    print(json.dumps({"report": str(report_path), **post}, indent=2))


if __name__ == "__main__":
    try:
        main()
    except BaseException:
        path = HERE / ("v2-failure-" + datetime.now(timezone.utc).strftime("%H%M%S") + ".json")
        u.pure_save(path, {"at": datetime.now(timezone.utc).isoformat(), "traceback": traceback.format_exc(),
                           "Lean_calls": 0, "API_calls": 0, "credentials_reads": 0})
        raise
