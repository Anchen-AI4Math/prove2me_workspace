"""Prepare or durably verify the epsilon/2 bridge on the existing canonical root.

This wrapper never creates a theorem or proposal.  ``--prepare-only`` is pure
and requires the three bounded compiler records.  ``--advance`` can POST only
one proof to the exact existing canonical target, writes its intent first, and
thereafter only polls the recorded submission.  On ``SKETCH_ACCEPTED`` it reads
the refreshed graph and decompositions and checks the actual Open-parent edge.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path

import stage_openai_bound_two_graph_bridge as full
import stage_openai_bound_two_graph_bridge_3ctx_v2 as stage


TASK, ROOT, STAGE = stage.TASK, stage.ROOT, stage.STAGE
OLD_STAGE = stage.BASE
DEST = STAGE / "verification-publication"
SELF = Path(__file__).resolve()
API = ROOT / "scripts/p2m_api.py"
STD3 = {"propext", "Classical.choice", "Quot.sound"}
VERIFY_STATUSES = {"PENDING", "COMPILING", "SKETCH_ACCEPTED", "ACCEPTED",
                   "CE", "WA", "SORRY", "FAILED", "ERROR"}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha_bytes(raw):
    return hashlib.sha256(raw).hexdigest()


def sha(path):
    return sha_bytes(Path(path).read_bytes())


def read(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def encode(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode()


def exact(path, raw):
    path = Path(path)
    if path.exists() and path.read_bytes() != raw:
        raise ValueError("Frozen epsilon/2 bridge verification artifact differs: " + str(path))
    if not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)


def task_path(value):
    path = Path(value)
    return path if path.is_absolute() else TASK / path


def open_sketch_axioms(log_path):
    """Parse exactly one expected Open-parent axiom line.

    The shared closed-proof parser intentionally rejects ``sorryAx``.  This
    local parser has the single finite exception needed for an imported Open
    platform child and still rejects every name outside Std3 plus ``sorryAx``.
    """
    marker = "'solution' depends on axioms: ["
    rows = [line.strip() for line in Path(log_path).read_text(encoding="utf-8").splitlines()
            if marker in line]
    need(len(rows) == 1 and rows[0].endswith("]"),
         "Expected exactly one complete solution axiom line in Open sketch audit")
    values = [item.strip() for item in rows[0].split(marker, 1)[1][:-1].split(",") if item.strip()]
    need(len(values) == len(set(values)) and set(values) <= STD3 | {"sorryAx"}
         and "sorryAx" in values,
         "Open sketch axiom line is outside the finite Std3 + sorryAx envelope")
    return values


def preflight(source, manifest, expected_module, emit_olean, *, borrowed=False):
    # c1 is intentionally borrowed from the byte-identical old stage: root had
    # already started that actual compile before the 3-context micro-stage was
    # requested. c2/c4 are native to the micro-stage.
    source = Path(source)
    record_path = Path(str(source) + ".preflight.json")
    need(record_path.is_file(), "Actual bridge preflight is pending: " + str(record_path))
    row = read(record_path)
    expected_manifest = read(manifest)
    need(row["success"] is True and row["exit_code"] == 0 and row["timed_out"] is False
         and 0 < row["seconds"] <= 300 and row["timeout_seconds"] == 300
         and row["source_unchanged"] is True and row["manifest_unchanged"] is True
         and row["input_certificates_stable"] is True
         and row["dependencies_stable_during_compile"] is True
         and row["actual_module_identity"] == expected_module
         and row["source_sha256_before"] == row["source_sha256_after"] == sha(source)
         and row["manifest_sha256_before"] == row["manifest_sha256_after"] == sha(manifest)
         and row["mode"] == expected_manifest["mode"]
         and bool(row["output_olean"]) is emit_olean,
         "Actual bridge compiler record differs: " + str(source))
    if emit_olean:
        need(sha(task_path(row["output_olean"])) == row["output_olean_sha256"],
             "Actual bridge OLean changed: " + expected_module)
    return {"record": full.rel(record_path), "record_sha256": sha(record_path),
            "source": full.rel(source), "source_sha256": sha(source),
            "manifest": full.rel(manifest), "manifest_sha256": sha(manifest),
            "module": expected_module, "seconds": row["seconds"],
            "output_olean": row["output_olean"],
            "output_olean_sha256": row["output_olean_sha256"],
            "log": row["log"], "log_sha256": row["log_sha256"],
            "borrowed_byte_identical_old_stage_context": borrowed}


def validation():
    stage.check_only()
    plan = read(STAGE / "preparation.json")
    old_plan = read(OLD_STAGE / "preparation.json")
    need((OLD_STAGE / full.PARENT_FILE).read_bytes() == (STAGE / full.PARENT_FILE).read_bytes()
         and read(OLD_STAGE / "c1.json")["output_sha256"] ==
             read(STAGE / "c1.json")["output_sha256"],
         "Borrowed parent source/manifest content differs across stages")
    c1 = preflight(OLD_STAGE / full.PARENT_FILE, OLD_STAGE / "c1.json",
                   full.PARENT_MODULE, True, borrowed=True)
    c2 = preflight(STAGE / full.SOLUTION_FILE, STAGE / "c2.json",
                   full.SOLUTION_MODULE, True)
    c4 = preflight(STAGE / stage.AUDIT_FILE, STAGE / "c4.json",
                   Path(stage.AUDIT_FILE).stem, False)
    open_axioms = open_sketch_axioms(task_path(c4["log"]))
    need("sorryAx" in open_axioms and set(open_axioms) - {"sorryAx"} <= STD3,
         "Open-parent bridge audit lacks its sole expected non-Std3 axiom")
    solution = STAGE / full.SOLUTION_FILE
    raw = solution.read_bytes()
    command = (STAGE / "literal-theorem-command.lean.txt").read_bytes()
    need(raw.count(command) == 1 and b"sorry" not in raw and b"#print" not in raw
         and b"PiIrrationality.openai_bound_two" not in raw
         and full.PLATFORM_IMPORT in raw and full.SOURCE_IMPORT not in raw,
         "Submitted bridge source is not the exact target-independent literal proof")
    historical = plan["historical_closed_source_solution"]
    need(sha(TASK / historical["certificate"]) == historical["certificate_sha256"]
         and sha(TASK / historical["log"]) == historical["log_sha256"]
         and historical["axioms"] == ["propext", "Classical.choice", "Quot.sound"]
         and historical["closed_full_build"] is True,
         "Historical real-source closed mirror certificate differs")
    return {
        "schema_version": 1,
        "artifact_kind": "canonical-openai-bound-two-epsilon-half-bridge-validation",
        "target_theorem_id": full.TARGET_ID,
        "target_theorem_name": "PiIrrationality.openai_bound_two",
        "parent_theorem_id": full.PARENT_ID,
        "parent_theorem_name": "OAI.PiExponent.pi_eventual_lower_bound",
        "environment": full.ENV,
        "submitted_solution": full.rel(solution),
        "submitted_solution_sha256": sha(solution),
        "literal_theorem_command_sha256": sha_bytes(command),
        "solution_complete_type_checked_as": "PiIrrationality.UpperBound (2 : ℝ)",
        "solution_body_literal_source_bytes": True,
        "solution_own_code_has_sorry": False,
        "solution_has_print_command": False,
        "solution_imports_target": False,
        "open_parent_reference_is_sketch_type_validation_only": True,
        "open_parent_reference_is_not_closed_proof_evidence": True,
        "open_parent_expected_axioms": open_axioms,
        "sorryAx_source": full.PARENT_MODULE,
        "historical_real_source_closed_mirror": historical,
        "actual_preflights": {"c1_borrowed_parent": c1, "c2_solution": c2, "c4_audit": c4},
        "max_file_seconds": max(c1["seconds"], c2["seconds"], c4["seconds"]),
        "stage_preparation_sha256": sha(STAGE / "preparation.json"),
        "old_stage_preparation_sha256": sha(OLD_STAGE / "preparation.json"),
        "stage_producer_sha256": sha(Path(stage.__file__)),
        "full_stage_producer_sha256": sha(Path(full.__file__)),
        "wrapper_sha256": sha(SELF),
        "api_client_sha256": sha(API),
        "validated": True,
        "Lean_started_by_wrapper": False,
        "API_used": False,
        "submission_ready": False,
    }


def explanation():
    return (
        "Let ε>0. Apply OAI.PiExponent.pi_eventual_lower_bound at the exponent "
        "2+ε/2>2, obtaining Q≥2 and q^{-(2+ε/2)}≤|π-p/q| for q≥Q. "
        "Such q satisfies q>1. Since -(2+ε)<-(2+ε/2), strict monotonicity of "
        "the real power of the base q gives q^{-(2+ε)}<q^{-(2+ε/2)}. Rewriting "
        "1/q^{2+ε} as q^{-(2+ε)} and composing the inequalities proves the "
        "campaign's exact PiIrrationality.UpperBound 2 statement."
    )


def artifacts():
    report = validation()
    target, parent = read(full.TARGET_JSON), read(full.PARENT_JSON)
    solution = STAGE / full.SOLUTION_FILE
    descriptor = {"theorem_id": full.TARGET_ID, "proof_type": "prove",
                  "explanation": explanation(),
                  "file": {"filename": Path(full.SOLUTION_FILE).name,
                           "source": full.rel(solution), "sha256": sha(solution),
                           "utf8": solution.read_text(encoding="utf-8")}}
    spec = importlib.util.spec_from_file_location("p2m_api_offline", API)
    api = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(api)
    multipart, ctype = api._multipart(
        {"theorem_id": descriptor["theorem_id"], "proof_type": descriptor["proof_type"],
         "explanation": descriptor["explanation"]},
        {"file": (descriptor["file"]["filename"], descriptor["file"]["utf8"].encode())})
    pins = {
        "schema_version": 1,
        "artifact_kind": "canonical-openai-bound-two-existing-target-proof-preparation",
        "target_theorem_id": full.TARGET_ID,
        "target_theorem_name": target["theorem_name"],
        "parent_theorem_id": full.PARENT_ID,
        "parent_theorem_name": parent["theorem_name"],
        "environment": full.ENV,
        "target_snapshot_sha256": sha(full.TARGET_JSON),
        "parent_snapshot_sha256": sha(full.PARENT_JSON),
        "validation_sha256": sha_bytes(encode(report)),
        "descriptor_sha256": sha_bytes(encode(descriptor)),
        "multipart_sha256": sha_bytes(multipart),
        "multipart_content_type": ctype,
        "solution_sha256": report["submitted_solution_sha256"],
        "wrapper_sha256": sha(SELF),
        "api_client_sha256": sha(API),
        "route": "/verify",
        "exact_existing_target_only": True,
        "creates_theorem_or_proposal": False,
        "durable_post_policy": "write verify_intent before POST; never repeat an existing intent",
        "expected_success_status": "SKETCH_ACCEPTED",
        "post_acceptance_checks": ["target readback", "graph", "decompositions", "actual parent edge"],
        "API_used": False,
        "submission_ready": False,
    }
    return report, descriptor, multipart, pins


def prepare():
    report, descriptor, multipart, pins = artifacts()
    exact(DEST / "validation.json", encode(report))
    exact(DEST / "verification-payload.json", encode(descriptor))
    exact(DEST / "verification-request.multipart", multipart)
    exact(DEST / "preparation.json", encode(pins))
    return {"prepared": True, "network_used": False, "API_used": False,
            "target_theorem_id": full.TARGET_ID,
            "solution_sha256": pins["solution_sha256"],
            "multipart_sha256": pins["multipart_sha256"]}


def check():
    report, descriptor, multipart, pins = artifacts()
    need((DEST / "validation.json").read_bytes() == encode(report)
         and (DEST / "verification-payload.json").read_bytes() == encode(descriptor)
         and (DEST / "verification-request.multipart").read_bytes() == multipart
         and (DEST / "preparation.json").read_bytes() == encode(pins),
         "Prepared canonical bridge verification bytes differ")
    return report, descriptor, multipart, pins


def exact_server_theorem(current, frozen, label):
    for key in ("theorem_id", "theorem_name", "preamble", "formal_statement",
                "mathlib_rev", "visibility", "deprecated_at", "deprecated_by"):
        need(current.get(key) == frozen.get(key), label + " server identity/type changed: " + key)


def graph_edge_check(graph, decompositions, submission_id):
    sketch = "sketch-" + submission_id
    edges = {(row.get("source"), row.get("target"), row.get("kind"))
             for row in graph.get("edges", [])}
    need(graph.get("root_id") == full.TARGET_ID
         and (full.PARENT_ID, sketch, "sketch") in edges
         and (sketch, full.TARGET_ID, "sketch") in edges,
         "Refreshed canonical graph lacks the actual e717 -> submission -> root edges")
    rows = decompositions.get("decompositions", [])
    matching = [row for row in rows if row.get("submission_id") == submission_id]
    need(len(matching) == 1
         and any(child.get("theorem_id") == full.PARENT_ID
                 and child.get("theorem_name") == "OAI.PiExponent.pi_eventual_lower_bound"
                 for child in matching[0].get("children", [])),
         "Refreshed decomposition lacks the actual e717 Open parent")
    return {"sketch_node": sketch, "parent_to_sketch": True,
            "sketch_to_root": True, "decomposition_parent_present": True,
            "graph_nodes": len(graph.get("nodes", [])), "graph_edges": len(graph.get("edges", []))}


def advance():
    report, descriptor, multipart, pins = check()
    target_frozen, parent_frozen = read(full.TARGET_JSON), read(full.PARENT_JSON)
    record_path = DEST / "publication.json"
    record = read(record_path) if record_path.exists() else {
        "target_theorem_id": full.TARGET_ID, "target_theorem_name": pins["target_theorem_name"],
        "parent_theorem_id": full.PARENT_ID, "environment": full.ENV,
        "solution_sha256": pins["solution_sha256"], "multipart_sha256": pins["multipart_sha256"]}
    need(record["target_theorem_id"] == full.TARGET_ID
         and record["parent_theorem_id"] == full.PARENT_ID
         and record["environment"] == full.ENV
         and record["solution_sha256"] == pins["solution_sha256"]
         and record["multipart_sha256"] == pins["multipart_sha256"],
         "Existing durable bridge record has different identity or bytes")

    def save():
        record["updated_at_utc"] = datetime.now(timezone.utc).isoformat()
        exact_raw = encode(record)
        record_path.parent.mkdir(parents=True, exist_ok=True)
        record_path.write_bytes(exact_raw)

    spec = importlib.util.spec_from_file_location("p2m_api", API)
    api = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(api)
    token = None

    def request(method, path, **kwargs):
        nonlocal token
        # Hash/record gate before and after every request; no Lean replay here.
        need(sha(DEST / "preparation.json") == sha_bytes(encode(pins))
             and sha(SELF) == pins["wrapper_sha256"] and sha(API) == pins["api_client_sha256"],
             "Frozen bridge request inputs changed")
        if token is None:
            token = api.get_token()
        status, raw = api._request(method, path, token=token, **kwargs)
        need(sha(DEST / "preparation.json") == sha_bytes(encode(pins)),
             "Frozen bridge preparation changed during request")
        try:
            return status, json.loads(raw)
        except json.JSONDecodeError:
            return status, {"raw_body": raw}

    def get_json(path):
        status, body = request("GET", path)
        need(status == 200 and isinstance(body, dict), "Bridge readback failed: " + path)
        return body

    if not record.get("verify_intent"):
        target = get_json("/theorems/" + full.TARGET_ID)
        parent = get_json("/theorems/" + full.PARENT_ID)
        exact_server_theorem(target, target_frozen, "Canonical target")
        exact_server_theorem(parent, parent_frozen, "Open parent")
        need(target.get("status") == "Open" and parent.get("status") == "Open",
             "Target or required Open parent no longer has the reviewed status")
        record["pre_post_target"] = target
        record["pre_post_parent"] = parent
        record["verify_intent"] = {
            "at_utc": datetime.now(timezone.utc).isoformat(),
            "endpoint": "/verify", "theorem_id": full.TARGET_ID,
            "parent_theorem_id": full.PARENT_ID,
            "multipart_sha256": pins["multipart_sha256"],
            "content_type": pins["multipart_content_type"],
            "solution_sha256": pins["solution_sha256"],
        }
        save()
        status, body = request("POST", "/verify", raw_body=multipart,
                               ctype=pins["multipart_content_type"])
        record["verify_response"] = {"http_status": status, "body": body}
        if status in (200, 202) and body.get("status") in VERIFY_STATUSES:
            record["submission_id"] = body.get("submission_id") or body.get("id")
        save()
        need(record.get("submission_id"),
             "Verification POST response is uncertain; intent recorded and POST will never be repeated")
        if body.get("status") != "SKETCH_ACCEPTED":
            return record
    else:
        need(record.get("submission_id"),
             "A verify intent exists without a known submission id; never repeat POST")
        status, body = request("GET", "/verify?submission_id=" + record["submission_id"])
        record["last_verify_verdict"] = {"http_status": status, "body": body}
        save()
        need(status == 200 and body.get("theorem_id") == full.TARGET_ID
             and body.get("status") in VERIFY_STATUSES,
             "Verification poll has unknown status or wrong target")
        if body.get("status") != "SKETCH_ACCEPTED":
            return record

    target = get_json("/theorems/" + full.TARGET_ID)
    graph = get_json("/theorems/" + full.TARGET_ID + "/graph")
    decompositions = get_json("/theorems/" + full.TARGET_ID + "/decompositions")
    exact_server_theorem(target, target_frozen, "Post-sketch canonical target")
    edge = graph_edge_check(graph, decompositions, record["submission_id"])
    for name, body in (("post-target.json", target), ("post-graph.json", graph),
                       ("post-decompositions.json", decompositions)):
        (DEST / name).write_bytes(encode(body))
    record["confirmed_SKETCH_ACCEPTED"] = True
    record["actual_parent_edge"] = edge
    record["post_readback_sha256"] = {
        name: sha(DEST / name) for name in
        ("post-target.json", "post-graph.json", "post-decompositions.json")}
    save()
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--prepare-only", action="store_true")
    modes.add_argument("--check-only", action="store_true")
    modes.add_argument("--advance", action="store_true")
    args = parser.parse_args()
    if args.prepare_only:
        result = prepare()
    elif args.check_only:
        report, _, _, pins = check()
        result = {"checked": True, "network_used": False, "API_used": False,
                  "target_theorem_id": full.TARGET_ID,
                  "max_file_seconds": report["max_file_seconds"],
                  "multipart_sha256": pins["multipart_sha256"]}
    else:
        result = advance()
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
