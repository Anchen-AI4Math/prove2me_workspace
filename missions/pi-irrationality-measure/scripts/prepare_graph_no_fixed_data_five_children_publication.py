"""Pure offline preparation for the arithmetic Open child and NoFixedData sketch.

Pending preparation works before the eight Lean preflights. Final preparation
requires their strict interface certificate, a public NoFixedData target id,
and the actual Mean theorem's Accepted/Proved readback. No API is called.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path

import certify_graph_no_fixed_data_five_children as consumer
import stage_graph_no_fixed_data_five_children as stage


TASK, ROOT, STAGE = stage.TASK, stage.ROOT, stage.STAGE
DEST = STAGE / "publication-v2"
SELF = Path(__file__).resolve()
ONLINE = TASK / "scripts/publish_graph_no_fixed_data_five_children.py"
API = ROOT / "scripts/p2m_api.py"
CERT = consumer.CERT
PRIOR = TASK / "verification/graph-conditional-route-20261011-v2/publication-v3/publication.json"
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"
MEAN_RECORD = stage.CHILDREN[3][4]
ARITH_GET = TASK / "verification/determinant-core-exact-name-lookup-20261011T135109_614374Z.json"


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha_bytes(raw):
    return hashlib.sha256(raw).hexdigest()


def sha(path):
    return sha_bytes(Path(path).read_bytes())


def read(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def encode(doc):
    return (json.dumps(doc, ensure_ascii=False, indent=2) + "\n").encode()


def rel(path):
    return Path(path).resolve().relative_to(TASK.resolve()).as_posix()


def exact(path, raw):
    path = Path(path)
    if path.exists():
        need(path.read_bytes() == raw, "Frozen five-child publication artifact differs: " + str(path))
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)


def arith_metadata(prep):
    return {
        "theorem_name": stage.ARITH,
        "theorem_title": "Arithmetic lower bound for a nonzero selected interpolation minor",
        "natural_language_statement": (
            "For fixed approximation data $d$, a positive interpolation scale $H$, "
            "and a selection of columns whose interpolation minor has nonzero determinant, "
            "let $b(H)$ be the actual mean row weight and $M(H)$ the actual row count. "
            "The source arithmetic estimate gives\n\n"
            "$$-\\bigl(1-b(H)\\bigr)-e_{\\mathrm{ar}}(d)\\le "
            "\\frac{\\log|\\det A_{\\mathrm{minor}}(H)|}{M(H)H}." "$$\n\n"
            "Here $e_{\\mathrm{ar}}(d)$ is the arithmetic error stored in the "
            "campaign's original fixed data. This is the exact original source interface, "
            "currently published as an Open dependency for the NoFixedData reduction."
        ),
        "source": ("https://github.com/openai/math/blob/" + prep["source_commit"] +
                   "/lean/OAI/NumberTheory/PiExponent/Approximation/"
                   "DeterminantContradiction.lean#L74-L85"),
        "tags": ["number-theory", "determinants", "irrationality-measure", "openai-pi-exponent-017"],
    }


def explanation():
    return (
        "The source contradiction proof first combines the analytic error limit with the "
        "proved convergence of the collision rate. At sufficiently large $H$, the "
        "collision rate exceeds the total error. A surjective interpolation matrix "
        "then has a nonsingular full-row minor. Its arithmetic lower bound, the bounds "
        "on the actual mean row weight, and the analytic upper bound contradict the "
        "proved determinant-bounds inconsistency theorem. The imported children are "
        "the proved collision limit, full-row minor, comparison, and mean-bound theorems, "
        "together with the Open arithmetic lower-bound target. This submission records "
        "their exact dependency decomposition and is a sketch, not a closed proof."
    )


def static(require_final=False):
    stage.check()
    prep = read(STAGE / "preparation.json")
    need(prep["NoFixedData"]["name"] == stage.NFD and
         prep["NoFixedData"]["same_comparator_as_frozen_v2_sha256"] ==
             sha(STAGE / stage.NFD_FILE) and
         prep["source_proof_changes"] == [
             {"before": "(tendsto_collisionRate d).sub",
              "after": "(tendsto_collisionRate_source017 d).sub", "count": 1},
             {"before": "have hlower := actual_minor_arithmetic_lower_bound d H hH selection hdet'",
              "after": "have hlower := actual_minor_arithmetic_lower_bound_source017 d H hH selection hdet'",
              "count": 1}], "NoFixedData original proof binding changed")
    arith_wire = (STAGE / "arithmetic-source017-open-wire.lean").read_bytes()
    preamble = (STAGE / stage.NFD_FILE).read_bytes().split(b"theorem ", 1)[0]
    need(arith_wire.startswith(preamble) and
         arith_wire.count(("theorem " + stage.ARITH).encode()) == 1 and
         sha_bytes(arith_wire) == prep["original_arithmetic"]["source017_open_wire_sha256"] and
         arith_wire.endswith(b":= by\n  sorry\n"),
         "Arithmetic Open theorem wire is not the exact staged source type")
    arith_formal = arith_wire[len(preamble):].decode()
    arith_meta = arith_metadata(prep)
    arith_problem = {"theorem_name": stage.ARITH,
                     "theorem_title": arith_meta["theorem_title"],
                     "preamble": preamble.decode(), "formal_statement": arith_formal,
                     "natural_language_statement": arith_meta["natural_language_statement"],
                     "source": arith_meta["source"], "tags": arith_meta["tags"]}
    publish = {"problems": [arith_problem], "env": ENV, "private": False}
    solution = STAGE / stage.SOL_FILE
    solution_raw = solution.read_bytes()
    need(solution_raw.count(b"theorem solution") == 1 and b"sorry" not in solution_raw and
         stage.NFD.encode() not in solution_raw and
         sha(solution) == prep["file_sha256"][stage.SOL_FILE],
         "Global proof sketch changed or references its own target")
    previous = read(PRIOR) if PRIOR.is_file() else None
    target_id = previous.get("NoFixedData_theorem_id") if previous else None
    if target_id is not None:
        need(isinstance(target_id, str) and target_id, "Existing NoFixedData id malformed")
    lookup = read(ARITH_GET)
    rows = [row for row in lookup["records"] if row["theorem_name"] == stage.ARITH]
    need(len(rows) == 1 and rows[0]["http_status"] == 200 and rows[0]["matches"] == [] and
         lookup["environment"] == ENV and lookup["read_only"] is True,
         "Historical arithmetic source017 exact-name GET preimage differs")
    public = prep["public_children_at_staging"]
    need(all(public[k]["platform_proved_at_staging"] for k in
             ("collision", "minor", "comparison")) and
         public["mean"]["status_at_staging"] == "Open" and
         all((STAGE / "saved-public-wire" / (k + ".lean")).is_file() and
             sha(STAGE / "saved-public-wire" / (k + ".lean")) == public[k]["exact_wire_sha256"]
             for k in public), "Pinned public child wire/status differs")
    mean_now = read(MEAN_RECORD)
    mean_body = mean_now.get("target_readback", {}).get("body", {})
    mean_proved = (mean_now.get("confirmed_proved") is True and
                   mean_now.get("last_verify_verdict", {}).get("body", {}).get("status") == "ACCEPTED" and
                   mean_body.get("theorem_id") == public["mean"]["theorem_id"] and
                   mean_body.get("theorem_name") == stage.CHILDREN[3][1] and
                   mean_body.get("status") == "Proved" and
                   (mean_body.get("preamble", "") + mean_body.get("formal_statement", "")).encode() ==
                       (STAGE / "saved-public-wire/mean.lean").read_bytes())
    cert = None
    if require_final:
        need(target_id is not None, "NoFixedData public Open target id is pending")
        need(mean_proved, "Actual mean theorem has not been confirmed Accepted/Proved")
        need(CERT.is_file(), "Eight-preflight strict interface certificate is pending")
        cert = read(CERT)
        need(cert == consumer.validate(write=False) and
             CERT.read_bytes() == consumer.encode(cert) and
             cert["validated_interface"] is True and
             cert["validated_closed_proof"] is False and
             cert["five_child_graph_sketch_only"] is True and
             cert["mean_platform_proved_now"] is True and
             cert["source_to_generated_seven_kernel_type_equal"] is True and
             set(cert["all_eight_preflights"]) == set(prep["ordered_compiler_manifests"]),
             "Actual eight-preflight strict interface replay differs")
    descriptor = {"theorem_id": target_id, "proof_type": "prove",
                  "explanation": explanation(),
                  "file": {"filename": Path(stage.SOL_FILE).name, "source": rel(solution),
                           "sha256": sha(solution), "utf8": solution_raw.decode()}}
    payloads = {"arithmetic-publish-payload.json": json.dumps(publish, ensure_ascii=False).encode(),
                "verification-payload.json": encode(descriptor)}
    ctype = None
    if target_id is not None:
        spec = importlib.util.spec_from_file_location("p2m_api_offline", API)
        api = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(api)
        multipart, ctype = api._multipart(
            {"theorem_id": target_id, "proof_type": "prove", "explanation": descriptor["explanation"]},
            {"file": (descriptor["file"]["filename"], solution_raw)})
        payloads["verification-request.multipart"] = multipart
    pins = {"schema_version": 1,
            "artifact_kind": "NoFixedData-five-children-arithmetic-Open-and-existing-target-sketch-preparation",
            "environment": ENV, "proposal_status": "Draft", "submission_ready": False,
            "NoFixedData_name": stage.NFD, "NoFixedData_theorem_id": target_id,
            "arithmetic_source017_name": stage.ARITH,
            "arithmetic_historical_exact_name_GET_sha256": sha(ARITH_GET),
            "arithmetic_Open_wire_sha256": sha_bytes(arith_wire),
            "mean_theorem_id": public["mean"]["theorem_id"],
            "mean_platform_Proved_confirmed_at_preparation": mean_proved,
            "child_theorem_ids": {key: info["theorem_id"] for key, info in public.items()},
            "stage_preparation_sha256": sha(STAGE / "preparation.json"),
            "strict_certificate_sha256": sha(CERT) if cert else None,
            "offline_wrapper_sha256": sha(SELF), "online_wrapper_sha256": sha(ONLINE),
            "strict_consumer_sha256": sha(Path(consumer.__file__)),
            "stage_producer_sha256": sha(Path(stage.__file__)),
            "api_client_sha256": sha(API),
            "NoFixedData_wire_sha256": sha(STAGE / stage.NFD_FILE),
            "solution_sha256": sha(solution),
            "compiler_manifest_sha256": {name: sha(STAGE / name)
                                        for name in prep["ordered_compiler_manifests"]},
            "payload_sha256": {name: sha_bytes(raw) for name, raw in payloads.items()},
            "multipart_content_type": ctype,
            "expected_verify_status": "SKETCH_ACCEPTED", "closed_proof": False,
            "Open_arithmetic_child": True,
            "durable_policy": "save intent before POST; never repeat recorded intent; poll only known ids",
            "API_used": False}
    return prep, arith_problem, descriptor, payloads, pins, cert


def prepare_pending():
    prep, problem, descriptor, payloads, pins, cert = static(require_final=False)
    need(cert is None, "Pending mode unexpectedly has a final certificate")
    exact(DEST / "arithmetic-publish-payload.json", payloads["arithmetic-publish-payload.json"])
    exact(DEST / "arithmetic-open-wire.lean",
          (STAGE / "arithmetic-source017-open-wire.lean").read_bytes())
    # The pending descriptor is explicitly not an HTTP request.
    exact(DEST / "verification-payload.pending.json", payloads["verification-payload.json"])
    pending = dict(pins)
    pending.update({"artifact_kind": "NoFixedData-five-children-pending-publication",
                    "strict_validation_pending": True, "network_used": False})
    exact(DEST / "pending-preparation.json", encode(pending))
    return {"prepared": True, "final_ready": False, "mean_proved_now": pins["mean_platform_Proved_confirmed_at_preparation"],
            "NoFixedData_target_id_pending": pins["NoFixedData_theorem_id"] is None,
            "strict_certificate_pending": True, "network_used": False}


def prepare_final():
    prep, problem, descriptor, payloads, pins, cert = static(require_final=True)
    for name, raw in payloads.items():
        exact(DEST / name, raw)
    exact(DEST / "arithmetic-open-wire.lean",
          (STAGE / "arithmetic-source017-open-wire.lean").read_bytes())
    exact(DEST / "validation.json", CERT.read_bytes())
    exact(DEST / "preparation.json", encode(pins))
    return {"prepared": True, "final_ready": True, "Open_sketch": True,
            "closed_proof": False, "NoFixedData_theorem_id": pins["NoFixedData_theorem_id"],
            "network_used": False}


def check():
    prep, problem, descriptor, payloads, pins, cert = static(require_final=True)
    need((DEST / "preparation.json").read_bytes() == encode(pins) and
         (DEST / "validation.json").read_bytes() == CERT.read_bytes() and
         (DEST / "arithmetic-open-wire.lean").read_bytes() ==
             (STAGE / "arithmetic-source017-open-wire.lean").read_bytes(),
         "Frozen final five-child publication preparation differs")
    for name, raw in payloads.items():
        need((DEST / name).read_bytes() == raw, "Frozen HTTP payload differs: " + name)
    return prep, problem, descriptor, payloads, pins, cert


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--prepare-pending", action="store_true")
    mode.add_argument("--prepare-only", action="store_true")
    mode.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    if args.prepare_pending:
        result = prepare_pending()
    elif args.prepare_only:
        result = prepare_final()
    else:
        check()
        result = {"checked": True, "final_ready": True, "network_used": False,
                  "Open_sketch": True, "closed_proof": False}
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
