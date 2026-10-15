"""Pure finite binding of the certified AP11 proof to the _source017 target.

The only new Lean evidence is the renamed comparator modecheck.  Original AP11
source, proof, five contexts, kernel snapshots, and Sol OLean are replayed.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import certify_grouped_collision_rate_node as original
import stage_collision_rate_source017_comparator as bridge
import validate_namespace_context_providers as context


TASK, STAGE = bridge.TASK, bridge.STAGE
SELF = Path(__file__).resolve()
CERT = STAGE / "naming-binding-validation.json"
GET = TASK / "verification/graph-refresh-20261011T131418_012581Z/existing-collision-rate-target.json"
OLD_PAYLOAD = bridge.AP11 / "publication/publish-payload.json"
INCOMPLETE_PREIMAGE = STAGE / "naming-binding-validation-incomplete-wire.preimage.json"
MODULE = "Theorems.Thm_OAI_PiExponent_DeterminantContradiction_tendsto_collisionRate_source017"


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def sha_bytes(raw):
    return hashlib.sha256(raw).hexdigest()


def read(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def encode(value):
    return (json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n").encode()


def rel(path):
    return Path(path).resolve().relative_to(TASK.resolve()).as_posix()


def validate(write=False):
    bridge.check_only()
    prior = original.validate(write=False)
    need(read(bridge.CERT) == prior and sha(bridge.CERT) == read(STAGE / bridge.AUDIT)["AP11_certificate_sha256"],
         "Original five-context AP11 certificate changed")
    audit = read(STAGE / bridge.AUDIT)
    old = bridge.ORIGINAL_WIRE.read_bytes()
    new_path = STAGE / bridge.OUTPUT
    new = new_path.read_bytes()
    need(old.count(bridge.OLD_TOKEN) == new.count(bridge.NEW_TOKEN) == 1
         and new == old.replace(bridge.OLD_TOKEN, bridge.NEW_TOKEN, 1)
         and new.replace(bridge.NEW_TOKEN, bridge.OLD_TOKEN, 1) == old,
         "Comparator differs beyond one original theorem-name token")
    preamble = audit["preamble"].encode()
    formal = audit["renamed_formal_statement"].encode()
    suffix = b"\n" + bridge.ap11.GROUP_FOOTERS[bridge.ap11.TARGET_MODULE]
    need(new == preamble + formal + suffix
         and sha_bytes(preamble + formal) == audit["exact_platform_wire_sha256"]
         and sha_bytes(formal) == audit["renamed_formal_statement_sha256"]
         and audit["original_source_name"] == bridge.ap11.TARGET
         and audit["public_platform_name"] == bridge.PUBLIC_NAME,
         "Finite source/public statement binding differs")
    old_problem = read(OLD_PAYLOAD)["problems"][0]
    need(old_problem["theorem_name"] == bridge.ap11.TARGET
         and old_problem["preamble"].encode() == preamble
         and old_problem["formal_statement"].encode() == formal.replace(bridge.NEW_TOKEN, bridge.OLD_TOKEN, 1)
         and old == (old_problem["preamble"] + old_problem["formal_statement"]).encode() + suffix,
         "Frozen old publish payload is not the exact missing-footer preimage")
    need(INCOMPLETE_PREIMAGE.is_file(), "Preserved first incomplete-wire certificate preimage is missing")
    pf = context.record(new_path, STAGE / bridge.MANIFEST, "modecheck", MODULE, STAGE)
    data = pf["data"]
    need(data["success"] is True and data["source_unchanged"] is True
         and data["manifest_unchanged"] is True and data["timed_out"] is False
         and data["exit_code"] == 0 and data.get("original_exit_code") is None
         and 0 < data["seconds"] <= 300
         and data["output_olean"] is None and data["output_olean_sha256"] is None
         and sha(context.file(data["log"])) == data["log_sha256"],
         "New _source017 comparator did not pass a bounded non-emitting modecheck")
    old_target = read(GET)
    need(old_target["theorem_id"] == "1a21b159-35ef-490d-8259-021afd876d54"
         and old_target["theorem_name"] == bridge.ap11.TARGET
         and old_target["status"] == "Proved"
         and old_target["visibility"] == "public"
         and old_target["deprecated_at"] is None
         and old_target["mathlib_rev"] == "0df444a360eaa60ab8c11dca51a86af692955474"
         and old_target["preamble"].startswith("import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily\n")
         and old_target["preamble"].encode() != preamble
         and old_target["formal_statement"].encode() != formal
         and old_target["theorem_name"] != bridge.PUBLIC_NAME,
         "Authoritative old-name GET no longer proves a distinct platform target")
    need(prior["source_type_equals_global_solution_type"] is True
         and prior["source_original_proof_byte_exact_after_name_change"] is True
         and prior["global_top_level_theorem_solution"] is True
         and prior["Std3_only"] is True
         and prior["type_only_theorem_values_null"] is True,
         "Original closed source/global solution proof gates differ")
    sol = TASK / prior["solution_olean"]
    need(sha(sol) == prior["solution_olean_sha256"] == audit["AP11_solution_olean_sha256"],
         "Actual AP11 solution OLean changed")
    result = {
        "schema_version": 1,
        "artifact_kind": "ap11-collision-rate-source017-finite-naming-binding-validation",
        "validated": True, "proposal_status": "Draft", "submission_ready": False,
        "original_source_name": bridge.ap11.TARGET,
        "public_platform_name": bridge.PUBLIC_NAME,
        "source_commit": bridge.ap11.COMMIT,
        "single_theorem_name_token_change": True,
        "old_token": bridge.OLD_TOKEN.decode(), "new_token": bridge.NEW_TOKEN.decode(),
        "name_token_byte_offset": audit["single_name_token_byte_offset"],
        "original_AP11_certificate": rel(bridge.CERT),
        "original_AP11_certificate_sha256": sha(bridge.CERT),
        "original_AP11_five_contexts_replayed": True,
        "original_AP11_type_and_closed_proof_reused": True,
        "original_AP11_solution_olean": rel(sol),
        "original_AP11_solution_olean_sha256": sha(sol),
        "bridge_audit": rel(STAGE / bridge.AUDIT),
        "bridge_audit_sha256": sha(STAGE / bridge.AUDIT),
        "new_comparator": rel(new_path), "new_comparator_sha256": sha(new_path),
        "new_comparator_manifest": rel(STAGE / bridge.MANIFEST),
        "new_comparator_manifest_sha256": sha(STAGE / bridge.MANIFEST),
        "new_comparator_preflight": pf,
        "renamed_platform_wire_sha256": sha_bytes(new),
        "renamed_platform_formal_statement_sha256": sha_bytes(formal + suffix),
        "renamed_preamble_sha256": sha_bytes(preamble),
        "renamed_source_theorem_command_sha256": sha_bytes(formal),
        "namespace_closure_sha256": sha_bytes(suffix),
        "old_incomplete_publish_payload": rel(OLD_PAYLOAD),
        "old_incomplete_publish_payload_sha256": sha(OLD_PAYLOAD),
        "first_incomplete_wire_certificate_preimage": rel(INCOMPLETE_PREIMAGE),
        "first_incomplete_wire_certificate_preimage_sha256": sha(INCOMPLETE_PREIMAGE),
        "old_community_target_GET": rel(GET), "old_community_target_GET_sha256": sha(GET),
        "old_community_theorem_id": old_target["theorem_id"],
        "old_community_preamble_sha256": sha_bytes(old_target["preamble"].encode()),
        "old_community_statement_sha256": sha_bytes(old_target["formal_statement"].encode()),
        "old_community_target_separate": True,
        "implementation_sha256": {rel(SELF): sha(SELF), rel(Path(bridge.__file__)): sha(Path(bridge.__file__)),
                                  rel(Path(original.__file__)): sha(Path(original.__file__)),
                                  rel(Path(context.__file__)): sha(Path(context.__file__))},
        "Lean_started_by_consumer": False, "API_used": False,
    }
    if write:
        raw = encode(result)
        if CERT.exists():
            need(CERT.read_bytes() == raw, "Frozen _source017 naming certificate differs")
        else:
            CERT.write_bytes(raw)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--certify-existing", action="store_true")
    mode.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    cert = validate(write=args.certify_existing)
    if args.check_only:
        need(CERT.is_file() and CERT.read_bytes() == encode(cert),
             "Saved _source017 naming certificate differs from pure replay")
    print(json.dumps({"validated": True, "theorem_name": cert["public_platform_name"],
                      "new_modecheck_seconds": cert["new_comparator_preflight"]["data"]["seconds"],
                      "one_name_token": True, "AP11_five_contexts_replayed": True,
                      "network_used": False, "Lean_started": False,
                      "proposal_status": "Draft"}, ensure_ascii=False))


if __name__ == "__main__":
    main()
