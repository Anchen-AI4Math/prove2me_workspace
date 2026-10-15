"""Derived strict AP19 certificate for the two actually observed auto CIs.

This replays the frozen original four-Def consumer with only its owned-CI
inventory guard expanded to the actual finite six-CI domain, then pairs both
closed automatic Prop proofs against one genuine source-only metadata probe.
"""
from __future__ import annotations

import argparse
from datetime import datetime
import json
from pathlib import Path

import stage_analytic_remainder_auto_ci_source_probe_v2 as probe
import certify_analytic_remainder_data_existing as original
import validate_namespace_context_providers as context
from certify_full_row_minor_node import refs
from validate_formal_log_node import checked_expr


TASK, STAGE = probe.TASK, probe.STAGE
SELF = Path(__file__).resolve()
CERT = STAGE / probe.CERTIFICATE
STD3 = {"propext", "Classical.choice", "Quot.sound"}
ROW_KEYS = {"name", "actualOwner", "privateUserName", "kind", "levelParams",
            "type", "value", "closedType", "closedValue", "isProp",
            "typeRefs", "valueRefs", "axioms"}

need, read, sha, encode, rel = probe.need, probe.read, probe.sha, probe.encode, probe.rel


def exact_refs(row):
    levels = row["levelParams"]
    need(isinstance(levels, list) and all(isinstance(x, str) for x in levels)
         and len(levels) == len(set(levels)), "Automatic CI universe binder domain differs")
    checked_expr(row["type"], set(levels))
    for field in ["typeRefs", "valueRefs", "axioms"]:
        values = row[field]
        need(isinstance(values, list) and all(isinstance(x, str) for x in values)
             and values == sorted(set(values)), "Malformed complete automatic CI " + field)
    need(refs(row["type"]) == row["typeRefs"], "Automatic CI full type refs differ")


def observed_owned_inventory(stage, pf, generated):
    path = stage / probe.base.INVENTORY_JSON
    doc = probe.base.read(path)
    finished = datetime.fromisoformat(pf["data"]["at_utc"]).timestamp()
    need(finished - pf["data"]["seconds"] - 2 <= path.stat().st_mtime <= finished + 2,
         "Actual generated six-CI inventory was outside original compiler interval")
    need(set(doc) == {"schemaVersion", "probeMainModule", "providerModule", "rawOwnedCIs"}
         and doc["schemaVersion"] == 1 and doc["probeMainModule"] == "GeneratedSnapshot"
         and doc["providerModule"] == probe.base.PLATFORM_MODULE,
         "Actual generated inventory envelope differs")
    rows = doc["rawOwnedCIs"]
    auto_names = probe.actual_auto_names()
    need([r["name"] for r in rows] == sorted(probe.base.NAMES + auto_names),
         "Additional unobserved generated CI was present")
    by_name = {r["resolvedName"]: r for r in generated}
    for row in rows:
        # The frozen generated inventory uses `owner`, not `actualOwner`.
        need(set(row) == (ROW_KEYS - {"actualOwner"}) | {"owner"}
             and row["owner"] == probe.base.PLATFORM_MODULE
             and row["privateUserName"] is None
             and row["closedType"] is True and row["closedValue"] is True,
             "Actual owned CI kind/closure/owner differs: " + row["name"])
        if row["name"] in probe.base.NAMES:
            primary = by_name[row["name"]]
            need(row["kind"] == "def" and row["isProp"] is False
                 and all(row[k] == primary[k] for k in ["levelParams", "type", "value", "axioms"])
                 and row["typeRefs"] == refs(row["type"])
                 and row["valueRefs"] == refs(row["value"]),
                 "Original full primary Def inventory/full CI differs: " + row["name"])
        else:
            need(row["name"] in auto_names and row["kind"] == "theorem"
                 and row["isProp"] is True and row["value"] is None
                 and row["axioms"] == ["propext"]
                 and not any(x.startswith("OAI.") for x in row["valueRefs"]),
                 "Observed auto CI is not a closed external-only Prop theorem")
            exact_refs(row)
    return doc


def written(path, pf):
    finished = datetime.fromisoformat(pf["data"]["at_utc"]).timestamp()
    need(path.is_file() and finished - pf["data"]["seconds"] - 2 <= path.stat().st_mtime <= finished + 2,
         "Source automatic CI JSON was not written in actual bounded compiler interval")
    return read(path)


def validate():
    probe.check_only()
    # Reuse all immutable original type/value/Std3/owner/context checks. Only
    # its final four-name raw inventory guard is adapted to six *observed* CIs.
    previous = original.owned_inventory
    original.owned_inventory = observed_owned_inventory
    try:
        first = original.validate("remainder")
    finally:
        original.owned_inventory = previous
    need(first["validated"] is True and first["Std3_only"] is True
         and first["provided_names"] == probe.base.NAMES
         and first["raw_equal_definition_count"] == 4
         and first["definition_values_equal_after_exact_inherited_closed_Prop_substitution"] is True
         and first["actual_owned_public_names"] == sorted(probe.base.NAMES + probe.actual_auto_names()),
         "Frozen original four-Def mathematical replay or observed-CI domain differs")
    pf = context.record(STAGE / probe.OUTPUT, STAGE / probe.MANIFEST,
                        "modecheck", Path(probe.OUTPUT).stem, STAGE)
    data = pf["data"]
    need(data["success"] is True and data["exit_code"] == 0
         and data["timed_out"] is False and 0 < data["seconds"] <= 300
         and data["timeout_seconds"] == 300 and data["mode"] == "modecheck"
         and data["output_olean"] is None and data["output_olean_sha256"] is None
         and "emit_olean" not in data,
         "Additional original-source automatic CI bounded modecheck did not pass")
    from certify_full_row_minor_node import imported_dep
    imported_dep(pf, probe.SOURCE_MODULE)
    source_doc = written(STAGE / probe.SOURCE_JSON, pf)
    need(set(source_doc) == {"schemaVersion", "probeMainModule", "sourceModule", "rawSourceAutomaticCIs"}
         and source_doc["schemaVersion"] == 1
         and source_doc["probeMainModule"] == Path(probe.OUTPUT).stem
         and source_doc["sourceModule"] == probe.SOURCE_MODULE,
         "Actual source automatic CI metadata envelope differs")
    source_rows = source_doc["rawSourceAutomaticCIs"]
    gen_doc = read(probe.base.STAGE / probe.base.INVENTORY_JSON)
    gen = {r["name"]: r for r in gen_doc["rawOwnedCIs"] if r["kind"] == "theorem"}
    names = probe.actual_auto_names()
    need([r["name"] for r in source_rows] == names and sorted(gen) == names,
         "Genuine source/generated automatic CI domains differ")
    pairs = []
    for left in source_rows:
        right = gen[left["name"]]
        need(set(left) == ROW_KEYS and left["actualOwner"] == probe.SOURCE_MODULE
             and left["privateUserName"] is None and left["kind"] == "theorem"
             and left["closedType"] is True and left["closedValue"] is True
             and left["isProp"] is True and left["value"] is None
             and right["owner"] == probe.base.PLATFORM_MODULE
             and right["closedType"] is True and right["closedValue"] is True
             and right["isProp"] is True and right["value"] is None,
             "Original/generated automatic CI is not a genuine closed owned Prop pair")
        exact_refs(left)
        exact_refs(right)
        need(all(left[k] == right[k] for k in
                 ["levelParams", "type", "typeRefs", "valueRefs", "axioms"])
             and set(left["axioms"]) <= STD3,
             "Two genuine automatic proof CIs differ in full type, direct refs or Std3: " + left["name"])
        pairs.append({"name": left["name"], "source_owner": left["actualOwner"],
                      "generated_owner": right["owner"],
                      "levelParams": left["levelParams"],
                      "full_type_sha256": probe.digest(encode(left["type"])),
                      "typeRefs": left["typeRefs"], "valueRefs": left["valueRefs"],
                      "axioms": left["axioms"], "closed_Prop": True,
                      "full_type_direct_refs_Std3_equal": True})
    return {"schema_version": 1,
            "artifact_kind": "ap19-analytic-remainder-four-Def-autoCI-derived-validation-v2",
            "validated": True, "Std3_only": True,
            "provided_names": probe.base.NAMES,
            "primary_Def_full_types_values_equal": True,
            "original_three_contexts_reused_unmodified": True,
            "actual_owned_CI_names": sorted(probe.base.NAMES + names),
            "actual_source_generated_closed_Prop_autoCI_pairs": pairs,
            "original_frozen_consumer": rel(Path(original.__file__)),
            "original_frozen_consumer_sha256": sha(Path(original.__file__)),
            "original_consumer_inventory_guard_rejected_two_observed_extra_CIs": True,
            "original_math_replay_sha256": probe.digest(encode(first)),
            "original_preflights": first["preflights"],
            "source_automatic_preflight": pf,
            "preparation_sha256": sha(STAGE / "preparation.json"),
            "manifest_sha256": sha(STAGE / probe.MANIFEST),
            "original_preparation_sha256": sha(probe.base.STAGE / "preparation.json"),
            "original_emitted_provider_olean": first["provider_olean"],
            "original_emitted_provider_olean_sha256": first["provider_olean_sha256"],
            "source_automatic_json_sha256": sha(STAGE / probe.SOURCE_JSON),
            "generated_owned_inventory_sha256": sha(probe.base.STAGE / probe.base.INVENTORY_JSON),
            "implementation_hashes": {rel(p): sha(p) for p in
                                      [SELF, probe.SELF, Path(original.__file__), Path(probe.base.__file__)]},
            "max_file_seconds": max(first["max_file_seconds"], data["seconds"]),
            "submission_ready": False, "proposal_status": "Draft",
            "Lean_started_by_consumer": False, "API_used": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--certify-existing", action="store_true")
    mode.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    report = validate()
    raw = encode(report)
    if CERT.exists():
        need(CERT.read_bytes() == raw, "Existing derived automatic CI certificate differs")
    elif args.certify_existing:
        CERT.write_bytes(raw)
    else:
        need(False, "Check-only requires an existing genuine derived certificate")
    print(json.dumps({"certificate": rel(CERT), "certificate_sha256": sha(CERT),
                      "validated": True, "Std3_only": True,
                      "paired_automatic_CIs": [r["name"] for r in report["actual_source_generated_closed_Prop_autoCI_pairs"]],
                      "max_file_seconds": report["max_file_seconds"],
                      "Lean_started_by_consumer": False, "API_used": False},
                     ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
