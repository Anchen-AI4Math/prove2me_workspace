"""Bounded AP10 determinant adapter: one actually certified proof-CI pair.

The frozen ordinary consumer and original snapshot bytes remain unchanged. Its
complete checks are replayed after exactly one in-memory proof-name substitution,
only in two known definition values, once the actual helper CIs have equal closed
propositional types and bounded source/generated witnesses.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import certify_core_parent_data_existing as ordinary
import stage_determinant_data_helper_pair as pair
import validate_namespace_context_providers as context
from certify_command_emission_probe import checked_expr

SELF = Path(__file__).resolve()
CERT = pair.BASE / "actual-provider-validation-helper-v2.json"
FAILURE = pair.STAGE / "strict-consumer-replay-failure.log"
STD3 = {"propext", "Classical.choice", "Quot.sound"}
HELPER_FIELDS = {"name","kind","levelParams","closedType","closedValue","isProp",
                 "type","value","prettyType","typeRefs","valueRefs","axioms","owner"}


def helper_pair():
    generated=pair.stage_files()
    for name,raw in generated.items():
        pair.core.need((pair.STAGE/name).read_bytes()==raw,"Exact extra-CI stage changed: "+name)
    sides={}
    for i,(side,name,module) in enumerate([
            ("source",pair.SOURCE_HELPER,pair.SOURCE_MODULE),
            ("generated",pair.GENERATED_HELPER,pair.GENERATED_MODULE)],1):
        filename="HelperPair"+side.capitalize()+".lean"
        rec=context.record(pair.STAGE/filename,pair.STAGE/f"c{i}.json","modecheck",Path(filename).stem,pair.STAGE)
        data=rec["data"]
        pair.core.need(data["success"] and data["exit_code"]==0 and not data["timed_out"]
            and 0<data["seconds"]<=300 and data["timeout_seconds"]==300
            and data["output_olean"] is None and data["output_olean_sha256"] is None,
            "Actual helper probe did not pass within budget")
        path=pair.STAGE/(side+"-helper.json")
        report=pair.core.read(path)
        from datetime import datetime
        end=datetime.fromisoformat(data["at_utc"]).timestamp()
        pair.core.need(end-data["seconds"]-2<=path.stat().st_mtime<=end+2,"Helper JSON outside actual compiler interval")
        pair.core.need(set(report)=={"schemaVersion","side","probeMainModule","importModule","helper","actualParentReferences"}
            and report["schemaVersion"]==1 and report["side"]==side
            and report["probeMainModule"]==Path(filename).stem and report["importModule"]==module,
            "Actual helper report identity/schema differs")
        ci=report["helper"]
        pair.core.need(set(ci)==HELPER_FIELDS and ci["name"]==name and ci["owner"]==module
            and ci["kind"] in {"theorem","def"} and ci["closedType"] is True and ci["closedValue"] is True
            and ci["isProp"] is True and ci["value"] is not None,"Actual helper is not an owned closed proof CI")
        levels=ci["levelParams"]
        pair.core.need(isinstance(levels,list) and len(levels)==len(set(levels)) and all(isinstance(x,str) for x in levels),"Helper universe domain differs")
        checked_expr(ci["type"],set(levels));checked_expr(ci["value"],set(levels))
        for key,expr in [("typeRefs",ci["type"]),("valueRefs",ci["value"])]:
            pair.core.need(ci[key]==sorted(set(pair.refs(expr))),"Actual helper references do not match its full CI")
        pair.core.need(ci["axioms"]==sorted(set(ci["axioms"])) and set(ci["axioms"])<=STD3,"Actual helper has nonstandard axioms")
        parents=report["actualParentReferences"]
        pair.core.need([x["name"] for x in parents]==pair.PARENTS,"Actual helper parent reference domain differs")
        for parent in parents:
            pair.core.need(set(parent)=={"name","owner","valueRefs"} and parent["owner"]==module
                and name in parent["valueRefs"] and parent["valueRefs"]==sorted(set(parent["valueRefs"])),"Helper is not actually used by its parent")
        sides[side]={"preflight":rec,"actual_report":report,"output":pair.core.rel(path),"output_sha256":pair.core.sha(path)}
    source=sides["source"]["actual_report"]["helper"]; target=sides["generated"]["actual_report"]["helper"]
    pair.core.need(source["levelParams"]==target["levelParams"] and source["type"]==target["type"],
                   "Paired actual proof CI types are not identical")
    pair.core.need(source["axioms"]==target["axioms"],"Paired actual helper axioms differ")
    return {"source_name":pair.SOURCE_HELPER,"generated_name":pair.GENERATED_HELPER,
            "actual_closed_propositional_types_equal":True,"actual_full_proof_values_equal":source["value"]==target["value"],
            "basis":"identical actual closed proof CI types, checked as propositions by Lean; kernel proof irrelevance permits the unique proof-name substitution",
            "actual_witnesses":sides}


def validate():
    proof_pair=helper_pair(); pair.diagnosis()
    old_rows=ordinary.rows; substituted=[]
    def bounded_rows(path,record,count):
        rows=old_rows(path,record,count)
        if Path(path).resolve()==pair.SOURCE_JSON.resolve():
            for row in rows:
                if row["resolvedName"] in pair.PARENTS:
                    before=row["value"];after=pair.replace_constant(before)
                    pair.core.need(before!=after,"Expected actual proof helper difference absent")
                    row["value"]=after;substituted.append(row["resolvedName"])
        return rows
    try:
        ordinary.rows=bounded_rows
        result=ordinary.validate("determinant")
    finally:
        ordinary.rows=old_rows
    pair.core.need(substituted==pair.PARENTS,"Substitution exceeded its fixed two-parent domain")
    result["artifact_kind"]="ap10-determinant-certified-proof-helper-provider-validation"
    result.pop("definition_values_equal_and_exported")
    result.update({"raw_definition_values_equal":False,
        "definition_values_equal_after_certified_proof_CI_substitution":True,
        "raw_equal_definition_count":12,"changed_only_by_actual_proof_helper":pair.PARENTS,
        "certified_actual_helper_pair":proof_pair,
        "original_source_and_generated_snapshot_bytes_preserved":True,
        "ordinary_consumer_path":pair.core.rel(Path(ordinary.__file__)),
        "ordinary_consumer_sha256":pair.core.sha(Path(ordinary.__file__)),
        "difference_diagnosis":pair.core.rel(pair.STAGE/"difference-diagnosis.json"),
        "difference_diagnosis_sha256":pair.core.sha(pair.STAGE/"difference-diagnosis.json"),
        "normalization_domain":{"constant_pairs":1,"parent_values":2,"types_modified":False,"source_files_modified":False},
        "max_file_seconds":max(result["max_file_seconds"],*(x["preflight"]["data"]["seconds"] for x in proof_pair["actual_witnesses"].values())),
        "consumer":pair.core.rel(SELF),"consumer_sha256":pair.core.sha(SELF)})
    result["implementation_hashes"].update({pair.core.rel(x):pair.core.sha(x) for x in [SELF,Path(pair.__file__),pair.TYPED]})
    if FAILURE.exists():result["preserved_strict_consumer_failure"]={"path":pair.core.rel(FAILURE),"sha256":pair.core.sha(FAILURE)}
    return result


def main():
    p=argparse.ArgumentParser(description=__doc__);m=p.add_mutually_exclusive_group(required=True)
    m.add_argument("--certify-existing",action="store_true");m.add_argument("--check-only",action="store_true");a=p.parse_args()
    report=validate();raw=pair.core.encode(report)
    if CERT.exists():pair.core.need(CERT.read_bytes()==raw,"Existing helper certificate differs; refusing overwrite")
    elif a.certify_existing:CERT.write_bytes(raw)
    print(json.dumps({"certificate":pair.core.rel(CERT),"validated":True,
        "raw_equal_defs":12,"proof_helper_normalized_defs":2,
        "actual_full_helper_values_equal":report["certified_actual_helper_pair"]["actual_full_proof_values_equal"],
        "Std3_only":True,"max_file_seconds":report["max_file_seconds"],"Lean_started":False,"API_used":False}))


if __name__=="__main__":main()
