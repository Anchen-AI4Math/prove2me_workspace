"""Pure extra CI staging for the actual AP10 numeral-proof helper difference."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import stage_core_parent_data_providers as core

TASK, V = core.TASK, core.V
BASE = V / "ap10/determinant"
STAGE = BASE / "helper-pair"
SELF = Path(__file__).resolve()
TYPED = V / "TypedSnapshotCore.inc"
SOURCE_JSON = BASE / "source-full-ci.jsonl"
GENERATED_JSON = BASE / "generated-full-ci.jsonl"
SOURCE_HELPER = "OAI.PiExponent.DeterminantContradiction.collisionConstant._proof_1"
GENERATED_HELPER = "OAI.PiExponent.DeterminantContradiction.GlobalInterpolationStatement._proof_1"
SOURCE_MODULE = core.CONFIGS["determinant"]["source_module"]
GENERATED_MODULE = core.CONFIGS["determinant"]["platform_module"]
PARENTS = ["OAI.PiExponent.DeterminantContradiction.GlobalInterpolationStatement",
           "OAI.PiExponent.DeterminantContradiction.AnalyticAggregateStatement"]


def replace_constant(value):
    if isinstance(value, list):
        if value and value[0] == "const" and value[1] == SOURCE_HELPER:
            return [value[0], GENERATED_HELPER, value[2]]
        return [replace_constant(x) for x in value]
    return value


def refs(value):
    if isinstance(value, list):
        if value and value[0] == "const": yield value[1]
        for child in value: yield from refs(child)


def first_difference(left, right, path="$", ancestors=()):
    if type(left) != type(right): return {"path":path,"source":left,"generated":right}
    if isinstance(left,list):
        if len(left)!=len(right):return {"path":path,"source_length":len(left),"generated_length":len(right)}
        for i,(a,b) in enumerate(zip(left,right,strict=True)):
            if a!=b:return first_difference(a,b,path+f"[{i}]",ancestors+(left,))
    return {"path":path,"source":left,"generated":right}


def diagnosis():
    source=[json.loads(x) for x in SOURCE_JSON.read_text(encoding="utf-8").splitlines() if x.strip()]
    generated=[json.loads(x) for x in GENERATED_JSON.read_text(encoding="utf-8").splitlines() if x.strip()]
    names=core.config("determinant")["names"]
    core.need([x["resolvedName"] for x in source]==names and [x["resolvedName"] for x in generated]==names,"Actual14CI domain differs")
    rows=[]
    for left,right in zip(source,generated,strict=True):
        changed=[k for k in left if k!="sourceModule" and left[k]!=right[k]]
        core.need(changed==(["value"] if left["resolvedName"] in PARENTS else []),"Unexpected additional CI difference")
        core.need(replace_constant(left["value"])==right["value"],"Definition mismatch extends beyond the one actual numeral-proof helper pair")
        rows.append({"name":left["resolvedName"],"changed_fields":changed,
            "raw_types_equal":left["type"]==right["type"],"raw_values_equal":left["value"]==right["value"],
            "Std3_equal":left["axioms"]==right["axioms"],
            "first_difference":first_difference(left["value"],right["value"]) if changed else None,
            "source_only_constants":sorted(set(refs(left["value"]))-set(refs(right["value"]))),
            "generated_only_constants":sorted(set(refs(right["value"]))-set(refs(left["value"]))),
            "matches_after_unverified_actual_helper_pair_substitution":True})
    return {"schema_version":1,"artifact_kind":"ap10-determinant-actual-CI-difference-diagnosis",
        "source_json":core.rel(SOURCE_JSON),"source_json_sha256":core.sha(SOURCE_JSON),
        "generated_json":core.rel(GENERATED_JSON),"generated_json_sha256":core.sha(GENERATED_JSON),
        "source_helper":SOURCE_HELPER,"generated_helper":GENERATED_HELPER,
        "difference_is_numeral_instance_proof_argument":True,"14_rows":rows,
        "strict_consumer":"scripts/certify_core_parent_data_existing.py",
        "strict_consumer_sha256":core.sha(TASK/"scripts/certify_core_parent_data_existing.py"),
        "strict_consumer_original_failure_reported_by_root":"Source/generated kernel type, complete value or Std3 differs: OAI.PiExponent.DeterminantContradiction.GlobalInterpolationStatement",
        "helper_CI_pair_not_yet_validated":True,"validated":False,"API_used":False,"Lean_started":False}


PROBE = r'''
open Lean Meta
namespace DeterminantDataHelperPair

def refs (e : Expr) : Array Name :=
  (e.getUsedConstants).qsort (fun a b => a.toString < b.toString)

def valueOf (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo d => some d.value
  | .thmInfo t => some t.value
  | _ => none

def ownerOf (env : Environment) (n : Name) : MetaM String := do
  let some idx := env.getModuleIdxFor? n | throwError "Actual CI has no imported owner: {n}"
  let some owner := env.header.moduleNames[idx.toNat]? | throwError "Invalid imported owner: {n}"
  pure owner.toString

def exportPairSide (side output helper importModule : String) : MetaM Unit := do
  let env ← getEnv
  let name := helper.toName
  let some ci := env.find? name | throwError "Actual referenced helper CI is absent: {name}"
  let some value := valueOf ci | throwError "Actual helper has no value: {name}"
  if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars ||
     value.hasMVar || value.hasFVar || value.hasLooseBVars then
    throwError "Actual helper type/value is not closed"
  unless (← isProp ci.type) do throwError "Differing numeral helper is not a proof of a proposition"
  unless (← ownerOf env name) == importModule do throwError "Actual helper has wrong module owner"
  let axioms ← Lean.collectAxioms name
  unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
    throwError "Actual helper uses axioms outside Std3"
  let mut parents : Array Json := #[]
  for n in #[`OAI.PiExponent.DeterminantContradiction.GlobalInterpolationStatement,
             `OAI.PiExponent.DeterminantContradiction.AnalyticAggregateStatement] do
    let some parent := env.find? n | throwError "Actual parent is missing"
    let some parentValue := valueOf parent | throwError "Actual parent has no value"
    unless (refs parentValue).contains name do throwError "Parent does not actually use the helper"
    parents := parents.push <| Json.mkObj [("name", toJson n.toString),
      ("owner", toJson (← ownerOf env n)),
      ("valueRefs", toJson ((refs parentValue).map Name.toString))]
  let kind := match ci with | .thmInfo _ => "theorem" | .defnInfo _ => "def" | _ => "other"
  let pretty ← ppExpr ci.type
  let row := Json.mkObj [("name", toJson name.toString), ("kind", toJson kind),
    ("levelParams", toJson (ci.levelParams.map Name.toString)),
    ("closedType", toJson true), ("closedValue", toJson true), ("isProp", toJson true),
    ("type", PiExponentInterfaceSnapshot.exprJson ci.type),
    ("value", PiExponentInterfaceSnapshot.exprJson value),
    ("prettyType", toJson pretty.pretty),
    ("typeRefs", toJson ((refs ci.type).map Name.toString)),
    ("valueRefs", toJson ((refs value).map Name.toString)),
    ("axioms", toJson ((axioms.map Name.toString).qsort (fun a b => a < b))),
    ("owner", toJson (← ownerOf env name))]
  let report := Json.mkObj [("schemaVersion", toJson (1 : Nat)), ("side", toJson side),
    ("probeMainModule", toJson env.mainModule.toString), ("importModule", toJson importModule),
    ("helper", row), ("actualParentReferences", Json.arr parents)]
  IO.FS.writeFile output report.compress
end DeterminantDataHelperPair
'''


def stage_files():
    d=diagnosis();outputs={"difference-diagnosis.json":core.encode(d)}
    pins={core.rel(p):core.sha(p) for p in [SELF,SOURCE_JSON,GENERATED_JSON,TYPED,TASK/"scripts/certify_core_parent_data_existing.py",BASE/"preparation.json",BASE/"c1.json",BASE/"c2.json",BASE/"c3.json"]}
    for i,(side,helper,module) in enumerate([("source",SOURCE_HELPER,SOURCE_MODULE),("generated",GENERATED_HELPER,GENERATED_MODULE)],1):
        filename="HelperPair"+side.capitalize()+".lean";out=STAGE/(side+"-helper.json")
        raw=("import Lean\nimport "+module+"\n\n"+TYPED.read_text(encoding="utf-8").rstrip()+"\n\n"+PROBE+
             "\nrun_meta do\n  DeterminantDataHelperPair.exportPairSide "+" ".join(json.dumps(x) for x in [side,core.workspace_rel(out),helper,module])+"\n#print axioms "+helper+"\n").encode()
        outputs[filename]=raw
        outputs[f"c{i}.json"]=core.encode({"schema_version":1,"artifact_kind":"ap10-actual-helper-pair-bounded-manifest",
            "output":core.workspace_rel(STAGE/filename),"output_sha256":core.sha_bytes(raw),
            "imports":["Lean",module],"input_hashes":pins,"runtime_sha256":core.sha(core.ap9.RUNTIME),
            "mode":"modecheck","emit_olean":False,"timeout_seconds":300,"validated":False,"submission_ready":False})
    outputs["preparation.json"]=core.encode({"schema_version":1,"artifact_kind":"ap10-actual-helper-pair-preparation",
        "source_helper":SOURCE_HELPER,"generated_helper":GENERATED_HELPER,"source_module":SOURCE_MODULE,"generated_module":GENERATED_MODULE,
        "input_hashes":pins,"source_commit":core.COMMIT,"bounded_probe_count":2,
        "commands":["python scripts/preflight_staged_module.py ap10/determinant/helper-pair/HelperPairSource.lean --root ap10/determinant/helper-pair --imports-manifest ap10/determinant/helper-pair/c1.json --timeout-seconds 300",
                    "python scripts/preflight_staged_module.py ap10/determinant/helper-pair/HelperPairGenerated.lean --root ap10/determinant/helper-pair --imports-manifest ap10/determinant/helper-pair/c2.json --timeout-seconds 300"],
        "API_used":False,"Lean_started":False,"validated":False,"submission_ready":False})
    return outputs


def main():
    p=argparse.ArgumentParser(description=__doc__);m=p.add_mutually_exclusive_group(required=True);m.add_argument("--prepare",action="store_true");m.add_argument("--check-only",action="store_true");a=p.parse_args();outputs=stage_files()
    for name,raw in outputs.items():
        path=STAGE/name
        if path.exists():core.need(path.read_bytes()==raw,"Immutable extra-CI stage differs: "+name)
        elif a.prepare:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(raw)
        else:raise ValueError("Extra-CI stage missing: "+name)
    print(json.dumps({"prepared":a.prepare,"checked_files":len(outputs),"helper_pair_domain":2,"Lean_started":False,"API_used":False}))


if __name__=="__main__":main()
