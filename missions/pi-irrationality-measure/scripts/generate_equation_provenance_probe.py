"""Stage a paired authoritative equation API provenance probe; no Lean/network.

The pair is evidence construction only. It grants no new generated-command
owner and must not be used by the provider node generator until certified.
"""
import hashlib
import json
from pathlib import Path

from generate_independent_node import runtime_pin
from generate_platform_bundles import bundle_module

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
STAGE = TASK / "verification/equation-provenance-probe"
MODULE = "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation"
PRIMARY = "OAI.PiExponent.FormalLogTruncation.shiftMap"
REQUIRED = "OAI.PiExponent.FormalLogTruncation.shiftMap.eq_1"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


PROBE = r'''
namespace PiExponentEquationProvenanceProbe
open Lean Meta

def ownership (env : Environment) (name : Name) : Json :=
  match env.getModuleIdxFor? name with
  | some idx => Json.mkObj [
      ("kind", toJson "ImportedModule"), ("index", toJson idx.toNat),
      ("module", toJson (env.header.moduleNames[idx.toNat]?.map Name.toString))]
  | none => Json.mkObj [("kind", toJson "OwnModule"), ("module", toJson env.mainModule.toString)]

def checkedCI (name : Name) : MetaM Json := do
  let ci ← getConstInfo name
  if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars then
    throwError "Equation probe type is not closed: {name}"
  let value := match ci with
    | .defnInfo d => some d.value
    | _ => none
  if value.any (fun e => e.hasMVar || e.hasFVar || e.hasLooseBVars) then
    throwError "Equation probe definition value is not closed: {name}"
  let kind ← match ci with
    | .defnInfo _ => pure "def"
    | .thmInfo _ => pure "theorem"
    | _ => throwError "Equation probe found unsupported constant kind: {name}"
  let axioms ← collectAxioms name
  unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
    throwError "Equation probe nonstandard axiom: {name}"
  return Json.mkObj [
    ("actualName", toJson name.toString),
    ("userName", toJson (privateToUserName name).toString),
    ("levelParams", toJson (ci.levelParams.map Name.toString)),
    ("kind", toJson kind),
    ("type", PiExponentInterfaceSnapshot.exprJson ci.type),
    ("value", value.map PiExponentInterfaceSnapshot.exprJson |>.getD Json.null),
    ("owner", ownership (← getEnv) name),
    ("axioms", toJson (axioms.map Name.toString))]

def exportEquationSnapshot (primary : Name) (expectedModule output side : String) : MetaM Unit := do
  let envBefore ← getEnv
  let ci ← getConstInfo primary
  match ci with
  | .defnInfo _ => pure ()
  | _ => throwError "Primary source binding is not a definition"
  let some idx := envBefore.getModuleIdxFor? primary
    | throwError "Primary must belong to the imported source/provider module"
  unless envBefore.header.moduleNames[idx.toNat]?.map Name.toString == some expectedModule do
    throwError "Primary binding belongs to an unexpected module"
  let equations? ← Lean.Meta.getEqnsFor? primary
  let unfolding? ← Lean.Meta.getUnfoldEqnFor? primary
  let mut equations : Array Json := #[]
  for name in equations?.getD #[] do
    let parent? ← Lean.Meta.isEqnThm? name
    unless parent? == some primary do
      throwError "getEqnsFor? result lacks its exact inverse primary relation: {name}"
    equations := equations.push <| Json.mkObj [
      ("getter", toJson "Lean.Meta.getEqnsFor?"),
      ("inversePrimary", toJson (parent?.map Name.toString)),
      ("CI", ← checkedCI name)]
  let unfolding ← match unfolding? with
    | some name => pure <| Json.mkObj [
        ("getter", toJson "Lean.Meta.getUnfoldEqnFor?"), ("CI", ← checkedCI name)]
    | none => pure Json.null
  let result := Json.mkObj [
    ("side", toJson side), ("expectedModule", toJson expectedModule),
    ("primaryBinding", ← checkedCI primary),
    ("getEqnsForReturnedSome", toJson equations?.isSome),
    ("actualEquationNames", toJson (equations?.map (·.map Name.toString))),
    ("equations", Json.arr equations), ("unfolding", unfolding),
    ("probeMainModule", toJson (← getEnv).mainModule.toString),
    ("theoremProofValuesExported", toJson false)]
  IO.FS.writeFile output result.compress

end PiExponentEquationProvenanceProbe
'''


def main():
    STAGE.mkdir(parents=True, exist_ok=True)
    core_path = TASK / "verification/TypeOnlyTheoremSnapshotCore.inc"
    core = core_path.read_text(encoding="utf-8")
    runtime = json.loads((TASK / "verification/lean-runtime.json").read_text(encoding="utf-8"))
    lean_src = Path(runtime["executable"]).parent.parent / "src/lean/Lean"
    apis = [lean_src / p for p in ["Meta/Eqns.lean", "Environment.lean", "PrivateName.lean", "Util/CollectAxioms.lean"]]
    plan_path = TASK / "verification/provider-plans/all-shared-public/platform-unit-plan-provider-variant.json"
    plan = json.loads(plan_path.read_text(encoding="utf-8"))
    owners = [u for u in plan["units"] if PRIMARY in u["graph_names"]]
    if len(owners) != 1 or owners[0]["module"] != MODULE or owners[0]["category"] not in {"definition", "definition_embedded"}:
        raise ValueError("Primary has no unique planned proved Definition command")
    source_path = TASK / "port/lean" / (MODULE.replace(".","/")+".lean")
    original_path = TASK / "source/lean" / (MODULE.replace(".","/")+".lean")
    state = json.loads((TASK/"verification/extraction-state.json").read_text(encoding="utf-8"))
    facts_entry = state["stage2"][MODULE.replace(".","/")+".lean"]
    facts_path = ROOT/facts_entry["facts"]
    if sha(facts_path) != facts_entry["facts_sha256"] or sha(source_path) != owners[0]["source_sha256"]:
        raise ValueError("Primary source/AST witness differs from the provider plan")
    generated_module = bundle_module(MODULE)
    outputs = {}
    for side, module in (("original",MODULE),("generated",generated_module)):
        output = (STAGE/(side+".json")).relative_to(ROOT).as_posix()
        text = "import Lean\nimport Lean.Meta.Eqns\nimport " + module + "\n\n" + core + PROBE + (
            "\nrun_meta do\n  PiExponentEquationProvenanceProbe.exportEquationSnapshot `" + PRIMARY + " " +
            json.dumps(module) + " " + json.dumps(output) + " " + json.dumps(side) + "\n")
        path = STAGE/("Probe"+side.title()+".lean")
        path.write_bytes(text.encode("utf-8"))
        outputs[path.name] = sha(path)
    pins = {p.relative_to(TASK).as_posix():sha(p) for p in [plan_path, core_path,
            TASK/"verification/TypeOnlyTheoremSnapshotCore.lineage.json",
            TASK/"verification/decl_graph.jsonl",TASK/"verification/lean-runtime.json",
            TASK/"scripts/generate_equation_provenance_probe.py",source_path,original_path]}
    pins[facts_path.relative_to(TASK).as_posix()] = sha(facts_path)
    graph_rows = []
    for line in (TASK/"verification/decl_graph.jsonl").read_bytes().splitlines():
        row = json.loads(line)
        if row["name"] in {PRIMARY,REQUIRED}:
            graph_rows.append({"row":row,"row_sha256":hashlib.sha256(line).hexdigest()})
    manifest = {"schema_version":1,"primary_binding":PRIMARY,"required_equation":REQUIRED,
        "source_module":MODULE,"generated_module":generated_module,"primary_source_unit":owners[0],
        "primary_facts":facts_path.relative_to(ROOT).as_posix(),"primary_facts_sha256":sha(facts_path),
        "graph_rows":graph_rows,"input_hashes":pins,"runtime_sha256":runtime_pin(),
        "pinned_lean_api_source_hashes":{str(p):sha(p) for p in apis},"outputs_sha256":outputs,
        "source_witness_commit":"adc7f1241b42e322a6451854ab7e4b4c146bf78a",
        "snapshot_exporter_theorem_value":"null","metadata_cache_untouched":True,
        "provisional":True,"validated":False,"provider_availability_established":False,
        "submission_ready":False,"lean_started":False,"api_used":False,
        "before_compilation_required":["hold extractor and strictly recheck all captured input hashes",
            "generated Def imports actual certified provider OLeans; no stubs",
            "pin exact generated Def source/OLean/certificate and its full dependency closure"],
        "certification_policy":["both exact probe files compile individually within 300 seconds; pin records and logSHAs",
            "original getEqnsFor? actually returns required Graph equation and exact inversePrimary primary binding",
            "generated getter actually returns matching equation via primary source binding",
            "primary CI type and complete Def value match with only certified naming/universe correspondence",
            "equation CI kind, closed kernel type, universe binders and Std3 match using API names",
            "record equation owners as observed, including lazily realized OwnModule equations; do not infer owner from spelling",
            "certified API primary relationship plus proven same Def body establishes available generated equation",
            "do not update provider/global planner or infer prefix-based equation ownership from this uncompiled plan"]}
    (STAGE/"probe-plan.json").write_text(json.dumps(manifest,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({"stage":STAGE.relative_to(TASK).as_posix(),"files":outputs,
                      "validated":False,"provider_availability_established":False}))


if __name__ == "__main__":
    main()
