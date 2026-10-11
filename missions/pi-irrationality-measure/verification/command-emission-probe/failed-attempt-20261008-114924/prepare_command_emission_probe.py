"""Prepare exact-command environment-delta provenance without Lean/network.

The original parser prefix is copied byte-for-byte, imports are augmented only
for the probe instrumentation. The command's emitted constants are established
by an actual Name-set delta in the future compiler, never by a prefix heuristic.
This isolated script does not modify SketchOracle or extraction caches.
"""
import hashlib
import json
from pathlib import Path

from generate_independent_node import runtime_pin

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
STAGE = TASK / "verification/command-emission-probe"
MODULE = "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer"
START = 797


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


EXPORTER = r'''
namespace PiExponentCommandEmissionProbe
open Lean Meta

def owner (env : Environment) (name : Name) : Json :=
  match env.getModuleIdxFor? name with
  | some idx => Json.mkObj [
      ("kind", toJson "ImportedModule"), ("moduleIndex", toJson idx.toNat),
      ("module", toJson (env.header.moduleNames[idx.toNat]?.map Name.toString))]
  | none => Json.mkObj [("kind", toJson "OwnModule"), ("module", toJson env.mainModule.toString)]

def checkedCI (name : Name) : MetaM Json := do
  let ci ← getConstInfo name
  if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars then
    throwError "Command probe CI type is not closed: {name}"
  let (kind, value, safety) ← match ci with
    | .defnInfo d => pure ("def", some d.value, toJson (reprStr d.safety))
    | .thmInfo t => do
      if t.value.hasMVar || t.value.hasFVar || t.value.hasLooseBVars then
        throwError "Command probe theorem proof is not closed: {name}"
      pure ("theorem", none, Json.null)
    | _ => throwError "Command probe unsupported emitted CI kind: {name}"
  if value.any (fun e => e.hasMVar || e.hasFVar || e.hasLooseBVars) then
    throwError "Command probe CI value is not closed: {name}"
  let axioms ← collectAxioms name
  unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
    throwError "Command probe CI has nonstandard axioms: {name}"
  return Json.mkObj [
    ("actualName", toJson name.toString),
    ("privateUserName", toJson (privateToUserName? name |>.map Name.toString)),
    ("kind", toJson kind), ("safety", safety),
    ("levelParams", toJson (ci.levelParams.map Name.toString)),
    ("type", PiExponentInterfaceSnapshot.exprJson ci.type),
    ("value", value.map PiExponentInterfaceSnapshot.exprJson |>.getD Json.null),
    ("typeRefs", toJson (ci.type.getUsedConstants.map Name.toString)),
    ("valueRefs", toJson (value.map Expr.getUsedConstants |>.getD #[] |>.map Name.toString)),
    ("owner", owner (← getEnv) name),
    ("axioms", toJson (axioms.map Name.toString))]

def after (beforeNames : Std.HashSet Name)
    (expectedUser sourceCommandSHA sourceModule output : String) : MetaM Unit := do
  let env ← getEnv
  -- Compare actual Lean.Name values, not printed suffixes or private counters.
  let delta := env.constants.toList.filterMap fun (name, _) =>
    if beforeNames.contains name then none else some name
  let primary := delta.filter fun name =>
    ((privateToUserName? name).map Name.toString) == some expectedUser
  unless primary.length == 1 do
    throwError "Exact command did not emit one actual primary private binding"
  let mut rows : Array Json := #[]
  for name in delta do
    unless (env.getModuleIdxFor? name).isNone do
      throwError "Exact command delta contains an imported constant"
    rows := rows.push (← checkedCI name)
  let result := Json.mkObj [
    ("association", toJson "exact-parser-command-env-Name-set-delta"),
    ("sourceModule", toJson sourceModule), ("sourceCommandSHA256", toJson sourceCommandSHA),
    ("primaryActualName", toJson primary.head!.toString),
    ("primaryExpectedUserName", toJson expectedUser),
    ("beforeNameCount", toJson beforeNames.size),
    ("afterNameCount", toJson env.constants.toList.length),
    ("actualEmittedNames", toJson (delta.map Name.toString)),
    ("rows", Json.arr rows), ("probeMainModule", toJson env.mainModule.toString),
    ("theoremProofValuesExported", toJson false)]
  IO.FS.writeFile output result.compress

def sourceSnapshot (requests : Array (String × String)) (output : String) : MetaM Unit := do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for (graphName, expectedModule) in requests do
    let names := env.constants.toList.filterMap fun (name, _) =>
      if name.toString == graphName then some name else none
    unless names.length == 1 do
      throwError "Graph name does not select one original actual CI: {graphName}"
    let actualName := names.head!
    let some idx := env.getModuleIdxFor? actualName | throwError "Original CI is not imported"
    unless (env.header.moduleNames[idx.toNat]?.map Name.toString) == some expectedModule do
      throwError "Original actual CI owner differs from the graph module"
    rows := rows.push (← checkedCI actualName)
  IO.FS.writeFile output (Json.arr rows |>.compress)

end PiExponentCommandEmissionProbe
'''


def context_closure_audit(inventory, state, graph, scopes):
    """List private ordinary defs needed by retained syntax context, not kernel.

    These are candidates for command provenance, never automatic promotions.
    Authority is the exact same-file binding ref plus raw command inventory.
    """
    v = TASK/"verification"
    plan_path = v/"provider-plans/all-shared-public/platform-unit-plan-provider-variant.json"
    artifacts_path = v/"provider-plans/all-shared-public/platform-artifact-plan-provider-variant.json"
    plan = json.loads(plan_path.read_text(encoding="utf-8"))
    artifacts = json.loads(artifacts_path.read_text(encoding="utf-8"))
    units = {u["id"]:u for u in plan["units"]}
    modules = {m["module"]:m for m in inventory["modules"]}
    raw_owner = {n:(m["module"],u) for m in inventory["modules"] for u in m["units"] for n in u["graph_names"]}
    scope_modules = {m["source"].removesuffix(".lean").replace("/","."):m for m in scopes["modules"]}
    cache,facts_pins = {},{}
    for name in {m for node in artifacts["nodes"].values() for m in node["source_components"]}:
        entry = state["stage2"][name.replace(".","/")+".lean"]
        path = ROOT/entry["facts"]
        if sha(path)!=entry["facts_sha256"]:
            raise ValueError("Context audit AST facts changed: "+name)
        facts_pins[entry["facts"]] = sha(path)
        fs = [json.loads(l) for l in path.read_bytes().splitlines()]
        contexts = [f["syntax"]["range"] for f in fs if f["kind"]=="command" and not f["isDeclaration"]]
        refs = [f for f in fs if f["kind"]=="ref"]
        local_bindings = {}
        for u in modules[name]["units"]:
            if not u["nameRange"] or len(u["graph_names"])!=1:
                continue
            b = u["nameRange"]
            identities = {r["const"] for r in refs if r["start"]==b["start"] and r["end"]==b["end"]}
            if len(identities)==1:
                identity = next(iter(identities))
                if identity in local_bindings and local_bindings[identity]!=u["graph_names"][0]:
                    raise ValueError("Context audit same-file binding identity is ambiguous")
                local_bindings[identity] = u["graph_names"][0]
        cache[name] = (contexts,refs,local_bindings)
    findings = []
    for key,node in artifacts["nodes"].items():
        definition_modules,todo = set(),list(node["definition_modules"])
        while todo:
            name=todo.pop()
            if name in definition_modules:
                continue
            definition_modules.add(name)
            if name in artifacts["definition_bundles"]:
                todo.extend(artifacts["definition_bundles"][name]["imports"])
        available = {n for u in units.values() if u["module"] in definition_modules and u["category"] in {"definition","definition_embedded"} for n in u["graph_names"]}
        available.update(n for u in node["inline_units"]+node["node_dependencies"]+[key] for n in units[u]["graph_names"])
        target_scope = next(d for d in scope_modules[units[key]["module"]]["declarations"] if d["range"]["start"]==units[key]["start"])
        for name in node["source_components"]:
            contexts,refs,bindings = cache[name]
            for ref in refs:
                a,b = ref["start"]["offset"],ref["end"]["offset"]
                parent = [s for s in contexts if s["start"]["offset"]<=a<=b<=s["end"]["offset"]]
                if len(parent)!=1:
                    continue
                constant = bindings.get(ref["const"],ref["const"])
                row = graph.get(constant)
                if not row or constant in available or not row["isPrivate"] or row["kind"]!="def" or constant not in raw_owner:
                    continue
                owner_module,u = raw_owner[constant]
                if owner_module!=name or u["is_instance_command"] or u["graph_kinds"]!=["def"] or len(u["graph_names"])!=1:
                    continue
                active = name==units[key]["module"] and any(s["range"]==parent[0] for s in target_scope["context_commands"])
                findings.append({"node":key,"node_theorem_name":node["theorem_name_before_platform_renames"],
                    "source_component":name,"context_command_range":parent[0],"reference_range":{"start":ref["start"],"end":ref["end"]},
                    "referenced_graph_name":constant,"private_definition_unit":name+":"+str(u["start"]["offset"]),
                    "private_definition_range":{"start":u["start"],"end":u["end"]},"active_target_context":active,
                    "unowned_direct_project_dependencies":[n for n in row["typeDeps"]+row["valueDeps"]+row["constructors"] if n in graph and n not in raw_owner],
                    "proposed_action":"exact-command emission provenance, then reviewed context/private closure or rejection",
                    "classification_changed":False})
    report = {"nodes_considered":len(artifacts["nodes"]),"contexts_needing_private_definition_closure":findings,
        "distinct_nodes":len({r["node"] for r in findings}),"distinct_private_def_commands":len({r["private_definition_unit"] for r in findings}),
        "input_hashes":{p.relative_to(TASK).as_posix():sha(p) for p in [plan_path,artifacts_path,v/"ast-unit-inventory.json",v/"ast-scope-inventory.json",v/"decl_graph.jsonl"]},
        "facts_input_hashes":facts_pins,"actual_implementation_ready":False,"validated":False,"submission_ready":False,
        "lean_started":False,"api_used":False}
    (STAGE/"source-node-context-closure-cases.json").write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
    return {k:report[k] for k in ["nodes_considered","distinct_nodes","distinct_private_def_commands"]}


def main():
    runtime_sha = runtime_pin()
    v = TASK / "verification"
    inventory_path, graph_path = v/"ast-unit-inventory.json",v/"decl_graph.jsonl"
    inventory = json.loads(inventory_path.read_text(encoding="utf-8"))
    module = next(m for m in inventory["modules"] if m["module"] == MODULE)
    selected = [u for u in module["units"] if u["start"]["offset"] == START]
    if len(selected)!=1:
        raise ValueError("Probe requires one exact AST command unit")
    unit = selected[0]
    if unit["graph_kinds"] != ["def"] or len(unit["graph_names"])!=1 or not unit["privateTok"] or unit["is_instance_command"]:
        raise ValueError("This first command probe supports one source-private ordinary def/abbrev")
    source = TASK/"port/lean"/(MODULE.replace(".","/")+".lean")
    original = TASK/"source/lean"/(MODULE.replace(".","/")+".lean")
    raw = source.read_bytes()
    if sha(source)!=module["source_sha256"]:
        raise ValueError("Source differs from authoritative AST command inventory")
    state = json.loads((v/"extraction-state.json").read_text(encoding="utf-8"))
    entry = state["stage2"][MODULE.replace(".","/")+".lean"]
    facts_path = ROOT/entry["facts"]
    if sha(facts_path)!=entry["facts_sha256"]:
        raise ValueError("Command probe source facts changed")
    facts = [json.loads(line) for line in facts_path.read_bytes().splitlines()]
    commands = [f for f in facts if f["kind"]=="command"]
    exact = [f for f in commands if f["isDeclaration"] and f["syntax"]["range"]=={"start":unit["start"],"end":unit["end"]}]
    if len(exact)!=1:
        raise ValueError("Source command unit differs from parser authority")
    first = min(f["syntax"]["range"]["start"]["offset"] for f in commands)
    a,b = unit["start"]["offset"],unit["end"]["offset"]
    graph = {r["name"]:r for r in (json.loads(l) for l in graph_path.read_bytes().splitlines())}
    primary = graph[unit["graph_names"][0]]
    scopes_path = v/"ast-scope-inventory.json"
    scopes = json.loads(scopes_path.read_text(encoding="utf-8"))
    scope = next(d for m in scopes["modules"] if m["source"]==MODULE.replace(".","/")+".lean"
                 for d in m["declarations"] if d["range"]["start"]==unit["start"])
    if scope["verified_name"]!=primary["userName"]:
        raise ValueError("Command primary binding differs from its full source namespace")
    # Source prefix contains whole commands only; every original scope is closed
    # after the probe. No future command or altered source statement is copied.
    prefix_commands = [f for f in commands if f["syntax"]["range"]["start"]["offset"]<a]
    if any(f["syntax"]["range"]["end"]["offset"]>a for f in prefix_commands):
        raise ValueError("Copied source prefix cuts an original command")
    closing = "\n"+"\n".join("end" for _ in scope["scope_stack"])+"\n"
    core_path = v/"TypeOnlyTheoremSnapshotCore.inc"
    core = core_path.read_text(encoding="utf-8")
    STAGE.mkdir(parents=True,exist_ok=True)
    command_sha = hashlib.sha256(raw[a:b]).hexdigest()
    output = (STAGE/"command-emitted.json").relative_to(ROOT).as_posix()
    text = "import Lean\n"+raw[:first].decode("utf-8")+"\n"+core+EXPORTER+raw[first:a].decode("utf-8")
    command_text = raw[a:b].decode("utf-8")
    # Parse and elaborate one exact command inside one action. The baseline is
    # an ordinary local value, not an initialized declaration in this module.
    # Runtime parsing avoids quotation hygiene changing the original binding.
    text += "\nrun_cmd do\n  let envBefore ← Lean.getEnv\n"
    text += "  let beforeNames := envBefore.constants.toList.foldl (fun names item => names.insert item.1) ({} : Std.HashSet Lean.Name)\n"
    text += "  let commandText : String := "+json.dumps(command_text,ensure_ascii=False)+"\n"
    text += "  let commandSyntax ← match Lean.Parser.runParserCategory envBefore (Lean.Name.mkSimple \"command\") commandText "+json.dumps(MODULE+":"+str(unit["start"]["line"]))+" with\n"
    text += "    | .ok syntax => pure syntax\n    | .error message => throwError \"Exact source command parse failed: {message}\"\n"
    text += "  unless commandSyntax.getKind.toString == "+json.dumps(exact[0]["syntax"]["syntaxKind"])+" do\n    throwError \"Parsed command kind differs from the authoritative source AST\"\n"
    text += "  Lean.Elab.Command.elabCommand commandSyntax\n"
    text += "  Lean.Elab.Command.liftTermElabM do\n    PiExponentCommandEmissionProbe.after beforeNames "+" ".join(json.dumps(s) for s in [primary["userName"],command_sha,MODULE,output])+closing
    emission_path = STAGE/"CommandEmission.lean"
    emission_path.write_bytes(text.encode("utf-8"))
    # Original auxiliary identities are selected from graph value/type edges.
    # There is no prefix-based association with the target command.
    todo,closure = list(unit["graph_names"]),set()
    while todo:
        name = todo.pop()
        if name in closure or name not in graph:
            continue
        closure.add(name)
        row = graph[name]
        todo.extend(row["typeDeps"]+row["valueDeps"]+row["constructors"])
    source_rows = [graph[n] for n in sorted(closure) if graph[n]["module"]==MODULE and graph[n]["isPrivate"]
                   and graph[n]["kind"] in {"def","theorem"}]
    source_output = (STAGE/"original-command-closure.json").relative_to(ROOT).as_posix()
    requests = ", ".join("("+json.dumps(r["name"])+", "+json.dumps(r["module"])+")" for r in source_rows)
    snapshot_path = STAGE/"SourceOriginalSnapshot.lean"
    snapshot = "import Lean\nimport "+MODULE+"\n\n"+core+EXPORTER+"\nrun_meta do\n  PiExponentCommandEmissionProbe.sourceSnapshot #["+requests+"] "+json.dumps(source_output)+"\n"
    snapshot_path.write_bytes(snapshot.encode("utf-8"))
    selected_paths = [source,original,facts_path,inventory_path,scopes_path,graph_path,core_path,
                      v/"lean-runtime.json",Path(__file__).resolve(),v/"provider-plans/all-shared-public/platform-artifact-plan-provider-variant.json"]
    pins = {p.relative_to(TASK).as_posix():sha(p) for p in selected_paths}
    runtime = json.loads((v/"lean-runtime.json").read_text(encoding="utf-8"))
    lean_src = Path(runtime["executable"]).parent.parent / "src/lean/Lean"
    api_paths = [lean_src/p for p in ["Elab/BuiltinEvalCommand.lean","Elab/Command.lean","Parser/Extension.lean","Meta/Eval.lean","Data/NameMap/Basic.lean","Environment.lean"]]
    headers = [f["syntax"] for f in facts if f["kind"]=="header"]
    if len(headers)!=1:
        raise ValueError("Probe source has no unique original import header")
    todo,original_imports = [headers[0]],[]
    while todo:
        node = todo.pop()
        if node["syntaxKind"]=="Lean.Parser.Module.import":
            ids,stack = [],[node]
            while stack:
                child=stack.pop()
                if child.get("identifier") is not None:
                    ids.append(child["identifier"])
                stack.extend(child.get("children",[]))
            if len(ids)!=1:
                raise ValueError("Probe original import syntax is ambiguous")
            original_imports.append(ids[0])
        todo.extend(node.get("children",[]))
    import_inventory = []
    for imported in sorted(set(original_imports)|{"Lean",MODULE}):
        candidates = [Path(p)/Path(*imported.split(".")).with_suffix(".olean") for p in runtime["environment"]["LEAN_PATH"].split(";")]
        resolved = next((p for p in candidates if p.is_file()),None)
        import_inventory.append({"module":imported,"resolved_first_ordered_runtime_olean":str(resolved) if resolved else None,
            "olean_sha256":sha(resolved) if resolved else None,"missing":resolved is None,
            "case":"CommandEmission" if imported in original_imports else "SourceOriginalSnapshot" if imported==MODULE else "both"})
    manifest = {"schema_version":1,"source_module":MODULE,"source_unit":unit,"source_primary_graph_row":primary,
        "exact_command_range":{"start":unit["start"],"end":unit["end"]},"exact_command_sha256":command_sha,
        "copied_prefix_range":{"start_offset":0,"end_offset":a},"copied_prefix_sha256":hashlib.sha256(raw[:a]).hexdigest(),
        "instrumentation_insertion_after_original_import_header":first,"scope_closing":closing,
        "command_execution":"single run_cmd: local actual Name baseline, runParserCategory exact source string, elabCommand, actual Name-set delta",
        "command_literal_source_bytes_sha256":hashlib.sha256(command_text.encode("utf-8")).hexdigest(),
        "same_module_initializers":False,"source_syntax_quotation_hygiene":False,
        "source_original_private_closure_requests":source_rows,"input_hashes":pins,"runtime_sha256":runtime_sha,
        "pinned_lean_api_source_hashes":{str(p):sha(p) for p in api_paths},
        "original_parser_imports":sorted(original_imports),"direct_import_olean_witnesses":import_inventory,
        "missing_direct_dependency_cases":[r for r in import_inventory if r["missing"]],
        "outputs_sha256":{p.name:sha(p) for p in [emission_path,snapshot_path]},
        "provisional":True,"validated":False,"submission_ready":False,"lean_started":False,"api_used":False,
        "required_before_compilation":["strictly recheck all selected input/runtime/executable hashes",
            "original project dependency OLeans must exist; missing imports are a rejection, never a stub"],
        "certification_policy":["both exact files compile individually within 300 seconds with all logSHAs",
            "actual Name equality/set delta ties all fresh own-module declarations to one exact AST command",
            "primary actual privateToUserName must equal full source binding identity uniquely",
            "type/value/Std3 checked for every emitted CI; theorem proof value null; all defs full nonnull values",
            "original SourcePrivateCI rows selected by actual env name and graph dependency edges",
            "no private numeric counter, source prefix, generated suffix or auxiliary owner is inferred from text",
            "source-to-emitted CI Name mapping requires validated actual environment maps and kernel type/full Def value correspondence",
            "provider/node generated alias command must repeat the same delta probe before granting its auxiliary closure availability"]}
    (STAGE/"probe-plan.json").write_text(json.dumps(manifest,indent=2)+"\n",encoding="utf-8")
    audit = context_closure_audit(inventory,state,graph,scopes)
    print(json.dumps({"stage":STAGE.relative_to(TASK).as_posix(),"unit":MODULE+":"+str(START),
                      "source_private_ci_requests":len(source_rows),"files":manifest["outputs_sha256"],"validated":False}))
    print(json.dumps(audit))


if __name__=="__main__":
    main()
