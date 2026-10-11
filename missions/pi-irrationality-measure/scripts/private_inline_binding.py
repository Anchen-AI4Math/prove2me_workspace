"""Isolate one proof-only atomic theorem at sanctioned source AST ranges.

This does not change source files or classify declarations. The caller must
reject exported statement dependencies and validate the generated environment.
"""
import hashlib
import json
from pathlib import Path
from span_edits import Edit, from_range


def isolate_inline_binding(unit, facts, graph_row, scope, wrapper, source_module,
                           source_bytes, node_name):
    if (unit["module"] != source_module or graph_row["module"] != source_module
            or unit["graph_names"] != [graph_row["name"]] or unit["graph_kinds"] != ["theorem"]
            or graph_row["kind"] != "theorem" or graph_row["isInstance"]
            or unit["is_instance_command"] or unit["is_local_instance"] or unit["deprivate"]
            or not unit["nameRange"] or unit["valueStart"] is None):
        raise ValueError("Isolation requires one atomic proof-only ordinary theorem binding")
    if scope["verified_name"] != graph_row["userName"]:
        raise ValueError("Source scope and graph user-name identity disagree")
    if (unit["start"] != wrapper["range"]["start"] or unit["end"] != wrapper["range"]["end"]
            or unit["nameRange"] != wrapper["nameRange"]):
        raise ValueError("Wrapper belongs to a different source command")
    tokens = wrapper["theorem_keyword_tokens"]
    if len(tokens) != 1 or tokens[0]["keyword"] not in {"theorem", "lemma"}:
        raise ValueError("No unique authoritative theorem keyword")
    token = tokens[0]["range"]
    a, b = token["start"]["offset"], token["end"]["offset"]
    binding = unit["nameRange"]
    start, end = binding["start"]["offset"], binding["end"]["offset"]
    if (source_bytes[a:b] != tokens[0]["keyword"].encode("utf-8")
            or not unit["start"]["offset"] <= a < b <= start < end <= unit["valueStart"]["offset"]):
        raise ValueError("The keyword/binding/value ranges are inconsistent")
    identities = {f["const"] for f in facts if f["kind"] == "ref"
                  and f["start"] == binding["start"] and f["end"] == binding["end"]}
    if len(identities) != 1:
        raise ValueError("Source binding must resolve to one same-file oracle identity")
    identity = next(iter(identities))
    namespace = scope["verified_name"].rpartition(".")[0]
    if not namespace.isascii() or any(not part.isidentifier() for part in namespace.split(".")):
        raise ValueError("Non-ASCII/complex helper namespace requires a separate isolation review")
    descriptor = [node_name, source_module, graph_row["name"], start, end]
    leaf = "_p2m_inline_" + hashlib.sha256(json.dumps(descriptor).encode("utf-8")).hexdigest()[:20]
    generated = namespace + "." + leaf
    edits = [from_range(binding, leaf, "bind per-node private inline helper alias")]
    seen = {(start, end)}
    for fact in facts:
        if fact["kind"] != "ref" or fact["const"] != identity:
            continue
        pair = (fact["start"]["offset"], fact["end"]["offset"])
        if pair in seen:
            continue
        seen.add(pair)
        edits.append(from_range({"start": fact["start"], "end": fact["end"]}, generated,
                                "rewrite same-file bound inline helper reference"))
    if unit["privateTok"] is None:
        if graph_row["isPrivate"]:
            raise ValueError("Private graph identity has no authoritative private modifier")
        edits.append(Edit(a, a, b"private ", "insert private at AST theorem token after attributes/wrappers"))
    else:
        private = unit["privateTok"]
        pa, pb = private["start"]["offset"], private["end"]["offset"]
        if (not graph_row["isPrivate"] or source_bytes[pa:pb] != b"private"
                or not unit["start"]["offset"] <= pa < pb <= a):
            raise ValueError("Existing private modifier is inconsistent")
    return edits, {"source_graph_name": graph_row["name"], "source_user_name": graph_row["userName"],
                   "source_module": source_module, "source_unit": unit["id"],
                   "source_binding_range": binding, "source_theorem_keyword": token,
                   "oracle_binding_identity": identity, "node_generated_name": generated,
                   "source_was_private": graph_row["isPrivate"],
                   "generated_kernel_name": None, "generated_kernel_name_recovery_pending": True}


def lean_name(name):
    if not name.isascii() or any(not part.isidentifier() for part in name.split(".")):
        raise ValueError("Generated helper alias cannot be represented as a conservative Lean name")
    return "`" + name


def lean_string(text):
    return json.dumps(text, ensure_ascii=False)


def collector_code(records, artifact, *, emit=True, inline_types_output=None):
    """Inline run_meta; no public collector constants and no guessed private IDs.

    Thm/Sol emit maps on stdout so the exact payload never writes local paths on
    the server. Only the local Generated Snapshot requests typed JSON output.
    """
    requests = ", ".join("(" + lean_string(r["source_graph_name"]) + ", " + lean_name(r["node_generated_name"]) + ")"
                         for r in records)
    text = '''\nopen Lean Meta in
run_meta do
  let requests : Array (String × Lean.Name) := #[REQUESTS]
  let env ← Lean.getEnv
  let mut rows : Array Lean.Json := #[]
  let mut actualNames : Array Lean.Name := #[]
  for (sourceName, userName) in requests do
    let mut candidates : Array Lean.Name := #[]
    for (actualName, _) in env.constants.toList do
      if Lean.privateToUserName? actualName == some userName then
        -- Imported constants have a module index; only this module has none.
        if (env.getModuleIdxFor? actualName).isNone then
          candidates := candidates.push actualName
    unless candidates.size == 1 do
      throwError "Expected one OwnModule private binding for {userName}, found {candidates.size}"
    let actualName := candidates[0]!
    let some ci := env.find? actualName | throwError "Missing recovered private declaration"
    let value ← match ci with
      | .thmInfo t => pure t.value
      | _ => throwError "Recovered inline binding is not a theorem"
    if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars ||
        value.hasMVar || value.hasFVar || value.hasLooseBVars then
      throwError "Recovered private theorem is not closed"
    let axioms ← Lean.collectAxioms actualName
    unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
      throwError "Private helper has a nonstandard axiom: {actualName}"
    actualNames := actualNames.push actualName
    rows := rows.push <| Lean.Json.mkObj [
      ("sourceGraphName", Lean.toJson sourceName),
      ("nodeGeneratedName", Lean.toJson userName.toString),
      ("actualKernelName", Lean.toJson actualName.toString),
      ("ownerKind", Lean.toJson "OwnModule"),
      ("ownModule", Lean.toJson env.mainModule.toString),
      ("moduleIndexIsNone", Lean.toJson true),
      ("levelParams", Lean.toJson (ci.levelParams.map Lean.Name.toString)),
      ("typeRefs", Lean.toJson (ci.type.getUsedConstants.map Lean.Name.toString)),
      ("valueRefs", Lean.toJson (value.getUsedConstants.map Lean.Name.toString)),
      ("axioms", Lean.toJson (axioms.map Lean.Name.toString))]
'''.replace("REQUESTS", requests)
    if emit:
        text += ('  IO.println ("PI_ISOLATED_PRIVATE_MAP " ++ (Lean.Json.mkObj [\n'
                 '    ("artifact", Lean.toJson ' + lean_string(artifact) + '),\n'
                 '    ("ownModule", Lean.toJson env.mainModule.toString),\n'
                 '    ("rows", Lean.Json.arr rows)]).compress)\n')
    if inline_types_output is not None:
        text += "  PiExponentInterfaceSnapshot.exportSnapshot actualNames " + lean_string(inline_types_output) + "\n"
    return text


def source_inline_snapshot_code(records, output):
    requests = ", ".join("(" + lean_string(r["source_graph_name"]) + ", " +
                         lean_string(r["source_module"]) + ")" for r in records)
    return '''\nopen Lean Meta in
run_meta do
  let requests : Array (String × String) := #[REQUESTS]
  let env ← Lean.getEnv
  let mut actualNames : Array Lean.Name := #[]
  for (sourceName, sourceModule) in requests do
    let candidates := env.constants.toList.filterMap fun (n, _) =>
      if n.toString == sourceName then some n else none
    unless candidates.length == 1 do
      throwError "Source helper name does not select one actual environment Name: {sourceName}"
    let actualName := candidates.head!
    let some idx := env.getModuleIdxFor? actualName | throwError "Source helper is not imported"
    let some owner := env.header.moduleNames[idx.toNat]? | throwError "Invalid source module index"
    unless owner.toString == sourceModule do
      throwError "Source helper belongs to the wrong module"
    let some ci := env.find? actualName | throwError "Missing source helper"
    match ci with
    | .thmInfo _ => pure ()
    | _ => throwError "Source helper is not a theorem"
    let axioms ← Lean.collectAxioms actualName
    unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
      throwError "Original helper has a nonstandard axiom"
    actualNames := actualNames.push actualName
  PiExponentInterfaceSnapshot.exportSnapshot actualNames OUTPUT
'''.replace("REQUESTS", requests).replace("OUTPUT", lean_string(output))


def recover_private_maps(manifest, preflights, root):
    """Read actual maps only from exact, successful generated-file preflights.

    Returns evidence without writing or changing a manifest. This certifies name
    recovery only; callers must still compare kernel types/proofs and validate
    the full publication flow.
    """
    root = Path(root).resolve()
    task = Path(__file__).resolve().parents[1]
    statement = (root / manifest["statement"]).resolve()
    solution = (root / manifest["solution"]).resolve()
    stage = statement.parent
    if stage.parent != (task / "verification/nodes-isolated-preview").resolve():
        raise ValueError("Expected an isolated preview stage in this mission")
    for relative, expected in manifest["input_hashes"].items():
        path = (task / relative).resolve()
        if not path.is_relative_to(task) or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise ValueError("Global input changed before private-name recovery: " + relative)
    for filename, expected in manifest["implementation_sha256"].items():
        path = task / "scripts" / filename
        if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise ValueError("Isolation implementation changed before name recovery")
    for origin in manifest["source_components"]:
        for field in ("source", "original_source", "facts"):
            path = (root / origin[field]).resolve()
            if not path.is_relative_to(task) or hashlib.sha256(path.read_bytes()).hexdigest() != origin[field + "_sha256"]:
                raise ValueError("Original/port/AST witness changed before name recovery")
    if hashlib.sha256((task / "verification/TypedSnapshotCore.inc").read_bytes()).hexdigest() != manifest["core_sha256"]:
        raise ValueError("Snapshot core changed before name recovery")
    from generate_independent_node import runtime_pin
    if runtime_pin() != manifest["runtime_sha256"]:
        raise ValueError("Pinned runtime changed before private-name recovery")
    expected_files = set(manifest["outputs_sha256"])
    if set(preflights) != expected_files or solution.parent != stage:
        raise ValueError("Private-name recovery requires exactly all four compiled files")
    source_names = {r["source_graph_name"]: r["node_generated_name"] for r in manifest["node_generated_names"]}
    output, evidence = {}, {}
    roles = {statement.name: "Thm", solution.name: "Sol", "SnapshotGenerated.lean": "SnapshotGenerated"}
    for filename, record in preflights.items():
        source = stage / filename
        log = (root / record["log"]).resolve()
        if (record["exit_code"] or record["original_exit_code"] or record["timed_out"]
                or not record["source_unchanged"] or record["mode"] != "verification"
                or not 0 < record["seconds"] <= 300 or not 0 < record["timeout_seconds"] <= 300
                or record["runtime_sha256"] != manifest["runtime_sha256"]
                or (root / record["source"]).resolve() != source
                or hashlib.sha256(source.read_bytes()).hexdigest() != manifest["outputs_sha256"][filename]
                or record["source_sha256"] != manifest["outputs_sha256"][filename]
                or not log.is_relative_to(stage.parents[1])
                or hashlib.sha256(log.read_bytes()).hexdigest() != record["log_sha256"]):
            raise ValueError("Stale/failed exact private-name preflight: " + filename)
        if filename not in roles:
            continue
        marker = manifest["private_map_log_marker"]
        messages = [json.loads(line[len(marker):]) for line in log.read_text(encoding="utf-8").splitlines()
                    if line.startswith(marker)]
        if len(messages) != 1 or messages[0]["artifact"] != roles[filename]:
            raise ValueError("Expected one private-map message for " + filename)
        message = messages[0]
        rows = message["rows"]
        if len(rows) != len(source_names) or {r["sourceGraphName"] for r in rows} != set(source_names):
            raise ValueError("Generated OwnModule helpers do not match original bindings")
        if not isinstance(message["ownModule"], str) or not message["ownModule"]:
            raise ValueError("Actual module identity is missing")
        actuals = set()
        mapping = {}
        for row in rows:
            if (row["nodeGeneratedName"] != source_names[row["sourceGraphName"]]
                    or row["ownerKind"] != "OwnModule" or row["moduleIndexIsNone"] is not True
                    or row["ownModule"] != message["ownModule"]
                    or not isinstance(row["actualKernelName"], str) or not row["actualKernelName"]
                    or not set(row["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"}):
                raise ValueError("Recovered binding has wrong alias, ownership or axioms")
            actuals.add(row["actualKernelName"])
            mapping[row["sourceGraphName"]] = row["actualKernelName"]
        if len(actuals) != len(rows):
            raise ValueError("Two source bindings resolve to the same private kernel name")
        output[roles[filename]] = mapping
        evidence[roles[filename]] = {"log": record["log"], "log_sha256": record["log_sha256"],
                                     "own_module": message["ownModule"], "rows": rows}
    if set(output) != set(manifest["expected_map_artifacts"]):
        raise ValueError("Private maps are incomplete")
    return {"source_to_generated_private_kernel_names": output, "evidence": evidence,
            "kernel_name_mapping_recovered": True, "kernel_types_validated": False,
            "validated": False, "submission_ready": False, "full_tree_ready": False}
