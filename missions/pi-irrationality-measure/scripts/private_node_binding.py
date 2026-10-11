"""Binding-faithful private theorem/definition helpers for provider nodes.

This isolated API preserves private def/abbrev command modifiers and bodies.
It does not edit any accepted generator or the earlier theorem-only adapter.
Actual private kernel Names are recovered from the environment, never guessed.
"""
import hashlib
import json

from private_inline_binding import isolate_inline_binding as isolate_theorem
from private_inline_binding import lean_name, lean_string
from span_edits import from_range


def walk_syntax(node):
    yield node
    for child in node.get("children", []):
        yield from walk_syntax(child)


def isolate_private_binding(unit, facts, graph_row, scope, wrapper, source_module,
                            source_bytes, node_name):
    if graph_row["kind"] == "theorem":
        edits, record = isolate_theorem(unit, facts, graph_row, scope, wrapper,
                                         source_module, source_bytes, node_name)
        record["source_kind"] = "theorem"
        record["snapshot_value_required"] = False
        return edits, record
    if (graph_row["kind"] != "def" or unit["graph_kinds"] != ["def"]
            or unit["graph_names"] != [graph_row["name"]] or graph_row["isInstance"]
            or not graph_row["isPrivate"] or not unit["private"] or unit["deprivate"]
            or unit["is_instance_command"] or unit["is_local_instance"]
            or unit["module"] != source_module or graph_row["module"] != source_module
            or not unit["nameRange"] or not unit["privateTok"] or unit["valueStart"] is None):
        raise ValueError("Private definition isolation requires one named private def/abbrev, without instance/opaque/structure companions")
    if (scope["verified_name"] != graph_row["userName"]
            or wrapper["range"] != {"start":unit["start"],"end":unit["end"]}
            or wrapper["nameRange"] != unit["nameRange"]):
        raise ValueError("Private definition scope/wrapper/graph binding identities disagree")
    commands = [f for f in facts if f["kind"] == "command" and f["isDeclaration"]
                and f["syntax"]["range"] == wrapper["range"]]
    if len(commands) != 1:
        raise ValueError("Private definition has no unique parser-owned command")
    binding = unit["nameRange"]
    bs, be = binding["start"]["offset"], binding["end"]["offset"]
    choices = []
    for node in walk_syntax(commands[0]["syntax"]):
        if node["syntaxKind"] not in {"Lean.Parser.Command.definition", "Lean.Parser.Command.abbrev"}:
            continue
        ids = [n for n in walk_syntax(node) if n["syntaxKind"] == "Lean.Parser.Command.declId"
               and n.get("range") == binding]
        tokens = [n for n in node.get("children", []) if n.get("atom") in {"def","abbrev"}]
        if len(ids) == 1 and len(tokens) == 1 and node["range"]["end"] == unit["end"]:
            choices.append((node,tokens[0]))
    if len(choices) != 1:
        raise ValueError("Private definition keyword must come from its unique AST declaration head")
    head, token = choices[0]
    kind = "def" if head["syntaxKind"] == "Lean.Parser.Command.definition" else "abbrev"
    if token["atom"] != kind or not token.get("range"):
        raise ValueError("Private definition parser kind and keyword disagree")
    ks, ke = token["range"]["start"]["offset"], token["range"]["end"]["offset"]
    ps, pe = unit["privateTok"]["start"]["offset"], unit["privateTok"]["end"]["offset"]
    private_tokens = [n for n in walk_syntax(commands[0]["syntax"])
                      if n.get("atom") == "private" and n.get("range") == unit["privateTok"]]
    if (len(private_tokens) != 1 or source_bytes[ps:pe] != b"private"
            or source_bytes[ks:ke] != kind.encode("utf-8")
            or not unit["start"]["offset"] <= ps < pe <= ks < ke <= bs < be <= unit["valueStart"]["offset"]):
        raise ValueError("Private definition modifier/keyword/binding/value ranges disagree")
    identities = {f["const"] for f in facts if f["kind"] == "ref"
                  and f["start"] == binding["start"] and f["end"] == binding["end"]}
    if len(identities) != 1:
        raise ValueError("Private definition binding must identify exactly one same-file oracle constant")
    identity = next(iter(identities))
    namespace = scope["namespace"]
    prefix = namespace+"." if namespace else ""
    relative = source_bytes[bs:be].decode("utf-8")
    if (not relative or not relative.isascii() or any(not p.isidentifier() for p in relative.split("."))
            or prefix+relative != graph_row["userName"]
            or namespace and (not namespace.isascii() or any(not p.isidentifier() for p in namespace.split(".")))):
        raise ValueError("Private definition full namespace and exact AST binding spelling disagree")
    descriptor = [node_name,source_module,graph_row["name"],bs,be]
    leaf = "_p2m_inline_"+hashlib.sha256(json.dumps(descriptor).encode("utf-8")).hexdigest()[:20]
    relative_prefix = relative.rpartition(".")[0]
    relative_alias = relative_prefix+"."+leaf if relative_prefix else leaf
    generated = prefix+relative_alias
    edits = [from_range(binding,relative_alias,"bind per-node private inline helper alias")]
    seen = {(bs,be)}
    for fact in facts:
        if fact["kind"] != "ref" or fact["const"] != identity:
            continue
        pair = (fact["start"]["offset"],fact["end"]["offset"])
        if pair in seen:
            continue
        seen.add(pair)
        edits.append(from_range({"start":fact["start"],"end":fact["end"]},generated,
                                "rewrite same-file bound inline helper reference"))
    return edits,{"source_graph_name":graph_row["name"],"source_user_name":graph_row["userName"],
        "source_module":source_module,"source_unit":unit["id"],"source_binding_range":binding,
        "source_definition_keyword":token["range"],"source_definition_keyword_text":kind,
        "source_kind":"def","source_was_private":True,"snapshot_value_required":True,
        "source_private_modifier_range":unit["privateTok"],"original_modifiers_preserved":True,
        "source_modifier_bytes_sha256":hashlib.sha256(source_bytes[unit["start"]["offset"]:ks]).hexdigest(),
        "oracle_binding_identity":identity,"node_generated_name":generated,
        "generated_kernel_name":None,"generated_kernel_name_recovery_pending":True}


def collector_code(records, artifact, *, emit=True, inline_types_output=None):
    requests = ", ".join("("+lean_string(r["source_graph_name"])+", "+lean_name(r["node_generated_name"])+
                         ", "+lean_string(r["source_kind"])+")" for r in records)
    text = '''
open Lean Meta in
run_meta do
  let requests : Array (String × Lean.Name × String) := #[REQUESTS]
  let env ← Lean.getEnv
  let mut rows : Array Lean.Json := #[]
  let mut actualNames : Array Lean.Name := #[]
  for (sourceName, userName, expectedKind) in requests do
    let mut candidates : Array Lean.Name := #[]
    for (actualName, _) in env.constants.toList do
      if Lean.privateToUserName? actualName == some userName then
        if (env.getModuleIdxFor? actualName).isNone then
          candidates := candidates.push actualName
    unless candidates.size == 1 do
      throwError "Expected one OwnModule private binding for {userName}, found {candidates.size}"
    let actualName := candidates[0]!
    let some ci := env.find? actualName | throwError "Missing recovered private declaration"
    let (kind, value, safety) ← match ci with
      | .thmInfo t => pure ("theorem", t.value, Lean.Json.null)
      | .defnInfo d => pure ("def", d.value, Lean.toJson (reprStr d.safety))
      | _ => throwError "Recovered private CI is neither theorem nor definition"
    unless kind == expectedKind do
      throwError "Recovered private CI kind differs from source Graph: {actualName}"
    if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars ||
        value.hasMVar || value.hasFVar || value.hasLooseBVars then
      throwError "Recovered private CI type/value is not closed"
    let axioms ← Lean.collectAxioms actualName
    unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
      throwError "Private helper has nonstandard axioms: {actualName}"
    actualNames := actualNames.push actualName
    rows := rows.push <| Lean.Json.mkObj [
      ("sourceGraphName", Lean.toJson sourceName),
      ("nodeGeneratedName", Lean.toJson userName.toString),
      ("actualKernelName", Lean.toJson actualName.toString),
      ("kind", Lean.toJson kind), ("safety", safety),
      ("ownerKind", Lean.toJson "OwnModule"),
      ("ownModule", Lean.toJson env.mainModule.toString),
      ("moduleIndexIsNone", Lean.toJson true),
      ("levelParams", Lean.toJson (ci.levelParams.map Lean.Name.toString)),
      ("typeRefs", Lean.toJson (ci.type.getUsedConstants.map Lean.Name.toString)),
      ("valueRefs", Lean.toJson (value.getUsedConstants.map Lean.Name.toString)),
      ("snapshotValueRequired", Lean.toJson (kind == "def")),
      ("axioms", Lean.toJson (axioms.map Lean.Name.toString))]
'''.replace("REQUESTS",requests)
    if emit:
        text += '  IO.println ("PI_ISOLATED_PRIVATE_MAP " ++ (Lean.Json.mkObj [\n'
        text += '    ("artifact", Lean.toJson '+lean_string(artifact)+'),\n'
        text += '    ("ownModule", Lean.toJson env.mainModule.toString),\n    ("rows", Lean.Json.arr rows)]).compress)\n'
    if inline_types_output is not None:
        text += '  PiExponentInterfaceSnapshot.exportSnapshot actualNames '+lean_string(inline_types_output)+'\n'
    return text


def source_inline_snapshot_code(records, output):
    requests = ", ".join("("+lean_string(r["source_graph_name"])+", "+lean_string(r["source_module"])+
                         ", "+lean_string(r["source_kind"])+")" for r in records)
    return '''
open Lean Meta in
run_meta do
  let requests : Array (String × String × String) := #[REQUESTS]
  let env ← Lean.getEnv
  let mut actualNames : Array Lean.Name := #[]
  for (sourceName, sourceModule, expectedKind) in requests do
    let candidates := env.constants.toList.filterMap fun (n, _) =>
      if n.toString == sourceName then some n else none
    unless candidates.length == 1 do
      throwError "Source Graph name does not select exactly one actual environment Name: {sourceName}"
    let actualName := candidates.head!
    let some idx := env.getModuleIdxFor? actualName | throwError "Source private CI is not imported"
    unless env.header.moduleNames[idx.toNat]?.map Lean.Name.toString == some sourceModule do
      throwError "Source private CI belongs to the wrong module"
    let some ci := env.find? actualName | throwError "Missing source private CI"
    let (kind, value) ← match ci with
      | .thmInfo t => pure ("theorem", t.value)
      | .defnInfo d => pure ("def", d.value)
      | _ => throwError "Source private CI is neither theorem nor definition"
    unless kind == expectedKind do
      throwError "Source private CI kind differs from Graph"
    if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars ||
        value.hasMVar || value.hasFVar || value.hasLooseBVars then
      throwError "Source private CI type/value is not closed"
    let axioms ← Lean.collectAxioms actualName
    unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
      throwError "Source private CI has nonstandard axioms"
    actualNames := actualNames.push actualName
  PiExponentInterfaceSnapshot.exportSnapshot actualNames OUTPUT
'''.replace("REQUESTS",requests).replace("OUTPUT",lean_string(output))


def compare_private_ci_snapshots(original_rows, generated_rows, records, validated_env_maps):
    """Compare closed CI exports using certified, artifact-specific Name maps.

    The calling verifier owns hash/runtime/preflight and map certification. An
    unvalidated collector message is deliberately not an admissible argument.
    Only constant/projection Name positions and universe parameter binders are
    normalized. Pretty strings, arbitrary JSON strings and theorem proofs are
    never rewritten or treated as type/value evidence.
    """
    if (validated_env_maps.get("validated") is not True
            or validated_env_maps.get("artifact") != "SnapshotGenerated"
            or validated_env_maps.get("unique_own_module_private_to_user_name") is not True
            or validated_env_maps.get("exact_source_runtime_input_preflight_pins_checked") is not True):
        raise ValueError("Private CI comparison requires certified SnapshotGenerated actual environment maps")
    by_source = {r["source_graph_name"]:r for r in records}
    if len(by_source) != len(records):
        raise ValueError("Private source binding records are not unique")
    rows = validated_env_maps["rows"]
    if len(rows) != len(records) or {r["sourceGraphName"] for r in rows} != set(by_source):
        raise ValueError("Certified environment map does not exactly cover private source bindings")
    name_map, actuals = {}, set()
    for row in rows:
        expected = by_source[row["sourceGraphName"]]
        if (row["nodeGeneratedName"] != expected["node_generated_name"]
                or row["kind"] != expected["source_kind"] or row["ownerKind"] != "OwnModule"
                or row["moduleIndexIsNone"] is not True
                or not isinstance(row["actualKernelName"],str) or not row["actualKernelName"]
                or row["actualKernelName"] in actuals):
            raise ValueError("Certified actual private binding differs from its source identity/kind")
        actuals.add(row["actualKernelName"])
        name_map[row["sourceGraphName"]] = row["actualKernelName"]
    original = {r["name"]:r for r in original_rows}
    generated = {r["name"]:r for r in generated_rows}
    if (len(original)!=len(original_rows) or len(generated)!=len(generated_rows)
            or set(original)!=set(by_source) or set(generated)!=actuals):
        raise ValueError("Private CI snapshot domains differ from actual certified binding maps")

    def normalized(tree, levels, names):
        if not isinstance(tree,list):
            return tree
        if not tree:
            return []
        if isinstance(tree[0],str) and tree[0] == "param":
            if len(tree)!=2 or not isinstance(tree[1],str) or tree[1] not in levels:
                raise ValueError("Kernel universe parameter is not bound by its CI levelParams")
            return ["param",levels[tree[1]]]
        if isinstance(tree[0],str) and tree[0] in {"const","projection"}:
            if len(tree)<2 or not isinstance(tree[1],str):
                raise ValueError("Malformed kernel constant/projection JSON")
            return [tree[0],names.get(tree[1],tree[1])]+[normalized(t,levels,names) for t in tree[2:]]
        if isinstance(tree[0],str) and tree[0] in {"mvar","fvar"}:
            raise ValueError("Private CI snapshot contains a free/metavariable")
        return [normalized(t,levels,names) for t in tree]

    checked = []
    for source_name, record in by_source.items():
        before, after = original[source_name], generated[name_map[source_name]]
        a,b = before["levelParams"],after["levelParams"]
        if len(a)!=len(b) or len(a)!=len(set(a)) or len(b)!=len(set(b)):
            raise ValueError("Private CI universe binder counts/uniqueness differ")
        left_levels,right_levels = {n:i for i,n in enumerate(a)},{n:i for i,n in enumerate(b)}
        if normalized(before["type"],left_levels,name_map)!=normalized(after["type"],right_levels,{}):
            raise ValueError("Private CI kernel types differ: "+source_name)
        if record["source_kind"] == "def":
            if before["value"] is None or after["value"] is None:
                raise ValueError("Private def/abbrev snapshot requires both complete nonnull values")
            if normalized(before["value"],left_levels,name_map)!=normalized(after["value"],right_levels,{}):
                raise ValueError("Private def/abbrev kernel values differ: "+source_name)
        elif before["value"] is not None or after["value"] is not None:
            raise ValueError("TypeOnly theorem snapshots must have null proof values")
        checked.append({"source_graph_name":source_name,"generated_actual_kernel_name":name_map[source_name],
                        "kind":record["source_kind"],"kernel_type_equal":True,
                        "kernel_value_equal":record["source_kind"]=="def"})
    return {"bindings":checked,"source_to_actual_kernel_names":name_map,
            "kernel_types_equal":True,"all_definition_values_equal":True,
            "normalization":"certified constant Names and universe binders only",
            "submission_ready":False}
