"""Close actual constructor proof refs using only genuine graph/parser spans."""
import json


def prefix(c, namespace, native=False):
    parent = "missions.zeta9.formalization.CoefficientMapAggregate" if native else "Definitions.Def_ZetaNine_CoefficientMapSummation"
    imports = [parent] + c["MATHLIB"] + ["Mathlib.Tactic.FinCases", "Mathlib.Tactic.Ring"]
    text = "\n".join("import " + m for m in imports)
    text += "\n\nset_option autoImplicit false\nnoncomputable section\nopen scoped BigOperators\nopen Finset Polynomial\n\nnamespace " + namespace + "\n\n"
    text += "\n".join(c["source"][f["span"]["start"]["offset"]:f["span"]["end"]["offset"]].decode() for f in c["definition_open_context"])
    return text + "\n\n"


def helper_binding(c, full):
    d = c["declaration"](full)
    a, v = d["declStart"]["offset"], d["valStart"]["offset"]
    refs = c["facts"]["CoefficientMapAggregate"]
    bindings = [r for r in refs if r["kind"] == "ref" and r["const"] == full and a <= r["start"]["offset"] < v]
    assert len(bindings) == 1 and d["docstring"] is None and d["privateTok"] is None
    binding = bindings[0]
    start = binding["start"]["offset"]
    assert c["source"][a:start].decode().strip() == "theorem"
    assert c["source"][start:binding["end"]["offset"]].decode() == full.split(".")[-1]
    return d, binding


def create_type_oracle(c, helpers):
    ordinary = c["def_facts"][:3]
    code = prefix(c, c["ALIAS_NS"], True)
    code += "\n\n".join(c["source"][d["declStart"]["offset"]:d["declEnd"]["offset"]].decode() for d in ordinary)
    code += "\n\nend " + c["ALIAS_NS"] + "\n\nopen Lean Meta\nset_option pp.fullNames true\nset_option pp.universes false\n\n"
    code += '''private def remapAggregateName (n : Name) : Name :=
  if n == `ZetaNine.CoefficientMapAggregate then
    `ZetaNine.CoefficientMapAggregateValueComparison
  else match n with
    | .str p s => .str (remapAggregateName p) s
    | .num p i => .num (remapAggregateName p) i
    | .anonymous => .anonymous

run_meta do
  for name in [''' + ", ".join("`" + n for n in helpers) + '''] do
    let ci ← getConstInfo name
    let type ← ppExpr ci.type
    let aliasExpr := ci.type.replace fun e => match e with
      | .const n ls =>
          if (`ZetaNine.CoefficientMapAggregate).isPrefixOf n then
            some (.const (remapAggregateName n) ls)
          else none
      | _ => none
    let aliasType ← ppExpr aliasExpr
    let axs ← Lean.collectAxioms name
    IO.println (Json.mkObj [("declaration", Json.str name.toString),
      ("original_type", Json.str type.pretty), ("alias_type", Json.str aliasType.pretty),
      ("axioms", toJson (axs.toList.map Name.toString))]).compress
'''
    for p in [c["OUT"] / "embedded-types.lean", c["PROJECT"] / "embedded-types.lean"]:
        c["write"](p, code)
    c["run"]("embedded-types", ["lake", "env", "lean", "embedded-types.lean"])
    return {r["declaration"]: r for r in c["rows"](c["OUT"] / "embedded-types.log")}


def create_definitions(c):
    ns = c["NS"]
    field_roots = {
        "aggregateLinearMap": ["aggregate_add", "aggregate_smul"],
        "coordinateLinearMap": ["coordinatePolynomial_add", "coordinatePolynomial_smul"],
    }
    all_helpers = set()
    helper_closures = {}
    for roots in field_roots.values():
        for name in roots:
            full = ns + "." + name
            reached = c["closure"]([full])
            helpers = [c["byname"][n] for n in reached if c["byname"][n]["module"].endswith(".CoefficientMapAggregate") and c["byname"][n]["kind"] == "theorem" and c["byname"][n]["startLine"] > 0]
            helpers.sort(key=lambda d: d["startLine"])
            helper_closures[full] = [h["name"] for h in helpers]
            all_helpers.update(helper_closures[full])
    expected = {ns + "." + n for n in ["actual_local_coefficient_add", "actual_local_coefficient_smul", "actual_rho_add", "actual_rho_smul", "actual_constant_add", "actual_constant_smul", "aggregate_add", "aggregate_smul", "coordinatePolynomial_add", "coordinatePolynomial_smul"]}
    assert all_helpers == expected
    type_rows = create_type_oracle(c, sorted(all_helpers))
    assert set(type_rows) == all_helpers
    assert all(set(r["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"} for r in type_rows.values())
    refs = [f for f in c["facts"]["CoefficientMapAggregate"] if f["kind"] == "ref"]
    provenance = []
    definitions = {}
    for alias, namespace in [(False, ns), (True, c["ALIAS_NS"])]:
        spans = []
        for name, d in zip(c["DEFS"], c["def_facts"]):
            a, b = d["declStart"]["offset"], d["declEnd"]["offset"]
            edits = []
            for helper in field_roots.get(name, []):
                full = ns + "." + helper
                occurrences = [r for r in refs if r["const"] == full and a <= r["start"]["offset"] < r["end"]["offset"] <= b]
                assert len(occurrences) == 1
                occurrence = occurrences[0]
                local_chunks = []
                local_facts = []
                for hn in helper_closures[full]:
                    hd, binding = helper_binding(c, hn)
                    hs, he = hd["declStart"]["offset"], hd["declEnd"]["offset"]
                    prefix_end = binding["start"]["offset"]
                    snippet = c["edit"](c["source"][hs:he], [(0, prefix_end - hs, b"have ")]).decode()
                    local_chunks.append("\n".join("    " + line for line in snippet.splitlines()))
                    local_facts.append({"name": hn, "declaration_fact": hd, "binding_fact": binding, "only_prefix_change": {"start": hs, "end": prefix_end, "replacement": "have "}})
                typ = type_rows[full]["alias_type" if alias else "original_type"]
                term = "((by\n" + "\n".join(local_chunks) + "\n    exact " + helper + ") :\n    (" + typ.replace("\n", "\n    ") + "))"
                rs, re = occurrence["start"]["offset"], occurrence["end"]["offset"]
                assert c["source"][rs:re].decode() == helper
                edits.append((rs - a, re - a, term.encode()))
                if not alias:
                    provenance.append({"definition": ns + "." + name, "actual_proof_callee": full, "reference_fact": occurrence, "helper_names": helper_closures[full], "helper_facts": local_facts, "actual_original_type": type_rows[full]["original_type"], "actual_semantically_remapped_alias_type": type_rows[full]["alias_type"], "replacement_proof_term": term, "data_fields_edited": False})
            spans.append(c["edit"](c["source"][a:b], edits).decode())
        definitions[alias] = prefix(c, namespace, alias) + "\n\n".join(spans) + "\n\nend " + namespace + "\n"
    c["dump"](c["OUT"] / "embedded-field-provenance.json", {"field_count": 4, "actual_original_helpers": sorted(all_helpers), "ordinary_data_defs_unchanged": 3, "new_global_helper_theorems": [], "fields": provenance, "data_value_kernel_comparison_pending": True})
    return definitions[False], definitions[True], provenance


def create_value_comparison(c):
    code = "import NativeValueComparisonDefinition\nimport Lean\n\nopen Lean Meta\nset_option autoImplicit false\nset_option pp.fullNames true\nset_option pp.universes false\nset_option pp.proofs true\n\n"
    for name in c["DEFS"]:
        code += "theorem native_value_" + name + "_eq : " + c["ALIAS_NS"] + "." + name + " = " + c["NS"] + "." + name + " := rfl\n\n"
    code += "theorem native_data_aggregateLinearMap (n : Nat) (W : Polynomial Rat) :\n  " + c["ALIAS_NS"] + ".aggregateLinearMap n W = " + c["NS"] + ".aggregate n W := rfl\n\n"
    code += "theorem native_data_coordinateLinearMap (a : Fin 5 → Rat) :\n  " + c["ALIAS_NS"] + ".coordinateLinearMap a = " + c["NS"] + ".coordinatePolynomial a := rfl\n\n"
    code += "theorem native_data_quarticAggregateLinearMap (n : Nat) (a : Fin 5 → Rat) :\n  " + c["ALIAS_NS"] + ".quarticAggregateLinearMap n a = " + c["NS"] + ".aggregate n (" + c["NS"] + ".coordinatePolynomial a) := rfl\n\n"
    code += "run_meta do\n  for (name, aliasName) in [" + ", ".join("(`" + c["NS"] + "." + n + ", `" + c["ALIAS_NS"] + "." + n + ")" for n in c["DEFS"]) + "] do\n"
    code += '''    let ci ← getConstInfo name
    let ai ← getConstInfo aliasName
    let .defnInfo d := ci | throwError "Original is not a definition"
    let .defnInfo a := ai | throwError "Comparison is not a definition"
    let typeEq ← isDefEq d.type a.type
    let valueEq ← isDefEq d.value a.value
    unless typeEq && valueEq do throwError "Original/comparison definition mismatch: {name}"
    let nt ← ppExpr d.type
    let nv ← ppExpr d.value
    let av ← ppExpr a.value
    let axs ← Lean.collectAxioms aliasName
    IO.println (Json.mkObj [("kind", Json.str "kernel_definition_value"),
      ("declaration", Json.str name.toString), ("alias_declaration", Json.str aliasName.toString),
      ("type", Json.str nt.pretty), ("type_kernel_equal", toJson typeEq),
      ("full_value_kernel_equal", toJson valueEq),
      ("pp_proofs_enabled", toJson true),
      ("original_expression_repr", Json.str (reprStr d.value)),
      ("comparison_expression_repr", Json.str (reprStr a.value)),
      ("original_raw_value", Json.str nv.pretty), ("comparison_raw_value", Json.str av.pretty),
      ("axioms", toJson (axs.toList.map Name.toString))]).compress
'''
    names = ["native_value_" + n + "_eq" for n in c["DEFS"]] + ["native_data_aggregateLinearMap", "native_data_coordinateLinearMap", "native_data_quarticAggregateLinearMap"]
    code += "  for name in [" + ", ".join("`" + n for n in names) + "] do\n"
    code += '''    let ci ← getConstInfo name
    let typ ← ppExpr ci.type
    let axs ← Lean.collectAxioms name
    IO.println (Json.mkObj [("kind", Json.str "rfl_or_data_equality"),
      ("declaration", Json.str name.toString), ("type", Json.str typ.pretty),
      ("axioms", toJson (axs.toList.map Name.toString))]).compress
'''
    for p in [c["OUT"] / "native-value-comparison.lean", c["PROJECT"] / "native-value-comparison.lean"]:
        c["write"](p, code)
