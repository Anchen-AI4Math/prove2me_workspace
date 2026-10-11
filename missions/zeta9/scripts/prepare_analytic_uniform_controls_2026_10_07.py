"""Pure expected-type/full-definition/kernel controls for the frozen 70-endpoint author SOURCE."""
from __future__ import annotations
import hashlib
import json
import re
from pathlib import Path

TASK = Path(__file__).resolve().parents[1]
OUT = TASK / "verification/formalization-analytic-factorial-preparation-2026-10-07"
PROJECT = OUT / ".rt/afb1"
LAYOUT_SHA = "f2b45465770375bf49131450fa3d72b3d9646fd4f940bf17199bbc42ee317a94"


def binding(path):
    data = path.read_bytes()
    return {"task_relative": path.relative_to(TASK).as_posix(), "bytes": len(data),
            "sha256": hashlib.sha256(data).hexdigest()}


def prefixes(text):
    return {m.group(1): text[m.start():text.index(":=", m.end()) + 2]
            for m in re.finditer(r"(?m)^theorem (\w+)", text)}


def arguments(prefix, name):
    text = prefix[len("theorem " + name):]
    out = []
    pos = 0
    while True:
        while text[pos].isspace():
            pos += 1
        if text[pos] == ":":
            return " ".join(out)
        opener = text[pos]
        assert opener in "({", (name, text[pos:])
        closer = ")" if opener == "(" else "}"
        depth, end = 1, pos + 1
        while depth:
            depth += (text[end] == opener) - (text[end] == closer)
            end += 1
        out += text[pos + 1:end - 1].split(":", 1)[0].split()
        pos = end


def quoted(names):
    return "#[" + ", ".join("``" + name for name in names) + "]"


def main():
    plan_path = OUT / "native-inputs-layout-v2-audit.json"
    assert binding(plan_path)["sha256"] == LAYOUT_SHA
    plan = json.loads(plan_path.read_text(encoding="utf-8"))
    original_inputs = []
    endpoints = []
    definitions = {}
    for row in plan["actual_source_copy_order"]:
        source = TASK / row["source"]["task_relative"]
        assert binding(source)["sha256"] == row["source"]["sha256"]
        text = source.read_text(encoding="utf-8")
        ns = re.search(r"(?m)^namespace (\S+)", text).group(1)
        original_inputs.append(binding(source))
        if source.relative_to(TASK).as_posix().startswith("formalization/Analytic"):
            for name, prefix in prefixes(text).items():
                endpoints.append({"name": name, "full_name": ns + "." + name, "prefix": prefix})
        for m in re.finditer(r"(?ms)^def (\w+)\b.*?(?=\n\n)", text):
            name = m.group(1)
            assert name not in definitions
            definitions[name] = {"full_name": ns + "." + name, "declaration": m.group(0)}
    assert len(endpoints) == 70 and len(definitions) == 29
    ns_names = sorted({row["full_name"].rsplit(".", 1)[0] for row in endpoints} |
                      {row["full_name"].rsplit(".", 1)[0] for row in definitions.values()})
    imports = '''import AnalyticWeightedBound
import Lean
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 200000
noncomputable section
open scoped BigOperators Topology
open Set Finset Filter Polynomial
open ZetaNine
open Lean Meta Elab Command
''' + "\n".join("open " + ns for ns in ns_names) + "\n"
    emitter = '''
private def afEmit (j : Json) : MetaM Unit := do
  liftIO <| IO.println ("AF_RECORD|" ++ j.compress)

private def afAxioms (n : Name) : MetaM Json := do
  let axs ← Lean.collectAxioms n
  for a in axs do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains a do
      throwError "Outside Std3: {n} -> {a}"
  return toJson (axs.map Name.toString)

private def afRecord (kind : String) (n : Name) : MetaM Unit := do
  let ci ← getConstInfo n
  let mut value := Json.null
  let mut valueTyped := false
  if let some e := ci.value? true then
    value := toJson (reprStr e)
    valueTyped ← isDefEq (← inferType e) ci.type
    unless valueTyped do throwError "Actual value/type kernel mismatch {n}"
  afEmit <| Json.mkObj [("kind",toJson kind),("name",toJson n.toString),
    ("type_raw",toJson (reprStr ci.type)),("value_raw",value),
    ("value_type_isDefEq",toJson valueTyped),
    ("levelParams",toJson (ci.levelParams.map Name.toString)),
    ("isProp",toJson (← isProp ci.type)),("axioms",← afAxioms n)]
'''
    own_modules = [row["module_name"] for row in plan["actual_source_copy_order"]]
    types = imports + emitter + "\nrun_cmd liftTermElabM do\n"
    for row in definitions.values():
        types += '  afRecord "definition" ``' + row["full_name"] + "\n"
    for row in endpoints:
        types += '  afRecord "theorem" ``' + row["full_name"] + "\n"
    types += '''  let env ← getEnv
  for i in [:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    if ''' + "#[" + ", ".join("`" + n for n in own_modules) + "]" + '''.contains m then
      let data := env.header.moduleData[i]!
      afEmit <| Json.mkObj [("kind",toJson "module_inventory"),("module",toJson m.toString),
        ("constant_names",toJson (data.constNames.map Name.toString)),
        ("extra_names",toJson (data.extraConstNames.map Name.toString))]
      for n in data.constNames do afRecord "module_declaration" n
      for n in data.extraConstNames do
        if (env.find? n).isSome then afRecord "module_extra" n
'''
    kernel = imports + emitter + "\nnamespace AFOriginalDefs\n"
    for name, row in definitions.items():
        head, body = row["declaration"].split(":=", 1)
        for dep, dependency in definitions.items():
            body = re.sub(r"(?<![\w.])" + re.escape(dep) + r"\b", dependency["full_name"], body)
        kernel += head + ":=" + body + "\n\n"
    kernel += "end AFOriginalDefs\n\n"
    for name, row in definitions.items():
        kernel += "theorem original_value_" + name + " : AFOriginalDefs." + name + " = " + row["full_name"] + " := rfl\n"
    kernel += "\nnamespace AFExpected\n"
    for row in endpoints:
        kernel += row["prefix"] + " by\n  exact @" + row["full_name"] + " " + arguments(row["prefix"], row["name"]) + "\n\n"
    kernel += "end AFExpected\n\n"
    helper_source = TASK / ".rt/aph1/APKernel.lean"
    original_helpers = helper_source.read_text(encoding="utf-8")
    helper_block = original_helpers[original_helpers.index("private def apProofHelpers"):original_helpers.index("\nrun_cmd liftTermElabM do", original_helpers.index("private def apProofHelpers"))]
    helper_block = helper_block.replace("apProofHelpers", "afProofHelpers").replace("apCompare", "afCompare").replace("apEmit", "afEmit").replace("apAxioms", "afAxioms")
    kernel += helper_block + "\nrun_cmd liftTermElabM do\n"
    for name, row in definitions.items():
        kernel += '  afCompare "definition_compare" ``' + row["full_name"] + " ``AFOriginalDefs." + name + " true\n"
        kernel += '  afRecord "definition_rfl" ``original_value_' + name + "\n"
    for row in endpoints:
        kernel += '  afCompare "theorem_compare" ``' + row["full_name"] + " ``AFExpected." + row["name"] + " false\n"
        kernel += '  afRecord "expected_theorem_value" ``AFExpected.' + row["name"] + "\n"
    resolver = imports + '''
run_cmd liftTermElabM do
  let env ← getEnv
  for n in env.header.moduleNames do
    let found ← Lean.findOLean n
    let canonical ← IO.FS.realPath found
    liftM <| IO.println ("AF_RECORD|" ++ (Json.mkObj [("kind",toJson "actual_module_resolver"),
      ("module",toJson n.toString),("found_olean",toJson found.toString),
      ("canonical_olean",toJson canonical.toString)]).compress)
'''
    boundary = imports + emitter + '''
namespace AFBoundary
theorem factorial_lower_zero : (0 : ℝ) ≤ Real.log (Nat.factorial 0 : ℝ) := by norm_num
theorem factorial_upper_one : Real.log (Nat.factorial 1 : ℝ) ≤ (0 : ℝ) := by norm_num
theorem actual_n_one_k_one_zero : CoefficientMap.actualR 1 (1 : ℚ) = 0 := by
  norm_num [CoefficientMap.actualR, CoefficientMap.numerator, CoefficientMap.poleProduct]
theorem actual_n_one_k_two_positive : (0 : ℝ) < (CoefficientMap.actualR 1 (2 : ℚ) : ℝ) :=
  AnalyticRationalFactorial.actualR_real_pos 1 2 (by norm_num)
theorem raw_n_one_first_term_zero : actualMomentSequence 1 4 0 = 0 :=
  actualMomentTerm_zero_of_pos_le 1 4 1 (by norm_num) (by norm_num)
theorem n_one_r_four_tail_exponent : tailPower 1 4 = 8 := by norm_num [tailPower]
theorem n_one_compact_contains_only_zero :
    (∑ m ∈ range (2 * 1 - 1), actualMomentSequence 1 4 m) = 0 := by
  norm_num [raw_n_one_first_term_zero]
theorem all_indices_nonnegative : ∀ n r m : ℕ, 0 ≤ actualMomentSequence n r m :=
  actualMomentSequence_nonneg
theorem no_even_input_for_actual_bound : ∀ n : ℕ, 1 ≤ n →
    |∑' m : ℕ, actualWeightedSequence n (1 : ℚ[X]) m| ≤
      analyticPrefactor n * weightedCoefficientHeight n (1 : ℚ[X]) := by
  intro n hn
  exact actualWeighted_uniform_bound n hn 1 (by norm_num)
theorem zero_polynomial_series : ∀ n m : ℕ, actualWeightedSequence n (0 : ℚ[X]) m = 0 := by
  intro n m
  simp [actualWeightedSequence, CoefficientMap.weightedR]
theorem zero_coefficient_height : ∀ n : ℕ, weightedCoefficientHeight n (0 : ℚ[X]) = 0 := by
  intro n
  simp [weightedCoefficientHeight]
theorem negative_constant_has_domain : (-1 : ℚ[X]).natDegree ≤ 4 := by norm_num
theorem excluded_n_zero : ¬ (1 ≤ (0 : ℕ)) := by norm_num
theorem excluded_degree_five : ¬ (Polynomial.X ^ 5 : ℚ[X]).natDegree ≤ 4 := by norm_num
theorem exact_uniform_family_domain :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ n : ℕ, 1 ≤ n → ∀ W : ℚ[X], W.natDegree ≤ 4 →
        |∑' m : ℕ, actualWeightedSequence n W m| ≤
          Real.exp ((-(2641 / 250 : ℝ) + ε n) * n) * weightedCoefficientHeight n W :=
  actual_weighted_uniform_o_one
end AFBoundary

run_cmd liftTermElabM do
'''
    boundary_names = re.findall(r"(?m)^theorem (\w+)", boundary)
    for name in boundary_names:
        boundary += '  afRecord "typed_boundary" ``AFBoundary.' + name + "\n"
    controls = []
    for name, text in (("AFTypes", types), ("AFKernel", kernel), ("AFResolver", resolver), ("AFBoundary", boundary)):
        target = PROJECT / "src" / (name + ".lean")
        assert not target.exists()
        target.write_text(text, encoding="utf-8")
        snapshot = OUT / "controls-v1" / (name + ".lean")
        snapshot.parent.mkdir(exist_ok=True)
        snapshot.write_text(text, encoding="utf-8")
        controls.append({"module": name, "control_source": binding(target), "source_snapshot": binding(snapshot)})
    report = {"status": "PURE_SOURCE_CONTROLS_ONLY", "actual_lean_calls": 0,
              "original_statement_prefixes_used_verbatim": True, "complete_theorem_names": [row["full_name"] for row in endpoints],
              "whole_definition_names": [row["full_name"] for row in definitions.values()],
              "original_statement_source_bindings": original_inputs, "control_sources": controls,
              "typed_boundary_names": boundary_names, "expected_type_controls": 70, "whole_definition_controls": 29,
              "planned_actual_Expr_equal_and_isDefEq": True, "planned_actual_value_inferType_checks": True,
              "helper_control_source_reused_as_SOURCE_only": binding(helper_source),
              "copied_foreign_proof_objects": 0, "actual_native_controls_not_yet_compiled": True}
    report_path = OUT / "controls-preparation-v1.json"
    assert not report_path.exists()
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": report["status"], "types": 70, "whole_definitions": 29,
                      "typed_boundaries": len(boundary_names), "audit": binding(report_path)}))


if __name__ == "__main__":
    main()
