import missions.zeta9.formalization.CoefficientMapConnection
import Lean
open Lean
set_option pp.fullNames true
set_option pp.universes false
set_option pp.proofs true
run_meta do
  let env ← getEnv
  let modules := env.header.moduleNames
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let some m := modules[idx.toNat]? | continue
    unless m == `missions.zeta9.formalization.CoefficientMapConnection do continue
    let kind := match ci with
      | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .axiomInfo _ => "axiom"
      | .opaqueInfo _ => "opaque" | _ => "other"
    let typ ← Lean.Meta.ppExpr ci.type
    let val := match ci with
      | .defnInfo d => some d.value | .thmInfo t => some t.value
      | .opaqueInfo o => some o.value | _ => none
    let printedVal ← match ci with
      | .defnInfo d => pure (some (← Lean.Meta.ppExpr d.value).pretty)
      | _ => pure none
    let range ← findDeclarationRanges? n
    let (sl, el) := match range with
      | some r => (r.range.pos.line, r.range.endPos.line) | none => (0, 0)
    let axs ← Lean.collectAxioms n
    IO.println (Json.mkObj [("declaration", Json.str n.toString), ("kind", Json.str kind),
      ("module", Json.str m.toString), ("internal", toJson n.isInternal),
      ("startLine", toJson sl), ("endLine", toJson el),
      ("type", Json.str typ.pretty), ("type_expression_repr", Json.str (reprStr ci.type)),
      ("value", toJson printedVal),
      ("definition_expression_repr", toJson (if kind == "def" then val.map reprStr else none)),
      ("type_dependencies", toJson (ci.type.getUsedConstants.toList.map Name.toString)),
      ("value_dependencies", toJson ((val.map (·.getUsedConstants.toList.map Name.toString)).getD [])),
      ("axioms", toJson (axs.toList.map Name.toString))]).compress
