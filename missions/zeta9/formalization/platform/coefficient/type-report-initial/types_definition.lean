import Definitions.Def_ZetaNine_ShortZeroCoefficient
open Lean
set_option pp.fullNames true
set_option pp.universes false
run_meta do
  let emit (label : String) (name : Name) : Lean.Elab.Term.TermElabM Unit := do
    let ci ← getConstInfo name
    let type ← Lean.Meta.ppExpr ci.type
    let value ← match ci with
      | .defnInfo info => pure (some (← Lean.Meta.ppExpr info.value).pretty)
      | _ => pure none
    IO.println (Json.mkObj [("label", Json.str label), ("declaration", Json.str name.toString),
      ("type", Json.str type.pretty), ("value", toJson value)]).compress
  emit "ZetaNine.ShortZeroCoefficient.weightedCoeff" `ZetaNine.ShortZeroCoefficient.weightedCoeff
  emit "ZetaNine.ShortZeroCoefficient.A" `ZetaNine.ShortZeroCoefficient.A
