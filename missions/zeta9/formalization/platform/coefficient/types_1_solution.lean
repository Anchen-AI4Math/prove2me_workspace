import Solutions.Sol_ZetaNine_ShortZeroCoefficient_A_ne_zero_of_even
open Lean
set_option pp.fullNames true
set_option pp.universes false
run_meta do
  let emit (label : String) (name : Name) : Lean.Meta.MetaM Unit := do
    let ci ← getConstInfo name
    let type ← Lean.Meta.ppExpr ci.type
    let value ← match ci with
      | .defnInfo info => pure (some (← Lean.Meta.ppExpr info.value).pretty)
      | _ => pure none
    IO.println (Json.mkObj [("label", Json.str label), ("declaration", Json.str name.toString),
      ("type", Json.str type.pretty), ("value", toJson value)]).compress
  emit "ZetaNine.ShortZeroCoefficient.A_ne_zero_of_even" `solution
