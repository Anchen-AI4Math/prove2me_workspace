import Solutions.Sol_ZetaNine_HarmonicStability_harmonic_perturbed_log_den_rate
import Lean
open Lean Meta
set_option pp.fullNames true
set_option pp.universes false
run_meta do
  let mut rows : Array Json := #[]
  let emit (label : String) (name : Name) : MetaM Unit := do
    let ci ← getConstInfo name
    let typ ← ppExpr ci.type
    let axioms ← Lean.collectAxioms name
    let body ← match ci with
      | .defnInfo d => pure (Json.str (← ppExpr d.value).pretty)
      | _ => pure Json.null
    IO.println (Json.mkObj [("label",Json.str label),("declaration",Json.str name.toString),("type",Json.str typ.pretty),("axioms",toJson (axioms.toList.map Name.toString)),("definitionValue",body)]).compress
  emit "ZetaNine.HarmonicStability.harmonic_perturbed_log_den_rate" `solution
  emit "ZetaNine.HarmonicStability.harmonicExceptionalProduct" `ZetaNine.HarmonicStability.harmonicExceptionalProduct
  emit "ZetaNine.HarmonicStability.harmonicPower" `ZetaNine.HarmonicStability.harmonicPower
  emit "ZetaNine.HarmonicStability.logDen" `ZetaNine.HarmonicStability.logDen
  emit "ZetaNine.HarmonicStability.primeRemainder" `ZetaNine.HarmonicStability.primeRemainder
  emit "MediumPNT" `MediumPNT
