import Lean
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Parameters
import Theorems.Thm_OAI_PiExponent_exists_rational_parameters
import Mathlib


theorem OAI.PiExponent.exists_parameters (ν : ℝ) (hν : 2 < ν) : Nonempty (Parameters ν) := by
  sorry


namespace OAI
namespace PiExponent

theorem exists_eta_preserving_exponent_gap
    (nu theta A : ℝ) (hnu : 2 < nu) (hA : 0 < A)
    (hgap : 1 - theta < nu * (A - theta)) :
    ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧
      0 < nu * (A * (1 - eta) - theta) - (1 - theta) := by
  let gap : ℝ := nu * (A - theta) - (1 - theta)
  have hgap_pos : 0 < gap := by dsimp [gap]; linarith
  have hnu_pos : 0 < nu := by linarith
  have hden_pos : 0 < 2 * nu * A := by positivity
  let eta : ℝ := min (1 / 2) (gap / (2 * nu * A))
  have heta_pos : 0 < eta := by
    dsimp [eta]
    exact lt_min (by norm_num) (div_pos hgap_pos hden_pos)
  have heta_half : eta ≤ 1 / 2 := min_le_left _ _
  have heta_lt_one : eta < 1 := by linarith
  have heta_gap : eta ≤ gap / (2 * nu * A) := min_le_right _ _
  have hscaled : eta * (2 * nu * A) ≤ gap :=
    (le_div_iff₀ hden_pos).mp heta_gap
  refine ⟨eta, heta_pos, heta_lt_one, ?_⟩
  dsimp [gap] at hgap_pos hscaled
  nlinarith

end PiExponent
end OAI

open OAI OAI.PiExponent

theorem solution (ν : ℝ) (hν : 2 < ν) : Nonempty (Parameters ν) := by
  obtain ⟨theta, A, B, C, htheta, hthetaA, hAB, hB, hgap, hC, hBinv, hBC, hCtheta⟩ :=
    exists_rational_parameters ν hν
  obtain ⟨eta, heta, heta1, hgapeta⟩ := exists_eta_preserving_exponent_gap
    ν theta A hν (lt_trans htheta hthetaA) hgap
  exact ⟨⟨theta, A, B, C, eta, htheta, hthetaA, hAB, hB, hgap, hC,
    hBinv, hBC, hCtheta, heta, heta1, hgapeta⟩⟩

#print axioms solution

open Lean Meta

open Lean Meta

namespace PiExponentInterfaceSnapshot

partial def levelJson : Level → Json
  | .zero => Json.arr #[toJson "zero"]
  | .succ u => Json.arr #[toJson "succ", levelJson u]
  | .max u v => Json.arr #[toJson "max", levelJson u, levelJson v]
  | .imax u v => Json.arr #[toJson "imax", levelJson u, levelJson v]
  | .param n => Json.arr #[toJson "param", toJson n.toString]
  | .mvar n => Json.arr #[toJson "mvar", toJson n.name.toString]

def binderTag : BinderInfo → String
  | .default => "explicit"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instance"

-- Keep binder information, constant names, universe levels and de Bruijn
-- indices. Binder display names and source metadata have no kernel meaning.
partial def exprJson : Expr → Json
  | .bvar i => Json.arr #[toJson "bvar", toJson i]
  | .fvar n => Json.arr #[toJson "fvar", toJson n.name.toString]
  | .mvar n => Json.arr #[toJson "mvar", toJson n.name.toString]
  | .sort u => Json.arr #[toJson "sort", levelJson u]
  | .const n us => Json.arr #[toJson "const", toJson n.toString,
      Json.arr (us.map levelJson).toArray]
  | .app f a => Json.arr #[toJson "app", exprJson f, exprJson a]
  | .lam _ t b bi => Json.arr #[toJson "lambda", toJson (binderTag bi), exprJson t, exprJson b]
  | .forallE _ t b bi => Json.arr #[toJson "forall", toJson (binderTag bi), exprJson t, exprJson b]
  | .letE _ t v b nondep => Json.arr #[toJson "let", exprJson t, exprJson v, exprJson b, toJson nondep]
  | .lit (.natVal n) => Json.arr #[toJson "natLiteral", toJson n]
  | .lit (.strVal s) => Json.arr #[toJson "stringLiteral", toJson s]
  | .mdata _ e => exprJson e
  | .proj n i e => Json.arr #[toJson "projection", toJson n.toString, toJson i, exprJson e]

def exportSnapshot (names : Array Name) (output : String) : MetaM Unit := do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for name in names do
    let some ci := env.find? name | throwError "Missing interface declaration: {name}"
    if ci.type.hasMVar || ci.type.hasFVar then
      throwError "The exported declaration type is not closed: {name}"
    let value := match ci with
      | .defnInfo d => some d.value
      | .thmInfo _ => none
      | _ => none
    let typeText ← ppExpr ci.type
    rows := rows.push <| Json.mkObj [
      ("name", toJson name.toString),
      ("levelParams", toJson (ci.levelParams.map Name.toString)),
      ("type", exprJson ci.type),
      ("value", value.map exprJson |>.getD Json.null),
      ("prettyType", toJson typeText.pretty)]
  IO.FS.writeFile output (Json.arr rows |>.compress)

end PiExponentInterfaceSnapshot

set_option pp.universes true
set_option pp.fullNames true
set_option pp.explicit true
run_meta do
  PiExponentInterfaceSnapshot.exportSnapshot #[`OAI.PiExponent.exists_eta_preserving_exponent_gap, `OAI.PiExponent.exists_parameters, `solution] "verification/ap5/p1/generated-type.json"

open Lean Meta in
run_meta do
  let names : Array Lean.Name := #[`OAI.PiExponent.exists_eta_preserving_exponent_gap, `solution]
  let env ← Lean.getEnv
  let mut rows : Array Lean.Json := #[]
  for name in names do
    if (env.getModuleIdxFor? name).isSome then throwError "p1 proof reference is not an OwnModule CI: {name}"
    let some ci := env.find? name | throwError "missing p1 proof reference {name}"
    let value ← match ci with | .thmInfo t => pure t.value | _ => throwError "p1 reference is not a theorem {name}"
    if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars || value.hasMVar || value.hasFVar || value.hasLooseBVars then throwError "open p1 proof reference {name}"
    let owner := env.mainModule
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do throwError "non-Std3 p1 proof reference {name}"
    let refs := fun (e : Lean.Expr) => ((e.getUsedConstants.map Lean.Name.toString).qsort (fun a b => a < b))
    rows := rows.push <| Lean.Json.mkObj [("name", Lean.toJson name.toString), ("kind", Lean.toJson "theorem"), ("levelParams", Lean.toJson (ci.levelParams.map Lean.Name.toString)), ("closedType", Lean.toJson true), ("closedValue", Lean.toJson true), ("typeRefs", Lean.toJson (refs ci.type)), ("valueRefs", Lean.toJson (refs value)), ("axioms", Lean.toJson ((axioms.map Lean.Name.toString).qsort (fun a b => a < b))), ("owner", Lean.Json.mkObj [("kind", Lean.toJson "OwnModule"), ("module", Lean.toJson owner.toString)])]
  IO.FS.writeFile "verification/ap5/p1/proof-references.json" ((Lean.Json.mkObj [("schemaVersion", Lean.toJson 1), ("probeMainModule", Lean.toJson env.mainModule.toString), ("rows", Lean.Json.arr rows)]).pretty)
