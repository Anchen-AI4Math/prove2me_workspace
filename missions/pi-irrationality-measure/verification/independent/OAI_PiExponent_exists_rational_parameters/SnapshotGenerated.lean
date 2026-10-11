import Lean
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic



theorem OAI.PiExponent.exists_rational_parameters (ν : ℝ) (hν : 2 < ν) :
    ∃ θ A B C : ℚ,
      0 < (θ : ℝ) ∧ (θ : ℝ) < A ∧ (A : ℝ) < B ∧ (B : ℝ) < 1 ∧
      ν * ((A : ℝ) - θ) > 1 - θ ∧
      1 < (C : ℝ) ∧ (B : ℝ) < 1 / C ∧
      (B : ℝ) < C * θ ∧ (C : ℝ) * θ < 1 := by sorry

theorem solution (ν : ℝ) (hν : 2 < ν) :
    ∃ θ A B C : ℚ,
      0 < (θ : ℝ) ∧ (θ : ℝ) < A ∧ (A : ℝ) < B ∧ (B : ℝ) < 1 ∧
      ν * ((A : ℝ) - θ) > 1 - θ ∧
      1 < (C : ℝ) ∧ (B : ℝ) < 1 / C ∧
      (B : ℝ) < C * θ ∧ (C : ℝ) * θ < 1 := by
  have hνpos : 0 < ν := by linarith
  have hdiv : 1 / ν < (1 / 2 : ℝ) :=
    (div_lt_iff₀ hνpos).2 (by linarith)
  obtain ⟨b, hbl, hbu⟩ := exists_rat_btwn (show (1 / 2 : ℝ) < 1 - 1 / ν by linarith)
  have hbpos : 0 < (b : ℝ) := by linarith
  have hb1 : (b : ℝ) < 1 := by
    have := one_div_pos.mpr hνpos
    linarith
  have hνb : ν * (b : ℝ) < ν - 1 := calc
    _ < ν * (1 - 1 / ν) := mul_lt_mul_of_pos_left hbu hνpos
    _ = ν - 1 := by field_simp
  have hcoeff : 0 < ν * (1 - (b : ℝ)) - 1 := by nlinarith
  have hδtop : 0 < min (1 : ℝ) ((2 * (b : ℝ) - 1) / ((b : ℝ) * b)) :=
    lt_min (by norm_num) (div_pos (by linarith) (mul_pos hbpos hbpos))
  obtain ⟨δ, hδpos, hδtop⟩ := exists_rat_btwn hδtop
  have hδ1 : (δ : ℝ) < 1 := lt_of_lt_of_le hδtop (min_le_left _ _)
  have hδsmall : (δ : ℝ) < (2 * (b : ℝ) - 1) / ((b : ℝ) * b) :=
    lt_of_lt_of_le hδtop (min_le_right _ _)
  have hδprod : (δ : ℝ) * ((b : ℝ) * b) < 2 * (b : ℝ) - 1 :=
    (lt_div_iff₀ (mul_pos hbpos hbpos)).mp hδsmall
  let θ : ℚ := 1 - δ
  let A : ℚ := 1 - b * δ
  have hθcast : (θ : ℝ) = 1 - (δ : ℝ) := by simp [θ]
  have hAcast : (A : ℝ) = 1 - (b : ℝ) * δ := by simp [A]
  have hθpos : 0 < (θ : ℝ) := by rw [hθcast]; linarith
  have hθA : (θ : ℝ) < A := by
    rw [hθcast, hAcast]
    nlinarith [mul_pos (sub_pos.mpr hb1) hδpos]
  have hApos : 0 < (A : ℝ) := lt_trans hθpos hθA
  have hA1 : (A : ℝ) < 1 := by
    rw [hAcast]
    nlinarith [mul_pos hbpos hδpos]
  have hAsq : (A : ℝ) ^ 2 < θ := by
    rw [hAcast, hθcast]
    nlinarith [mul_pos hδpos (sub_pos.mpr hδprod)]
  have hgap : 1 - (θ : ℝ) < ν * ((A : ℝ) - θ) := by
    rw [hAcast, hθcast]
    nlinarith [mul_pos hcoeff hδpos]
  have hCinterval : (A : ℝ) / θ < 1 / A := by
    apply (div_lt_div_iff₀ hθpos hApos).2
    nlinarith
  obtain ⟨C, hClo, hChi⟩ := exists_rat_btwn hCinterval
  have hC1 : 1 < (C : ℝ) := by
    have : (1 : ℝ) < (A : ℝ) / θ := (lt_div_iff₀ hθpos).2 (by simpa using hθA)
    exact lt_trans this hClo
  have hCpos : 0 < (C : ℝ) := by linarith
  have hACθ : (A : ℝ) < (C : ℝ) * θ := (div_lt_iff₀ hθpos).mp hClo
  have hCA : (C : ℝ) * A < 1 := (lt_div_iff₀ hApos).mp hChi
  have hAinvC : (A : ℝ) < 1 / C := (lt_div_iff₀ hCpos).2 (by nlinarith)
  have hCθ1 : (C : ℝ) * θ < 1 := by nlinarith [mul_lt_mul_of_pos_left hθA hCpos]
  have hBinterval : (A : ℝ) < min (1 / (C : ℝ)) ((C : ℝ) * θ) :=
    lt_min hAinvC hACθ
  obtain ⟨B, hBlo, hBhi⟩ := exists_rat_btwn hBinterval
  have hBinv : (B : ℝ) < 1 / C := lt_of_lt_of_le hBhi (min_le_left _ _)
  have hBCθ : (B : ℝ) < (C : ℝ) * θ := lt_of_lt_of_le hBhi (min_le_right _ _)
  exact ⟨θ, A, B, C, hθpos, hθA, hBlo, lt_trans hBCθ hCθ1,
    hgap, hC1, hBinv, hBCθ, hCθ1⟩

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
      | .thmInfo t => some t.value
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
  PiExponentInterfaceSnapshot.exportSnapshot #[`OAI.PiExponent.exists_rational_parameters, `solution] "missions/pi-irrationality-measure/verification/independent/OAI_PiExponent_exists_rational_parameters/generated-type.json"
#print axioms solution
