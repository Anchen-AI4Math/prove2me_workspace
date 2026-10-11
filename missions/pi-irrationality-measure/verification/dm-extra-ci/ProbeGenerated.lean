import Definitions.Def_OAI_NumberTheory_PiExponent_LocalAlgebra_Dimension
import Lean
import Lean.Meta.Eqns
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section


namespace OAI

open Filter Topology

namespace PiExponent

 theorem tendsto_nat_add_one_div_pow {r : ℝ} (hr : 1 < r) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) / r ^ n) atTop (𝓝 0) := by
  have h₁ := tendsto_pow_const_div_const_pow_of_one_lt 1 hr
  have h₀ := tendsto_pow_const_div_const_pow_of_one_lt 0 hr
  simpa only [pow_one, pow_zero, ← add_div, zero_add] using h₁.add h₀

 theorem tendsto_pow_div_nat_add_one {r : ℝ} (hr : 1 < r) :
    Tendsto (fun n : ℕ => r ^ n / ((n : ℝ) + 1)) atTop atTop := by
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < ((n : ℝ) + 1) / r ^ n :=
    Filter.Eventually.of_forall fun n =>
      div_pos (by positivity) (pow_pos (zero_lt_one.trans hr) n)
  have hwithin : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / r ^ n)
      atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_nat_add_one_div_pow hr, hpos⟩
  have hinv := hwithin.inv_tendsto_nhdsGT_zero
  change Tendsto (fun n : ℕ => (((n : ℝ) + 1) / r ^ n)⁻¹) atTop atTop at hinv
  simpa only [inv_div] using hinv

end PiExponent

end OAI

end

section







namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace PiExponent

















theorem dimensionK_div_W_le (B C : ℝ) (hB : 0 < B) (hC : 0 ≤ C) (m : ℕ) :
    (dimensionK C m : ℝ) / dimensionW B m ≤ (C * B) ^ m := by
  rw [dimensionW, div_inv_eq_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (dimensionK_le C hC m) (pow_pos hB m).le

theorem dimensionV_geometric_lower (theta B C : ℝ) (htheta : 0 < theta)
    (hB : 0 < B) (m : ℕ) (hlarge : 2 ≤ C ^ m) :
    (C * theta / B) ^ m ≤ dimensionV theta B C m := by
  have hfloor : C ^ m < (dimensionK C m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hK : C ^ m ≤ 2 * (dimensionK C m : ℝ) := by linarith
  rw [div_pow, mul_pow, div_eq_mul_inv]
  unfold dimensionV dimensionW
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hK (pow_pos htheta m).le)
    (inv_pos.mpr (pow_pos hB m)).le



theorem dimension_error_le (theta B C a b : ℝ) (htheta : 0 < theta)
    (hB : 0 < B) (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (m : ℕ) (hlarge : 2 ≤ C ^ m) :
    (a * (m : ℝ) + b) / dimensionV theta B C m +
        100 * (dimensionK C m : ℝ) / dimensionW B m ≤
      (a * (m : ℝ) + b) / (C * theta / B) ^ m + 100 * (C * B) ^ m := by
  have hr : 0 < (C * theta / B) ^ m := by
    have hCp : 0 < C := by
      by_contra hn
      have hz : C = 0 := le_antisymm (le_of_not_gt hn) hC
      subst C
      rcases m with _ | m <;> norm_num at hlarge
    positivity
  apply add_le_add
  · exact div_le_div_of_nonneg_left (by positivity) hr
      (dimensionV_geometric_lower theta B C htheta hB m hlarge)
  · rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (dimensionK_div_W_le B C hB hC m) (by norm_num)



theorem tendsto_dimension_error_majorant (theta B C a b : ℝ)
    (hB : 0 < B) (hC : 0 < C) (hsmall : C * B < 1)
    (hlarge : 1 < C * theta / B) :
    Tendsto (fun m : ℕ => (a * (m : ℝ) + b) / (C * theta / B) ^ m +
      100 * (C * B) ^ m) atTop (𝓝 0) := by
  have h₁ := tendsto_pow_const_div_const_pow_of_one_lt 1 hlarge
  have h₀ := tendsto_pow_const_div_const_pow_of_one_lt 0 hlarge
  have hlin : Tendsto (fun m : ℕ => (a * (m : ℝ) + b) /
      (C * theta / B) ^ m) atTop (𝓝 0) := by
    convert (h₁.const_mul a).add (h₀.const_mul b) using 1
    · ext m
      simp only [pow_one, pow_zero]
      ring
    · simp
  have hgeom := tendsto_pow_atTop_nhds_zero_of_lt_one (mul_pos hC hB).le hsmall
  simpa only [mul_zero, add_zero] using hlin.add (hgeom.const_mul 100)

theorem tendsto_dimension_collision (A B eta : ℝ)
    (hratio : 1 < B / A) (heta : 0 < eta) :
    Tendsto (fun m : ℕ => eta ^ 2 * (B / A) ^ m /
      (2 * ((m : ℝ) + 1))) atTop atTop := by
  have h := (tendsto_pow_div_nat_add_one hratio).const_mul_atTop
    (show 0 < eta ^ 2 / 2 by positivity)
  convert h using 1
  ext m
  rw [mul_div_mul_comm]



end PiExponent

end

end OAI

end
noncomputable section
open OAI OAI.PiExponent
open Filter
open scoped Topology


end

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

namespace PiExponentEquationProvenanceProbe
open Lean Meta

def ownership (env : Environment) (name : Name) : Json :=
  match env.getModuleIdxFor? name with
  | some idx => Json.mkObj [
      ("kind", toJson "ImportedModule"), ("index", toJson idx.toNat),
      ("module", toJson (env.header.moduleNames[idx.toNat]?.map Name.toString))]
  | none => Json.mkObj [("kind", toJson "OwnModule"), ("module", toJson env.mainModule.toString)]

def checkedCI (name : Name) : MetaM Json := do
  let ci ← getConstInfo name
  if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars then
    throwError "Equation probe type is not closed: {name}"
  let value := match ci with
    | .defnInfo d => some d.value
    | _ => none
  if value.any (fun e => e.hasMVar || e.hasFVar || e.hasLooseBVars) then
    throwError "Equation probe definition value is not closed: {name}"
  let kind ← match ci with
    | .defnInfo _ => pure "def"
    | .thmInfo _ => pure "theorem"
    | _ => throwError "Equation probe found unsupported constant kind: {name}"
  let axioms ← collectAxioms name
  unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
    throwError "Equation probe nonstandard axiom: {name}"
  return Json.mkObj [
    ("actualName", toJson name.toString),
    ("userName", toJson (privateToUserName name).toString),
    ("levelParams", toJson (ci.levelParams.map Name.toString)),
    ("kind", toJson kind),
    ("type", PiExponentInterfaceSnapshot.exprJson ci.type),
    ("value", value.map PiExponentInterfaceSnapshot.exprJson |>.getD Json.null),
    ("owner", ownership (← getEnv) name),
    ("axioms", toJson (axioms.map Name.toString))]

def exportEquationSnapshot (primary : Name) (expectedModule output side : String) : MetaM Unit := do
  let envBefore ← getEnv
  let ci ← getConstInfo primary
  match ci with
  | .defnInfo _ => pure ()
  | _ => throwError "Primary source binding is not a definition"
  let some idx := envBefore.getModuleIdxFor? primary
    | throwError "Primary must belong to the imported source/provider module"
  unless envBefore.header.moduleNames[idx.toNat]?.map Name.toString == some expectedModule do
    throwError "Primary binding belongs to an unexpected module"
  let equations? ← Lean.Meta.getEqnsFor? primary
  let unfolding? ← Lean.Meta.getUnfoldEqnFor? primary
  let mut equations : Array Json := #[]
  for name in equations?.getD #[] do
    let parent? ← Lean.Meta.isEqnThm? name
    unless parent? == some primary do
      throwError "getEqnsFor? result lacks its exact inverse primary relation: {name}"
    equations := equations.push <| Json.mkObj [
      ("getter", toJson "Lean.Meta.getEqnsFor?"),
      ("inversePrimary", toJson (parent?.map Name.toString)),
      ("CI", ← checkedCI name)]
  let unfolding ← match unfolding? with
    | some name => pure <| Json.mkObj [
        ("getter", toJson "Lean.Meta.getUnfoldEqnFor?"), ("CI", ← checkedCI name)]
    | none => pure Json.null
  let result := Json.mkObj [
    ("side", toJson side), ("expectedModule", toJson expectedModule),
    ("primaryBinding", ← checkedCI primary),
    ("getEqnsForReturnedSome", toJson equations?.isSome),
    ("actualEquationNames", toJson (equations?.map (·.map Name.toString))),
    ("equations", Json.arr equations), ("unfolding", unfolding),
    ("probeMainModule", toJson (← getEnv).mainModule.toString),
    ("theoremProofValuesExported", toJson false)]
  IO.FS.writeFile output result.compress

end PiExponentEquationProvenanceProbe

namespace DimensionMarginExtraCI
open Lean Meta

def refs (value : Expr) : Array String :=
  (value.getUsedConstants.map Name.toString).qsort (fun a b => a < b)

def exportExtra (side output : String) : MetaM Unit := do
  let env ← getEnv
  let parent ← getConstInfo `OAI.PiExponent.tendsto_nat_add_one_div_pow
  let .thmInfo theoremInfo := parent
    | throwError "Expected actual inline theorem parent"
  let theoremRefs := refs theoremInfo.value
  unless theoremRefs.contains "OAI.PiExponent.tendsto_nat_add_one_div_pow._simp_1_1" do
    throwError "Automatic simp helper is not literal in actual parent proof"
  let primaryV ← getConstInfo `OAI.PiExponent.dimensionV
  let .defnInfo d := primaryV | throwError "Expected actual dimensionV Definition"
  let definitionRefs := refs d.value
  unless definitionRefs.contains "OAI.PiExponent.dimensionV._proof_1" do
    throwError "Automatic proof helper is not literal in full Definition value"
  let primaryW := `OAI.PiExponent.dimensionW
  let equations? ← Lean.Meta.getEqnsFor? primaryW
  let names := equations?.getD #[]
  unless names.contains `OAI.PiExponent.dimensionW.eq_1 do
    throwError "Actual dimensionW equation getter omitted required referenced CI"
  let inverse? ← Lean.Meta.isEqnThm? `OAI.PiExponent.dimensionW.eq_1
  unless inverse? == some primaryW do
    throwError "Actual equation inverse primary differs"
  let result := Json.mkObj [
    ("schemaVersion", toJson (1 : Nat)), ("side", toJson side),
    ("probeMainModule", toJson env.mainModule.toString),
    ("sourceDerivedFrom", toJson "actual-primitive-proof-reference-set"),
    ("theoremParent", ← PiExponentEquationProvenanceProbe.checkedCI `OAI.PiExponent.tendsto_nat_add_one_div_pow),
    ("theoremParentValueRefs", toJson theoremRefs),
    ("simpHelper", ← PiExponentEquationProvenanceProbe.checkedCI `OAI.PiExponent.tendsto_nat_add_one_div_pow._simp_1_1),
    ("definitionWParent", ← PiExponentEquationProvenanceProbe.checkedCI primaryW),
    ("definitionWEquationNames", toJson (names.map Name.toString)),
    ("definitionWEquationInverse", toJson (inverse?.map Name.toString)),
    ("dimensionWEquation", ← PiExponentEquationProvenanceProbe.checkedCI `OAI.PiExponent.dimensionW.eq_1),
    ("definitionVParent", ← PiExponentEquationProvenanceProbe.checkedCI `OAI.PiExponent.dimensionV),
    ("definitionVFullValueRefs", toJson definitionRefs),
    ("dimensionVHelper", ← PiExponentEquationProvenanceProbe.checkedCI `OAI.PiExponent.dimensionV._proof_1),
    ("theoremProofValuesExported", toJson false)]
  IO.FS.writeFile output result.compress

end DimensionMarginExtraCI

run_meta do
  DimensionMarginExtraCI.exportExtra "generated" "missions/pi-irrationality-measure/verification/dm-extra-ci/generated-extra.json"
