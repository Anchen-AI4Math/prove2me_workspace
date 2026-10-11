import SketchedParent
import Lean
import Lean.Util.CollectAxioms
import GraphExprDag

set_option maxHeartbeats 12000000
set_option maxRecDepth 200000
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix Topology
open Finset Polynomial Filter
open ZetaNine ZetaNine.GraphBridge ZetaNine.CoefficientMapMatrix ZetaNine.CoefficientMapAggregate
open ZetaNine.AnalyticWeightedBound

/-! Complete type applications and seven required actual boundary controls. -/

example (n : ℕ) (hn2 : 2 ≤ n)
    (hn : Even n) (b a : ℤ) :
    (selectedIntegerMultiplier n hn2 hn b a).natDegree ≤ 4 := by
  exact ZetaNine.GraphBridge.one_selectedMultiplier_degree_le n hn2 hn b a

example
    (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b a : ℤ) :
    weightedCoefficientHeight n (selectedIntegerMultiplier n hn2 hn b a) =
      selectedInverseWeightedNorm n b a := by
  exact ZetaNine.GraphBridge.one_selectedMultiplier_height_eq_inverseNorm n hn2 hn b a

example (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    CoefficientMap.actualR n (k : ℚ) = 0 := by
  exact ZetaNine.GraphBridge.one_actualR_zero_of_pos_le n k hk hkn

example (n k : ℕ) (hk : n < k) :
    0 < CoefficientMap.actualR n (k : ℚ) := by
  exact ZetaNine.GraphBridge.one_actualR_pos_above_n n k hk

example (W : ℚ[X]) (t : ℚ) :
    ((W.eval t : ℚ) : ℝ) = (W.map (Rat.castHom ℝ)).eval (t : ℝ) := by
  exact ZetaNine.GraphBridge.one_real_mapped_eval W t

example (n : ℕ) (W : ℚ[X]) (j : ℕ) :
    actualWeightedSequence n W (j + n) =
      (CoefficientMap.actualR n ((j + n + 1 : ℕ) : ℚ) : ℝ) *
        (W.map (Rat.castHom ℝ)).eval
          (((j + n + 1 : ℕ) : ℝ) * (((j + n + 1 : ℕ) : ℝ) + n)) := by
  exact ZetaNine.GraphBridge.one_actualWeighted_tail_term n W j

example (n : ℕ) (W : ℚ[X]) :
    (∑ m ∈ range n, actualWeightedSequence n W m) = 0 := by
  exact ZetaNine.GraphBridge.one_actualWeighted_head_zero n W

example (n j : ℕ) :
    ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) ≤
      (((j + n + 1 : ℕ) : ℝ) * (((j + n + 1 : ℕ) : ℝ) + n)) := by
  exact ZetaNine.GraphBridge.one_actualWeighted_tail_center_le n j

example (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b a : ℤ)
    (hcoeff : ∀ i : ℕ, 0 ≤
      (Polynomial.taylor (((n : ℝ) + 1) * (2 * (n : ℝ) + 1))
        ((selectedIntegerMultiplier n hn2 hn b a).map (Rat.castHom ℝ))).coeff i)
    (hsample : 0 < ((selectedIntegerMultiplier n hn2 hn b a).map (Rat.castHom ℝ)).eval
      (((n : ℝ) + 2) * ((n : ℝ) + 2 + (n : ℝ)))) :
    0 < (b : ℝ) + (a : ℝ) * (riemannZeta (9 : ℂ)).re := by
  exact ZetaNine.GraphBridge.one_selected_actual_form_pos n hn2 hn b a hcoeff hsample

example
    (hshort : SelectedInversePositiveConeMargin) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ m : ℕ in atTop,
        ∃ b a : ℤ,
          (b : ℝ) + (a : ℝ) * (riemannZeta (9 : ℂ)).re ≠ 0 ∧
          |(b : ℝ) + (a : ℝ) * (riemannZeta (9 : ℂ)).re| <
            Real.exp (-(c * (m : ℝ))) := by
  exact ZetaNine.GraphBridge.one_small_forms_of_selected_inverse_positive_cone_margin hshort

/- Boundary: actual kernel zero head at smallest even scale. -/
example : CoefficientMap.actualR 2 (1 : ℚ) = 0 :=
  one_actualR_zero_of_pos_le 2 1 (by omega) (by omega)
example : CoefficientMap.actualR 2 (2 : ℚ) = 0 :=
  one_actualR_zero_of_pos_le 2 2 (by omega) (by omega)
example : 0 < CoefficientMap.actualR 2 (3 : ℚ) :=
  one_actualR_pos_above_n 2 3 (by omega)
example : CoefficientMap.actualR 0 (1 : ℚ) > 0 :=
  one_actualR_pos_above_n 0 1 (by omega)
example : (∑ m ∈ range 0, actualWeightedSequence 0 (0 : ℚ[X]) m) = 0 :=
  one_actualWeighted_head_zero 0 0
example : (((2 : ℝ)+1)*(2*2+1)) < (((2 : ℝ)+2)*((2 : ℝ)+2+2)) := by norm_num
example : ∀ j : ℕ, (((2 : ℝ)+1)*(2*2+1)) ≤
    (((j+2+1:ℕ):ℝ)*(((j+2+1:ℕ):ℝ)+2)) :=
  one_actualWeighted_tail_center_le 2


example : ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∃ b a : ℤ,
          (b : ℝ) + (a : ℝ) * (riemannZeta (9 : ℂ)).re ≠ 0 ∧
          |(b : ℝ) + (a : ℝ) * (riemannZeta (9 : ℂ)).re| <
            Real.exp (-(c * (n : ℝ))) := by
  exact solution

open Lean Meta Elab Command

private partial def directConsts : Expr → Array Name
  | .const n _ => #[n]
  | .app f a => directConsts f ++ directConsts a
  | .lam _ t b _ => directConsts t ++ directConsts b
  | .forallE _ t b _ => directConsts t ++ directConsts b
  | .letE _ t v b _ => directConsts t ++ directConsts v ++ directConsts b
  | .mdata _ e => directConsts e
  | .proj _ _ e => directConsts e
  | _ => #[]

private def emit (j : Json) : MetaM Unit := liftM <| IO.println ("GO_RECORD|" ++ j.compress)

run_cmd liftTermElabM do
  let initialEnv ← getEnv
  let ownNames := initialEnv.constants.toList.map Prod.fst |>.filter (fun n =>
    let s := n.toString
    (s.startsWith "ZetaNine.GraphBridge." &&
      n != ``ZetaNine.GraphBridge.selected_inverse_positive_cone_margin) ||
    s == "solution" || s.startsWith "solution." ||
    s.startsWith "_private.SketchedParent." ||
    s.startsWith "_private.SketchedParentV" ||
    s.startsWith "_private.Definitions.Def_ZetaNine_GraphBridge_OneForm." ||
    s.startsWith "_private.Definitions.Def_ZetaNine_GraphBridge_TwoForm.")
  emit <| Json.mkObj [("kind",toJson "complete_own_declaration_inventory"),
    ("names",toJson (ownNames.map Name.toString))]
  for n in ownNames do
    let ci ← getConstInfo n
    let some value := ci.value? true | throwError "Missing own full proof value {n}"
    let cs := directConsts value
    unless !cs.contains ``sorryAx do throwError "Own proof directly admits {n}"
    let payload ← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip ci.type value)
    let (ty,val) ← ofExcept (IndependentLosslessExprDagV1.decode payload)
    unless Expr.equal ci.type ty && Expr.equal value val do throwError "DAG byte fields changed {n}"
    unless ← isDefEq (← inferType val) ci.type do throwError "Wrong complete value type {n}"
    let axs ← Lean.collectAxioms n
    for a in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound, ``sorryAx].contains a do
        throwError "Unrecorded axiom dependency {n} {a}"
    emit <| Json.mkObj [("kind",toJson "own_complete_kernel_value"),("name",toJson n.toString),
      ("full_payload",toJson payload.compress),("direct_constants",toJson (cs.map Name.toString)),
      ("axioms",toJson (axs.map Name.toString)),("catalogue_sorryAx_is_explicit_sketch_assumption",toJson true),
      ("own_direct_sorryAx",toJson false),("complete_inferType_matches",toJson true)]
  let env ← getEnv
  for n in env.header.moduleNames do
    let found ← Lean.findOLean n
    let canonical ← IO.FS.realPath found
    emit <| Json.mkObj [("kind",toJson "actual_module_resolver"),("module",toJson n.toString),
      ("found_olean",toJson found.toString),("canonical_olean",toJson canonical.toString)]
