import SketchedParent
import Lean
import Lean.Util.CollectAxioms
import GraphExprDag

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 200000
noncomputable section
open scoped BigOperators Matrix Topology
open Finset Polynomial Filter
open Lean Meta Elab Command
open ZetaNine ZetaNine.GraphBridge ZetaNine.AnalyticWeightedBound
open ZetaNine.CoefficientMapMatrix ZetaNine.CoefficientMapAggregate

example : ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∃ b₁ a₁ b₂ a₂ : ℤ,
          b₁ * a₂ ≠ b₂ * a₁ ∧
          |(b₁ : ℝ) + (a₁ : ℝ) * (riemannZeta (9 : ℂ)).re| <
            Real.exp (-(c * (n : ℝ))) ∧
          |(b₂ : ℝ) + (a₂ : ℝ) * (riemannZeta (9 : ℂ)).re| <
            Real.exp (-(c * (n : ℝ))) := by
  exact ZetaNine.exponentially_small_independent_forms_of_zeta_nine

example (hshort : SelectedInverseShortPairMargin) : ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∃ b₁ a₁ b₂ a₂ : ℤ,
          b₁ * a₂ ≠ b₂ * a₁ ∧
          |(b₁ : ℝ) + (a₁ : ℝ) * (riemannZeta (9 : ℂ)).re| <
            Real.exp (-(c * (n : ℝ))) ∧
          |(b₂ : ℝ) + (a₂ : ℝ) * (riemannZeta (9 : ℂ)).re| <
            Real.exp (-(c * (n : ℝ))) := by
  exact two_small_forms_of_selected_inverse_margin hshort

example (n : ℕ) (b a : ℤ) :
    selectedInverseWeightedNorm n b a =
      ∑ i : Fin 5,
        |((selectedIntegerPair b a ᵥ* (selectionMatrix * (actualFMatrix n)⁻¹)) i : ℝ)| *
          (n : ℝ) ^ (2 * i.val) := rfl

example : SelectedInverseShortPairMargin ↔
  (∃ δ : ℝ, 0 < δ ∧
    ∀ N : ℕ, ∃ k : ℕ, N ≤ k ∧ 2 ≤ k ∧ Even k ∧
      ∃ b₁ a₁ b₂ a₂ : ℤ,
        b₁ * a₂ ≠ b₂ * a₁ ∧
        selectedInverseWeightedNorm k b₁ a₁ ≤ Real.exp (((2641 / 250 : ℝ) - δ) * k) ∧
        selectedInverseWeightedNorm k b₂ a₂ ≤ Real.exp (((2641 / 250 : ℝ) - δ) * k)) := Iff.rfl

example (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b a : ℤ) :
    (selectedIntegerMultiplier n hn2 hn b a).natDegree ≤ 4 :=
  selectedMultiplier_degree_le n hn2 hn b a

example (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b a : ℤ) :
    weightedCoefficientHeight n (selectedIntegerMultiplier n hn2 hn b a) =
      selectedInverseWeightedNorm n b a :=
  selectedMultiplier_weightedHeight_eq_inverseNorm n hn2 hn b a

example (n N k : ℕ) (hk : max n N ≤ k) : n ≤ k ∧ N ≤ k := by omega

private partial def directConsts : Expr → Array Name
  | .const n _ => #[n]
  | .app f a => directConsts f ++ directConsts a
  | .lam _ t b _ => directConsts t ++ directConsts b
  | .forallE _ t b _ => directConsts t ++ directConsts b
  | .letE _ t v b _ => directConsts t ++ directConsts v ++ directConsts b
  | .mdata _ e => directConsts e
  | .proj _ _ e => directConsts e
  | _ => #[]

private def emit (j : Json) : MetaM Unit := liftM <| IO.println ("GT_RECORD|" ++ j.compress)

run_cmd liftTermElabM do
  for n in #[``ZetaNine.GraphBridge.selectedInverseWeightedNorm,
      ``ZetaNine.GraphBridge.SelectedInverseShortPairMargin,
      ``ZetaNine.GraphBridge.selectedMultiplier_degree_le,
      ``ZetaNine.GraphBridge.selectedMultiplier_weightedHeight_eq_inverseNorm,
      ``ZetaNine.GraphBridge.two_small_forms_of_selected_inverse_margin,
      ``ZetaNine.exponentially_small_independent_forms_of_zeta_nine] do
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
