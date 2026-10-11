import missions.zeta9.formalization.CoefficientMapMatrix
import Lean
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped Matrix BigOperators
open Polynomial
namespace IndependentMatrixBoundary
open ZetaNine CoefficientMapAggregate CoefficientMapKernelBridge CoefficientMapMatrix

theorem raw_row_B (n : Nat) (i : Fin 5) : actualFMatrix n i (0 : Fin 5) =
    CoefficientMapFiniteSum.constantTerm n ((X : Rat[X]) ^ i.val) := rfl
theorem raw_row_rho3 (n : Nat) (i : Fin 5) : actualFMatrix n i (1 : Fin 5) =
    CoefficientMapFiniteSum.rho n 3 ((X : Rat[X]) ^ i.val) := rfl
theorem raw_row_rho5 (n : Nat) (i : Fin 5) : actualFMatrix n i (2 : Fin 5) =
    CoefficientMapFiniteSum.rho n 5 ((X : Rat[X]) ^ i.val) := rfl
theorem raw_row_rho7 (n : Nat) (i : Fin 5) : actualFMatrix n i (3 : Fin 5) =
    CoefficientMapFiniteSum.rho n 7 ((X : Rat[X]) ^ i.val) := rfl
theorem raw_row_rho9 (n : Nat) (i : Fin 5) : actualFMatrix n i (4 : Fin 5) =
    CoefficientMapFiniteSum.rho n 9 ((X : Rat[X]) ^ i.val) := rfl
theorem column_entries_are_monomial_output_transposed (n : Nat) (i j : Fin 5) :
    LinearMap.toMatrix' (quarticAggregateLinearMap n) i j = aggregate n ((X : Rat[X]) ^ j.val) i := by
  rw [column_action_matrix_is_transpose]
  rfl
theorem selector00 : selectionMatrix (0 : Fin 2) (0 : Fin 5) = 1 := rfl
theorem selector01 : selectionMatrix (0 : Fin 2) (1 : Fin 5) = 0 := rfl
theorem selector02 : selectionMatrix (0 : Fin 2) (2 : Fin 5) = 0 := rfl
theorem selector03 : selectionMatrix (0 : Fin 2) (3 : Fin 5) = 0 := rfl
theorem selector04 : selectionMatrix (0 : Fin 2) (4 : Fin 5) = 0 := rfl
theorem selector10 : selectionMatrix (1 : Fin 2) (0 : Fin 5) = 0 := rfl
theorem selector11 : selectionMatrix (1 : Fin 2) (1 : Fin 5) = 0 := rfl
theorem selector12 : selectionMatrix (1 : Fin 2) (2 : Fin 5) = 0 := rfl
theorem selector13 : selectionMatrix (1 : Fin 2) (3 : Fin 5) = 0 := rfl
theorem selector14 : selectionMatrix (1 : Fin 2) (4 : Fin 5) = 1 := rfl
theorem pair_B (b a : Int) : selectedIntegerPair b a (0 : Fin 2) = (b : Rat) := rfl
theorem pair_rho9 (b a : Int) : selectedIntegerPair b a (1 : Fin 2) = (a : Rat) := rfl
theorem target_tuple (b a : Int) : selectedIntegerOutput b a =
    ![(b : Rat), 0, 0, 0, (a : Rat)] := by
  funext j
  fin_cases j <;> rfl
theorem pure_nine_output_nonzero : selectedIntegerOutput 0 1 ≠ 0 := by
  intro heq
  have h := congrFun heq (4 : Fin 5)
  change (1 : Rat) = 0 at h
  norm_num at h
theorem pure_nine_multiplier_nonzero (n : Nat) (hn2 : 2 ≤ n) (hn : Even n) :
    selectedIntegerMultiplier n hn2 hn 0 1 ≠ 0 :=
  inverseMultiplier_nonzero_of_output_nonzero n hn2 hn (selectedIntegerOutput 0 1) pure_nine_output_nonzero
theorem zero_target_multiplier_zero (n : Nat) (hn2 : 2 ≤ n) (hn : Even n) :
    selectedIntegerMultiplier n hn2 hn 0 0 = 0 := by
  have ht : selectedIntegerOutput 0 0 = 0 := by
    funext j
    simp only [selectedIntegerOutput]
    split_ifs <;> rfl
  have hz : aggregate n (0 : Rat[X]) = selectedIntegerOutput 0 0 := by
    rw [ht]
    exact (aggregateLinearMap n).map_zero
  exact (inverseMultiplier_unique n hn2 hn (selectedIntegerOutput 0 0) 0 (by simp) hz).symm
theorem pure_nine_actual_sum_and_absolute (n : Nat) (hn2 : 2 ≤ n) (hn : Even n) :
    HasSum (fun t : Nat => (CoefficientMap.weightedR n (selectedIntegerMultiplier n hn2 hn 0 1)
      ((t + 1 : Nat) : Rat) : Real)) (CoefficientMapSummation.zetaReal 9) ∧
      Summable (fun t : Nat => ‖(CoefficientMap.weightedR n (selectedIntegerMultiplier n hn2 hn 0 1)
        ((t + 1 : Nat) : Rat) : Real)‖) := by
  simpa using selectedIntegerMultiplier_actual_HasSum_and_absolute n hn2 hn 0 1
theorem concrete_even_two_det : (actualFMatrix 2).det ≠ 0 :=
  actualFMatrix_det_ne_zero 2 (by decide) (by norm_num : Even 2)
theorem concrete_even_four_det : (actualFMatrix 4).det ≠ 0 :=
  actualFMatrix_det_ne_zero 4 (by decide) (by norm_num : Even 4)
theorem rational_inverse_coefficients_scope (n : Nat) (hn2 : 2 ≤ n) (hn : Even n) (b a : Int) :
    ∃ c : Fin 5 → Rat, c = selectedIntegerPair b a ᵥ* (selectionMatrix * (actualFMatrix n)⁻¹) ∧
      selectedIntegerMultiplier n hn2 hn b a = coordinatePolynomial c := by
  refine ⟨selectedIntegerPair b a ᵥ* (selectionMatrix * (actualFMatrix n)⁻¹), rfl, ?_⟩
  rw [← selectedIntegerMultiplier_coordinates_product]
  exact (polynomial_restore _ (selectedIntegerMultiplier_natDegree_le n hn2 hn b a)).symm
end IndependentMatrixBoundary
open Lean Meta
set_option pp.fullNames true
set_option pp.proofs true
run_meta do
  let env ← getEnv
  for (name, ci) in env.constants.toList do
    unless name.getPrefix == `IndependentMatrixBoundary do continue
    let .thmInfo _ := ci | continue
    let axs ← collectAxioms name
    IO.println (Json.mkObj [("declaration",Json.str name.toString),
      ("full_type_expression_repr",Json.str (reprStr ci.type)),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
