import missions.zeta9.formalization.CoefficientMapParameterSummationTransport
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
noncomputable section
open scoped BigOperators Matrix
open Polynomial ZetaNine
open ZetaNine.CoefficientMapAggregate ZetaNine.CoefficientMapMatrix
open ZetaNine.CoefficientMapKernelBridge ZetaNine.CoefficientMapReflection
open ZetaNine.CoefficientMapSummation ZetaNine.CoefficientMapFormalTransportData
open ZetaNine.CoefficientMapFormalTransportBounds ZetaNine.CoefficientMapFormalTransportOutputs
open ZetaNine.CoefficientMapParameterSummationTransport
namespace ParameterSummationIndependentFormula
def transferMultiplier (n : ℕ) (W : ℚ[X]) : ℚ[X] :=
  coordinatePolynomial (fun l : Fin 5 => ∑ i : Fin 5,
    polynomialCoordinates W i * connectionGamma n i l)
end ParameterSummationIndependentFormula
namespace ParameterSummationIndependentWhole
theorem whole_transferMultiplier :
    ZetaNine.CoefficientMapParameterSummationTransport.transferMultiplier =
      ParameterSummationIndependentFormula.transferMultiplier := by rfl
end ParameterSummationIndependentWhole
namespace ParameterSummationIndependentExpected
theorem expected_transferMultiplier_natDegree_le (n : ℕ) (W : ℚ[X]) :
    (transferMultiplier n W).natDegree ≤ 4 := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.transferMultiplier_natDegree_le n W

theorem expected_even_add_two (n : ℕ) (hn : Even n) : Even (n + 2) := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.even_add_two n hn

theorem expected_exactL_eq_prescribed_actual_output (n : ℕ) (W : ℚ[X]) :
    exactL n W = prescribedL (aggregate n W) := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.exactL_eq_prescribed_actual_output n W

theorem expected_transfer_actual_five_outputs (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) :
    aggregate n (transferMultiplier n W) = aggregate (n + 2) W := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.transfer_actual_five_outputs n hn W hW

theorem expected_transfer_actual_exactL (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) :
    exactL n (transferMultiplier n W) = exactL (n + 2) W := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.transfer_actual_exactL n hn W hW

theorem expected_quartic_actual_HasSum_and_absolute (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (W : ℚ[X]) (hW : W.natDegree ≤ 4) :
    HasSum (actualSeries n W) (exactL n W) ∧
      Summable (fun t : ℕ => ‖actualSeries n W t‖) := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.quartic_actual_HasSum_and_absolute n hn2 hn W hW

theorem expected_actual_chosen_exactL_transport (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    exactL (n + 2) (X ^ r.val) = exactL n (connectionP n r) := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.actual_chosen_exactL_transport n hn r

theorem expected_actual_chosen_HasSum_transport (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (r : Fin 5) :
    HasSum (actualSeries (n + 2) (X ^ r.val)) (exactL n (connectionP n r)) ∧
      HasSum (actualSeries n (connectionP n r)) (exactL n (connectionP n r)) ∧
      Summable (fun t : ℕ => ‖actualSeries (n + 2) (X ^ r.val) t‖) ∧
      Summable (fun t : ℕ => ‖actualSeries n (connectionP n r) t‖) := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.actual_chosen_HasSum_transport n hn2 hn r

theorem expected_actual_chosen_tsum_transport (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (r : Fin 5) :
    (∑' t : ℕ, actualSeries (n + 2) (X ^ r.val) t) =
      ∑' t : ℕ, actualSeries n (connectionP n r) t := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.actual_chosen_tsum_transport n hn2 hn r

theorem expected_quartic_HasSum_transport (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (W : ℚ[X]) (hW : W.natDegree ≤ 4) :
    HasSum (actualSeries (n + 2) W) (exactL (n + 2) W) ∧
      HasSum (actualSeries n (transferMultiplier n W)) (exactL (n + 2) W) ∧
      Summable (fun t : ℕ => ‖actualSeries (n + 2) W t‖) ∧
      Summable (fun t : ℕ => ‖actualSeries n (transferMultiplier n W) t‖) := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.quartic_HasSum_transport n hn2 hn W hW

theorem expected_quartic_tsum_transport (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (W : ℚ[X]) (hW : W.natDegree ≤ 4) :
    (∑' t : ℕ, actualSeries (n + 2) W t) =
      ∑' t : ℕ, actualSeries n (transferMultiplier n W) t := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.quartic_tsum_transport n hn2 hn W hW

theorem expected_transferred_inverseMultiplier_eq (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (b : Fin 5 → ℚ) :
    transferMultiplier n (inverseMultiplier (n + 2) (by omega) (even_add_two n hn) b) =
      inverseMultiplier n hn2 hn b := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.transferred_inverseMultiplier_eq n hn2 hn b

theorem expected_inverseMultiplier_coordinates_transport (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (b : Fin 5 → ℚ) :
    polynomialCoordinates (inverseMultiplier (n + 2) (by omega) (even_add_two n hn) b)
        ᵥ* connectionGamma n = polynomialCoordinates (inverseMultiplier n hn2 hn b) := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.inverseMultiplier_coordinates_transport n hn2 hn b

theorem expected_chosen_transferMultiplier_eq_connectionP (n : ℕ) (hn2 : 2 ≤ n)
    (hn : Even n) (r : Fin 5) :
    transferMultiplier n (X ^ r.val) = connectionP n r := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.chosen_transferMultiplier_eq_connectionP n hn2 hn r

theorem expected_selectedIntegerMultiplier_transport (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (b a : ℤ) :
    transferMultiplier n
        (selectedIntegerMultiplier (n + 2) (by omega) (even_add_two n hn) b a) =
      selectedIntegerMultiplier n hn2 hn b a := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.selectedIntegerMultiplier_transport n hn2 hn b a

theorem expected_selectedIntegerMultiplier_parameter_HasSum (n : ℕ) (hn2 : 2 ≤ n)
    (hn : Even n) (b a : ℤ) :
    HasSum (actualSeries (n + 2)
        (selectedIntegerMultiplier (n + 2) (by omega) (even_add_two n hn) b a))
      ((b : ℝ) + (a : ℝ) * zetaReal 9) ∧
      HasSum (actualSeries n (selectedIntegerMultiplier n hn2 hn b a))
        ((b : ℝ) + (a : ℝ) * zetaReal 9) ∧
      Summable (fun t : ℕ => ‖actualSeries (n + 2)
        (selectedIntegerMultiplier (n + 2) (by omega) (even_add_two n hn) b a) t‖) ∧
      Summable (fun t : ℕ => ‖actualSeries n (selectedIntegerMultiplier n hn2 hn b a) t‖) := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.selectedIntegerMultiplier_parameter_HasSum n hn2 hn b a

theorem expected_selectedIntegerMultiplier_parameter_tsum (n : ℕ) (hn2 : 2 ≤ n)
    (hn : Even n) (b a : ℤ) :
    (∑' t : ℕ, actualSeries (n + 2)
      (selectedIntegerMultiplier (n + 2) (by omega) (even_add_two n hn) b a) t) =
      ∑' t : ℕ, actualSeries n (selectedIntegerMultiplier n hn2 hn b a) t := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.selectedIntegerMultiplier_parameter_tsum n hn2 hn b a

end ParameterSummationIndependentExpected
namespace ParameterSummationIndependentBoundary
theorem n1_exact_r0 :
    exactL (1 + 2) (X ^ (0 : Fin 5).val) = exactL 1 (connectionP 1 (0 : Fin 5)) := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.actual_chosen_exactL_transport 1 (by decide) (0 : Fin 5)

theorem n2_HasSum_r0 :
    HasSum (actualSeries (2 + 2) (X ^ (0 : Fin 5).val)) (exactL 2 (connectionP 2 (0 : Fin 5))) ∧
      HasSum (actualSeries 2 (connectionP 2 (0 : Fin 5))) (exactL 2 (connectionP 2 (0 : Fin 5))) ∧
      Summable (fun t : ℕ => ‖actualSeries (2 + 2) (X ^ (0 : Fin 5).val) t‖) ∧
      Summable (fun t : ℕ => ‖actualSeries 2 (connectionP 2 (0 : Fin 5)) t‖) := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.actual_chosen_HasSum_transport 2 (by decide) (by decide) (0 : Fin 5)

theorem n2_HasSum_r4 :
    HasSum (actualSeries (2 + 2) (X ^ (4 : Fin 5).val)) (exactL 2 (connectionP 2 (4 : Fin 5))) ∧
      HasSum (actualSeries 2 (connectionP 2 (4 : Fin 5))) (exactL 2 (connectionP 2 (4 : Fin 5))) ∧
      Summable (fun t : ℕ => ‖actualSeries (2 + 2) (X ^ (4 : Fin 5).val) t‖) ∧
      Summable (fun t : ℕ => ‖actualSeries 2 (connectionP 2 (4 : Fin 5)) t‖) := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.actual_chosen_HasSum_transport 2 (by decide) (by decide) (4 : Fin 5)

theorem n2_tsum_r4 :
    (∑' t : ℕ, actualSeries (2 + 2) (X ^ (4 : Fin 5).val) t) =
      ∑' t : ℕ, actualSeries 2 (connectionP 2 (4 : Fin 5)) t := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.actual_chosen_tsum_transport 2 (by decide) (by decide) (4 : Fin 5)

theorem n2_transfer_r0 :
    transferMultiplier 2 (X ^ (0 : Fin 5).val) = connectionP 2 (0 : Fin 5) := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.chosen_transferMultiplier_eq_connectionP 2 (by decide) (by decide) (0 : Fin 5)

theorem n2_transfer_r4 :
    transferMultiplier 2 (X ^ (4 : Fin 5).val) = connectionP 2 (4 : Fin 5) := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.chosen_transferMultiplier_eq_connectionP 2 (by decide) (by decide) (4 : Fin 5)

theorem n2_selected_B :
    HasSum (actualSeries (2 + 2)
        (selectedIntegerMultiplier (2 + 2) (by omega) (even_add_two 2 (by decide)) (1 : ℤ) (0 : ℤ)))
      (((1 : ℤ) : ℝ) + ((0 : ℤ) : ℝ) * zetaReal 9) ∧
      HasSum (actualSeries 2 (selectedIntegerMultiplier 2 (by decide) (by decide) (1 : ℤ) (0 : ℤ)))
        (((1 : ℤ) : ℝ) + ((0 : ℤ) : ℝ) * zetaReal 9) ∧
      Summable (fun t : ℕ => ‖actualSeries (2 + 2)
        (selectedIntegerMultiplier (2 + 2) (by omega) (even_add_two 2 (by decide)) (1 : ℤ) (0 : ℤ)) t‖) ∧
      Summable (fun t : ℕ => ‖actualSeries 2 (selectedIntegerMultiplier 2 (by decide) (by decide) (1 : ℤ) (0 : ℤ)) t‖) := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.selectedIntegerMultiplier_parameter_HasSum 2 (by decide) (by decide) (1 : ℤ) (0 : ℤ)

theorem n2_selected_A :
    HasSum (actualSeries (2 + 2)
        (selectedIntegerMultiplier (2 + 2) (by omega) (even_add_two 2 (by decide)) (0 : ℤ) (1 : ℤ)))
      (((0 : ℤ) : ℝ) + ((1 : ℤ) : ℝ) * zetaReal 9) ∧
      HasSum (actualSeries 2 (selectedIntegerMultiplier 2 (by decide) (by decide) (0 : ℤ) (1 : ℤ)))
        (((0 : ℤ) : ℝ) + ((1 : ℤ) : ℝ) * zetaReal 9) ∧
      Summable (fun t : ℕ => ‖actualSeries (2 + 2)
        (selectedIntegerMultiplier (2 + 2) (by omega) (even_add_two 2 (by decide)) (0 : ℤ) (1 : ℤ)) t‖) ∧
      Summable (fun t : ℕ => ‖actualSeries 2 (selectedIntegerMultiplier 2 (by decide) (by decide) (0 : ℤ) (1 : ℤ)) t‖) := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.selectedIntegerMultiplier_parameter_HasSum 2 (by decide) (by decide) (0 : ℤ) (1 : ℤ)

theorem n2_selected_tsum :
    (∑' t : ℕ, actualSeries (2 + 2)
      (selectedIntegerMultiplier (2 + 2) (by omega) (even_add_two 2 (by decide)) (1 : ℤ) (1 : ℤ)) t) =
      ∑' t : ℕ, actualSeries 2 (selectedIntegerMultiplier 2 (by decide) (by decide) (1 : ℤ) (1 : ℤ)) t := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.selectedIntegerMultiplier_parameter_tsum 2 (by decide) (by decide) (1 : ℤ) (1 : ℤ)

end ParameterSummationIndependentBoundary
