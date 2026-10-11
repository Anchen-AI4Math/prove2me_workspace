import Solutions.Sol_ZetaNine_CoefficientMapShiftDegree_actual_shift_difference_small_degree_implies_zero
import Lean
open Lean Meta Polynomial
open ZetaNine.CoefficientMapShiftDegree
set_option autoImplicit false
set_option pp.fullNames true
set_option pp.universes false
set_option maxHeartbeats 2200000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem checked_actual_operator_eval (n : ℕ) (H : ℚ[X]) (t : ℚ) :
    (shiftDifference n H).eval t =
      (t - ((n : ℚ) + 1)) * (t + (n : ℚ)) ^ 10 * H.eval t -
      t ^ 10 * (t + (2 * (n : ℚ) + 1)) * H.eval (t + 1) := by
  simp [shiftDifference, shiftA, shiftB, eval_comp]

theorem checked_degree_zero_shift (H : ℚ[X]) (hH : H.natDegree = 0) :
    H.comp (X + C 1) = H := by
  rw [eq_C_of_natDegree_eq_zero hH]
  simp

theorem checked_n_one_constant_coefficient :
    (shiftDifference 1 (1 : ℚ[X])).coeff 10 = 5 := by
  have h := actual_shift_difference_coefficient 1 (1 : ℚ[X]) one_ne_zero
  norm_num at h
  exact h

theorem checked_n_one_last_allowed_coefficient :
    (shiftDifference 1 (X ^ 4 : ℚ[X])).coeff 14 = 1 := by
  have h := actual_shift_difference_coefficient 1 (X ^ 4 : ℚ[X]) (pow_ne_zero 4 X_ne_zero)
  norm_num at h
  exact h

theorem checked_n_one_resonance_outside_domain :
    (shiftDifference 1 (X ^ 5 : ℚ[X])).coeff 15 = 0 ∧
      (X ^ 5 : ℚ[X]) ≠ 0 ∧ ¬ (X ^ 5 : ℚ[X]).natDegree ≤ 7 * 1 - 3 := by
  have h := actual_shift_difference_coefficient 1 (X ^ 5 : ℚ[X]) (pow_ne_zero 5 X_ne_zero)
  norm_num at h
  exact ⟨h, pow_ne_zero 5 X_ne_zero, by norm_num⟩

theorem checked_n_two_nonmonic_last_allowed :
    (shiftDifference 2 (C 7 * X ^ 11 : ℚ[X])).coeff 21 = 7 := by
  have hC : (C 7 : ℚ[X]) ≠ 0 := by norm_num
  have hX : (X ^ 11 : ℚ[X]) ≠ 0 := pow_ne_zero 11 X_ne_zero
  have hdeg : (C 7 * X ^ 11 : ℚ[X]).natDegree = 11 := by
    rw [natDegree_mul hC hX]
    simp
  have hlead : (C 7 * X ^ 11 : ℚ[X]).leadingCoeff = 7 := by simp [leadingCoeff_mul]
  have h := actual_shift_difference_coefficient 2 (C 7 * X ^ 11 : ℚ[X]) (mul_ne_zero hC hX)
  norm_num [hdeg, hlead] at h
  exact h

theorem checked_exact_kernel_degree_interface (n : ℕ) (hn : 1 ≤ n) (H : ℚ[X])
    (hdeg : H.natDegree ≤ 7 * n - 3)
    (hsmall : (shiftDifference n H).natDegree ≤ 8) : H = 0 :=
  checked_actual_shift_difference_small_degree_implies_zero n hn H hdeg hsmall

theorem shift_ind_actual_eval (n : ℕ) (H : ℚ[X]) (t : ℚ) :
    (shiftDifference n H).eval t =
      (t-((n : ℚ)+1))*(t+(n : ℚ))^10*H.eval t -
        t^10*(t+(2*(n : ℚ)+1))*H.eval (t+1) := by
  simp [shiftDifference,shiftA,shiftB,eval_comp]

theorem shift_ind_zero_every_n (n : ℕ) : shiftDifference n (0 : ℚ[X]) = 0 := by
  simp [shiftDifference]

theorem shift_ind_zero_degree_every_n (n : ℕ) : (shiftDifference n (0 : ℚ[X])).natDegree = 0 := by
  rw [shift_ind_zero_every_n];rfl

theorem shift_ind_constant_shift (a : ℚ) : (C a).comp (X+C 1) = C a := by simp

theorem shift_ind_constant_nextCoeff (a : ℚ) : (C a : ℚ[X]).nextCoeff = 0 := by simp

theorem shift_ind_constant_coefficient (n : ℕ) (a : ℚ) :
    (shiftDifference n (C a)).coeff 10 = (7*(n : ℚ)-2)*a := by
  by_cases ha : a=0
  · simp [ha,shiftDifference]
  have h := actual_shift_difference_coefficient n (C a) (by simpa using ha)
  simpa using h

theorem shift_ind_negative_nonmonic_constant (n : ℕ) :
    (shiftDifference n (C (-3))).coeff 10 = -3*(7*(n : ℚ)-2) := by
  rw [shift_ind_constant_coefficient];ring

theorem shift_ind_n_zero_constant : (shiftDifference 0 (C (7 : ℚ))).coeff 10 = -14 := by
  rw [shift_ind_constant_coefficient];norm_num

theorem shift_ind_general_top_cancellation (n : ℕ) (H : ℚ[X]) :
    (shiftDifference n H).natDegree ≤ H.natDegree+10 := by
  by_cases hH : H=0
  · simp [hH,shiftDifference]
  have hHs : H.comp (X+C 1) ≠ 0 := by
    intro h
    exact hH ((taylor_eq_zero (r := (1 : ℚ)) (f := H)).mp h)
  have hHsdeg : (H.comp (X+C 1)).natDegree = H.natDegree := natDegree_taylor H 1
  have hHslead : (H.comp (X+C 1)).leadingCoeff = H.leadingCoeff := leadingCoeff_taylor 1 H
  have hp : shiftA n * H ≠ 0 := mul_ne_zero (shiftA_monic n).ne_zero hH
  have hq : shiftB n * H.comp (X+C 1) ≠ 0 := mul_ne_zero (shiftB_monic n).ne_zero hHs
  have hpd : (shiftA n * H).natDegree = 11+H.natDegree := by
    rw [(shiftA_monic n).natDegree_mul' hH,shiftA_natDegree]
  have hqd : (shiftB n * H.comp (X+C 1)).natDegree = 11+H.natDegree := by
    rw [(shiftB_monic n).natDegree_mul' hHs,shiftB_natDegree,hHsdeg]
  have hd : (shiftA n * H).degree = (shiftB n * H.comp (X+C 1)).degree := by
    rw [degree_eq_natDegree hp,degree_eq_natDegree hq,hpd,hqd]
  have hlc : (shiftA n * H).leadingCoeff = (shiftB n * H.comp (X+C 1)).leadingCoeff := by
    simp only [leadingCoeff_mul,(shiftA_monic n).leadingCoeff,(shiftB_monic n).leadingCoeff,hHslead,one_mul]
  have hlt := degree_sub_lt_left hd hp hlc
  by_cases hz : shiftDifference n H=0
  · simp [hz]
  have hh : (shiftDifference n H).natDegree < 11+H.natDegree := by
    apply (natDegree_lt_iff_degree_lt hz).mpr
    simpa only [shiftDifference,degree_eq_natDegree hp,hpd] using hlt
  omega

theorem shift_ind_exact_degree_in_domain (n : ℕ) (hn : 1≤n) (H : ℚ[X])
    (hH : H≠0) (hd : H.natDegree ≤ 7*n-3) :
    (shiftDifference n H).natDegree = H.natDegree+10 :=
  Nat.le_antisymm (shift_ind_general_top_cancellation n H)
    (actual_shift_difference_degree_lower_bound n hn H hH hd)

theorem shift_ind_actual_leadingCoeff_in_domain (n : ℕ) (hn : 1≤n) (H : ℚ[X])
    (hH : H≠0) (hd : H.natDegree ≤ 7*n-3) :
    (shiftDifference n H).leadingCoeff = (7*(n : ℚ)-2-(H.natDegree : ℚ))*H.leadingCoeff := by
  change (shiftDifference n H).coeff (shiftDifference n H).natDegree = _
  rw [shift_ind_exact_degree_in_domain n hn H hH hd]
  exact actual_shift_difference_coefficient n H hH

theorem shift_ind_low_degree_interface (n : ℕ) (hn : 1≤n) (H : ℚ[X])
    (hd : H.natDegree ≤ 7*n-3) (hsmall : (shiftDifference n H).natDegree ≤ 8) : H=0 :=
  checked_actual_shift_difference_small_degree_implies_zero n hn H hd hsmall

theorem shift_ind_original_even_quartic_interface (n : ℕ) (hn2 : 2≤n) (hn : Even n) (H : ℚ[X])
    (hd : H.natDegree ≤ 7*n-3) (hsmall : (shiftDifference n H).natDegree ≤ 8) : H=0 :=
  checked_actual_shift_difference_small_degree_implies_zero n (by omega) H hd hsmall

theorem shift_ind_resonance_n_one : (shiftDifference 1 (X^5 : ℚ[X])).coeff 15=0 ∧
    ¬ (X^5 : ℚ[X]).natDegree ≤ 7*1-3 := by
  have h := actual_shift_difference_coefficient 1 (X^5 : ℚ[X]) (pow_ne_zero 5 X_ne_zero)
  norm_num at h
  exact ⟨h,by norm_num⟩

theorem shift_ind_resonance_operator_still_nonzero :
    (shiftDifference 1 (X^5 : ℚ[X])).eval 1 = -1152 := by
  norm_num [shiftDifference,shiftA,shiftB,eval_comp]

theorem shift_ind_n_one_degree_last_allowed : (shiftDifference 1 (X^4 : ℚ[X])).natDegree = 14 := by
  have h := shift_ind_exact_degree_in_domain 1 (by omega) (X^4 : ℚ[X])
    (pow_ne_zero 4 X_ne_zero) (by norm_num)
  simpa using h

theorem shift_ind_n_two_nonmonic : (shiftDifference 2 (C 7 * X^11 : ℚ[X])).coeff 21=7 := by
  have hC : (C 7 : ℚ[X])≠0 := by norm_num
  have hX : (X^11 : ℚ[X])≠0 := pow_ne_zero 11 X_ne_zero
  have hd : (C 7 * X^11 : ℚ[X]).natDegree=11 := by rw [natDegree_mul hC hX];simp
  have hl : (C 7 * X^11 : ℚ[X]).leadingCoeff=7 := by simp [leadingCoeff_mul]
  have h := actual_shift_difference_coefficient 2 (C 7 * X^11 : ℚ[X]) (mul_ne_zero hC hX)
  norm_num [hd,hl] at h
  exact h


theorem shift_review_zero_solution (n : ℕ) (hn : 1 ≤ n) : (0 : ℚ[X]) = 0 :=
  solution n hn 0 (by simp) (by simp [shiftDifference])

theorem shift_review_zero_degree (n : ℕ) :
    (shiftDifference n (0 : ℚ[X])).degree = ⊥ ∧
    (shiftDifference n (0 : ℚ[X])).natDegree = 0 := by
  simp [shiftDifference]

theorem shift_review_nonmonic_n_zero : (shiftDifference 0 (C (-2 : ℚ))).coeff 10 = 4 := by
  have h := actual_shift_difference_coefficient 0 (C (-2 : ℚ)) (by norm_num)
  norm_num at h
  simpa only [map_neg] using h

theorem shift_review_negative_n_two : (shiftDifference 2 (C (-3 : ℚ) * X ^ 11)).coeff 21 = -3 := by
  have hC : (C (-3 : ℚ) : ℚ[X]) ≠ 0 := by norm_num
  have hX : (X ^ 11 : ℚ[X]) ≠ 0 := pow_ne_zero 11 X_ne_zero
  have hd : (C (-3 : ℚ) * X ^ 11 : ℚ[X]).natDegree = 11 := by
    rw [natDegree_mul hC hX]; simp
  have hl : (C (-3 : ℚ) * X ^ 11 : ℚ[X]).leadingCoeff = -3 := by simp [leadingCoeff_mul]
  have h := actual_shift_difference_coefficient 2 (C (-3 : ℚ) * X ^ 11) (mul_ne_zero hC hX)
  norm_num [hd,hl] at h
  simpa only [map_neg,neg_mul] using h

theorem shift_review_resonance_and_actual_eval :
    (shiftDifference 1 (X ^ 5 : ℚ[X])).coeff 15 = 0 ∧
    ¬ (X ^ 5 : ℚ[X]).natDegree ≤ 7 * 1 - 3 ∧
    (shiftDifference 1 (X ^ 5 : ℚ[X])).eval 1 = -1152 := by
  refine ⟨shift_ind_resonance_n_one.1,shift_ind_resonance_n_one.2,?_⟩
  exact shift_ind_resonance_operator_still_nonzero

theorem shift_review_resonance_nonzero : shiftDifference 1 (X ^ 5 : ℚ[X]) ≠ 0 := by
  intro h
  have hv := congrArg (fun P : ℚ[X] => P.eval 1) h
  rw [shift_ind_resonance_operator_still_nonzero] at hv
  norm_num at hv

theorem shift_review_eval_n_zero (H : ℚ[X]) (t : ℚ) :
    (shiftDifference 0 H).eval t =
      (t - 1) * t ^ 10 * H.eval t - t ^ 10 * (t + 1) * H.eval (t + 1) := by
  simp [shiftDifference,shiftA,shiftB,eval_comp]

run_meta do
  let emit (kind : String) (name : Name) : MetaM Unit := do
    let ci ← getConstInfo name
    let typ ← ppExpr ci.type
    let axs ← Lean.collectAxioms name
    let val ← match ci with
      | .defnInfo d => pure (Json.str (← ppExpr d.value).pretty)
      | _ => pure Json.null
    IO.println (Json.mkObj [("kind",Json.str kind),("declaration",Json.str name.toString),
      ("type",Json.str typ.pretty),("definitionValue",val),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
  for name in [`ZetaNine.CoefficientMapShiftDegree.shiftA, `ZetaNine.CoefficientMapShiftDegree.shiftB, `ZetaNine.CoefficientMapShiftDegree.shiftDifference, `ZetaNine.CoefficientMapShiftDegree.actual_nextCoeff_mul, `ZetaNine.CoefficientMapShiftDegree.actual_shift_nextCoeff, `ZetaNine.CoefficientMapShiftDegree.shiftA_monic, `ZetaNine.CoefficientMapShiftDegree.shiftB_monic, `ZetaNine.CoefficientMapShiftDegree.shiftA_natDegree, `ZetaNine.CoefficientMapShiftDegree.shiftB_natDegree, `ZetaNine.CoefficientMapShiftDegree.shiftA_nextCoeff, `ZetaNine.CoefficientMapShiftDegree.shiftB_nextCoeff, `ZetaNine.CoefficientMapShiftDegree.actual_shift_difference_coefficient, `ZetaNine.CoefficientMapShiftDegree.actual_shift_difference_coefficient_ne_zero, `ZetaNine.CoefficientMapShiftDegree.actual_shift_difference_degree_lower_bound, `ZetaNine.CoefficientMapShiftDegree.checked_actual_shift_difference_small_degree_implies_zero, `checked_actual_operator_eval, `checked_degree_zero_shift, `checked_n_one_constant_coefficient, `checked_n_one_last_allowed_coefficient, `checked_n_one_resonance_outside_domain, `checked_n_two_nonmonic_last_allowed, `checked_exact_kernel_degree_interface, `shift_ind_actual_eval, `shift_ind_zero_every_n, `shift_ind_zero_degree_every_n, `shift_ind_constant_shift, `shift_ind_constant_nextCoeff, `shift_ind_constant_coefficient, `shift_ind_negative_nonmonic_constant, `shift_ind_n_zero_constant, `shift_ind_general_top_cancellation, `shift_ind_exact_degree_in_domain, `shift_ind_actual_leadingCoeff_in_domain, `shift_ind_low_degree_interface, `shift_ind_original_even_quartic_interface, `shift_ind_resonance_n_one, `shift_ind_resonance_operator_still_nonzero, `shift_ind_n_one_degree_last_allowed, `shift_ind_n_two_nonmonic] do emit "native_exact" name
  for name in [`shift_review_zero_solution, `shift_review_zero_degree, `shift_review_nonmonic_n_zero, `shift_review_negative_n_two, `shift_review_resonance_and_actual_eval, `shift_review_resonance_nonzero, `shift_review_eval_n_zero] do emit "new_independent_control" name
