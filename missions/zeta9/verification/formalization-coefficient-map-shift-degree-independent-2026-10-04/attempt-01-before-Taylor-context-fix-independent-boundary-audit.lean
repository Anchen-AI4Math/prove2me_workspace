import missions.zeta9.formalization.CoefficientMapShiftDegree
import Lean
open Lean Meta Polynomial
open ZetaNine.CoefficientMapShiftDegree
set_option autoImplicit false
set_option pp.fullNames true
set_option pp.universes false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2200000

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
  have hp : shiftA n * H ≠ 0 := mul_ne_zero (shiftA_monic n).ne_zero hH
  have hq : shiftB n * H.comp (X+C 1) ≠ 0 := mul_ne_zero (shiftB_monic n).ne_zero hHs
  have hpd : (shiftA n * H).natDegree = 11+H.natDegree := by
    rw [(shiftA_monic n).natDegree_mul' hH,shiftA_natDegree]
  have hqd : (shiftB n * H.comp (X+C 1)).natDegree = 11+H.natDegree := by
    rw [(shiftB_monic n).natDegree_mul' hHs,shiftB_natDegree,natDegree_taylor]
  have hd : (shiftA n * H).degree = (shiftB n * H.comp (X+C 1)).degree := by
    rw [degree_eq_natDegree hp,degree_eq_natDegree hq,hpd,hqd]
  have hlc : (shiftA n * H).leadingCoeff = (shiftB n * H.comp (X+C 1)).leadingCoeff := by
    simp [leadingCoeff_mul,(shiftA_monic n).leadingCoeff,(shiftB_monic n).leadingCoeff,leadingCoeff_taylor]
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
  actual_shift_difference_small_degree_implies_zero n hn H hd hsmall

theorem shift_ind_original_even_quartic_interface (n : ℕ) (hn2 : 2≤n) (hn : Even n) (H : ℚ[X])
    (hd : H.natDegree ≤ 7*n-3) (hsmall : (shiftDifference n H).natDegree ≤ 8) : H=0 :=
  actual_shift_difference_small_degree_implies_zero n (by omega) H hd hsmall

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

run_meta do
  let emit (name : Name) : MetaM Unit := do
    let ci ← getConstInfo name
    let typ ← ppExpr ci.type
    let axs ← Lean.collectAxioms name
    let val ← match ci with
      | .defnInfo d => pure (Json.str (← ppExpr d.value).pretty)
      | _ => pure Json.null
    IO.println (Json.mkObj [("declaration",Json.str name.toString),("type",Json.str typ.pretty),
      ("axioms",toJson (axs.toList.map Name.toString)),("definitionValue",val)]).compress
  for name in [
    `shift_ind_actual_eval,`shift_ind_zero_every_n,`shift_ind_zero_degree_every_n,
    `shift_ind_constant_shift,`shift_ind_constant_nextCoeff,`shift_ind_constant_coefficient,
    `shift_ind_negative_nonmonic_constant,`shift_ind_n_zero_constant,
    `shift_ind_general_top_cancellation,`shift_ind_exact_degree_in_domain,
    `shift_ind_actual_leadingCoeff_in_domain,`shift_ind_low_degree_interface,
    `shift_ind_original_even_quartic_interface,`shift_ind_resonance_n_one,
    `shift_ind_resonance_operator_still_nonzero,`shift_ind_n_one_degree_last_allowed,
    `shift_ind_n_two_nonmonic] do emit name
