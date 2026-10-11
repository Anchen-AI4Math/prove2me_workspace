import missions.zeta9.formalization.CoefficientMapParameterShift

set_option autoImplicit false
set_option pp.universes true

noncomputable section
open Polynomial
open ZetaNine.CoefficientMap ZetaNine.CoefficientMapConnection
open ZetaNine.CoefficientMapParameterShift

#check @parameterScale
#check @connectionRemainder
#check @positiveProduct_add_two
#check @positiveProduct_parameter_shift
#check @negativeProduct_add_two_sub_one
#check @negativeProduct_parameter_shift
#check @poleProduct_parameter_shift
#check @factorial_parameter_shift
#check @connectionZ_eval_factors
#check @numerator_parameter_shift
#check @connectionD_eval_factors
#check @shifted_regular_conditions
#check @actual_R_parameter_shift
#check @connectionRemainder_successor
#check @connectionRemainder_difference
#check @actual_original_connection_transport
#check @five_actual_connection_transports_exist_unique

namespace ZetaNine.ParameterShiftAuthorTypeAudit

theorem expected_R_shift (n : ℕ) (t : ℚ)
    (hregular : ∀ k ≤ n + 2, t - 1 + (k : ℚ) ≠ 0) :
    actualR (n + 2) (t - 1) * (connectionD n).eval t =
      parameterScale n * (connectionZ n).eval (t * (t + (n : ℚ))) * actualR n t :=
  actual_R_parameter_shift n t hregular

theorem expected_Q_difference (n : ℕ) (hn : 1 ≤ n) (q : ℚ[X]) (t : ℚ)
    (hregular : ∀ k ≤ n + 2, t - 1 + (k : ℚ) ≠ 0) :
    connectionRemainder n q t - connectionRemainder n q (t + 1) =
      actualR n t * (connectionH n q).eval t / (connectionD n).eval t :=
  connectionRemainder_difference n hn q t hregular

theorem expected_original_transport (n : ℕ) (hn : 1 ≤ n) (r : ℕ) (P q : ℚ[X])
    (heq : connectionD n * P.comp (connectionU n) + connectionH n q =
      (connectionTarget n r).comp (connectionU n))
    (t : ℚ) (hregular : ∀ k ≤ n + 2, t - 1 + (k : ℚ) ≠ 0) :
    actualR (n + 2) (t - 1) * (t * (t + (n : ℚ)) - ((n : ℚ) + 1)) ^ r =
      actualR n t * P.eval (t * (t + (n : ℚ))) +
        (connectionRemainder n q t - connectionRemainder n q (t + 1)) :=
  actual_original_connection_transport n hn r P q heq t hregular

end ZetaNine.ParameterShiftAuthorTypeAudit

#print axioms parameterScale
#print axioms connectionRemainder
#print axioms positiveProduct_add_two
#print axioms positiveProduct_parameter_shift
#print axioms negativeProduct_add_two_sub_one
#print axioms negativeProduct_parameter_shift
#print axioms poleProduct_parameter_shift
#print axioms factorial_parameter_shift
#print axioms connectionZ_eval_factors
#print axioms numerator_parameter_shift
#print axioms connectionD_eval_factors
#print axioms shifted_regular_conditions
#print axioms actual_R_parameter_shift
#print axioms connectionRemainder_successor
#print axioms connectionRemainder_difference
#print axioms actual_original_connection_transport
#print axioms five_actual_connection_transports_exist_unique
#print axioms ZetaNine.ParameterShiftAuthorTypeAudit.expected_R_shift
#print axioms ZetaNine.ParameterShiftAuthorTypeAudit.expected_Q_difference
#print axioms ZetaNine.ParameterShiftAuthorTypeAudit.expected_original_transport
