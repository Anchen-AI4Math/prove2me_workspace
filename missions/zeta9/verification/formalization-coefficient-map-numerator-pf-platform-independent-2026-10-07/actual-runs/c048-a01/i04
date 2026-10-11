import missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions
import Lean
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
open Lean Meta
private partial def encodeName : Name → String
  | .anonymous => "Lean.Name.anonymous"
  | .str parent part => "(Lean.Name.mkStr " ++ encodeName parent ++ " " ++ (Json.str part).compress ++ ")"
  | .num parent part => "(Lean.Name.mkNum " ++ encodeName parent ++ " " ++ toString part ++ ")"
private partial def encodeLevel : Level → MetaM String
  | .zero => pure "Lean.Level.zero"
  | .succ a => return "(Lean.Level.succ " ++ (← encodeLevel a) ++ ")"
  | .max a b => return "(Lean.Level.max " ++ (← encodeLevel a) ++ " " ++ (← encodeLevel b) ++ ")"
  | .imax a b => return "(Lean.Level.imax " ++ (← encodeLevel a) ++ " " ++ (← encodeLevel b) ++ ")"
  | .param name => pure ("(Lean.Level.param " ++ encodeName name ++ ")")
  | .mvar _ => throwError "Unclosed universe metavariable in selected Expr"
private def encodeBinder : BinderInfo → String
  | .default => "Lean.BinderInfo.default"
  | .implicit => "Lean.BinderInfo.implicit"
  | .strictImplicit => "Lean.BinderInfo.strictImplicit"
  | .instImplicit => "Lean.BinderInfo.instImplicit"
private partial def encodeExpr : Expr → MetaM String
  | .bvar index => pure ("(Lean.Expr.bvar " ++ toString index ++ ")")
  | .sort level => return "(Lean.Expr.sort " ++ (← encodeLevel level) ++ ")"
  | .const name levels => do
      let encoded ← levels.mapM encodeLevel
      return "(Lean.Expr.const " ++ encodeName name ++ " [" ++ String.intercalate ", " encoded ++ "])"
  | .app fn arg => return "(Lean.Expr.app " ++ (← encodeExpr fn) ++ " " ++ (← encodeExpr arg) ++ ")"
  | .lam name ty body bi => return "(Lean.Expr.lam " ++ encodeName name ++ " " ++ (← encodeExpr ty) ++ " " ++ (← encodeExpr body) ++ " " ++ encodeBinder bi ++ ")"
  | .forallE name ty body bi => return "(Lean.Expr.forallE " ++ encodeName name ++ " " ++ (← encodeExpr ty) ++ " " ++ (← encodeExpr body) ++ " " ++ encodeBinder bi ++ ")"
  | .letE name ty value body nondep => return "(Lean.Expr.letE " ++ encodeName name ++ " " ++ (← encodeExpr ty) ++ " " ++ (← encodeExpr value) ++ " " ++ (← encodeExpr body) ++ " " ++ (if nondep then "true" else "false") ++ ")"
  | .lit (.natVal value) => pure ("(Lean.Expr.lit (Lean.Literal.natVal " ++ toString value ++ "))")
  | .lit (.strVal value) => pure ("(Lean.Expr.lit (Lean.Literal.strVal " ++ (Json.str value).compress ++ "))")
  | .proj name index value => return "(Lean.Expr.proj " ++ encodeName name ++ " " ++ toString index ++ " " ++ (← encodeExpr value) ++ ")"
  | .mdata _ _ => throwError "Metadata needs a separate lossless encoding; selected Expr rejected"
  | .fvar _ => throwError "Unclosed free variable in selected Expr"
  | .mvar _ => throwError "Unclosed metavariable in selected Expr"
private def emitEncoded (name : Name) (definition : Bool) : MetaM Unit := do
  let info ← getConstInfo name
  let ty ← encodeExpr info.type
  let mut pairs := [("kind",Json.str "independent_lossless_constructor_SOURCE"),
    ("declaration",Json.str name.toString),("full_type_constructor_SOURCE",Json.str ty),
    ("full_type_raw_Expr",Json.str (reprStr info.type))]
  if definition then
    let .defnInfo actual := info | throwError "Expected selected definition"
    let val ← encodeExpr actual.value
    pairs := pairs ++ [("full_value_constructor_SOURCE",Json.str val),
      ("full_value_raw_Expr",Json.str (reprStr actual.value))]
  IO.println (Json.mkObj pairs).compress
run_meta do
  emitEncoded `ZetaNine.CoefficientMap.clearedPoleProduct true
  emitEncoded `ZetaNine.CoefficientMap.poleProduct true
  emitEncoded `ZetaNine.CoefficientMapFormalTransportData.numeratorClearedSeries true
  emitEncoded `ZetaNine.CoefficientMapFormalTransportData.numeratorLocalCoefficient true
  emitEncoded `ZetaNine.CoefficientMapInjectivity.polePolynomial true
  emitEncoded `ZetaNine.CoefficientMapJet.shiftedClearedDenominator true
  emitEncoded `ZetaNine.CoefficientMapJet.shiftedVariable true
  emitEncoded `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalTruncation true
  emitEncoded `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock true
  emitEncoded `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialNumerator true
  emitEncoded `ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial true
  emitEncoded `ZetaNine.CoefficientMap.clearedPoleProduct_ne_zero false
  emitEncoded `ZetaNine.CoefficientMapInjectivity.polePolynomial_natDegree false
  emitEncoded `ZetaNine.CoefficientMapInjectivity.polePolynomial_pow_natDegree false
  emitEncoded `ZetaNine.CoefficientMapInjectivity.pole_factors_coprime false
  emitEncoded `ZetaNine.CoefficientMapJet.shiftedClearedDenominator_constant false
  emitEncoded `ZetaNine.CoefficientMapJet.shiftedClearedDenominator_constant_ne_zero false
  emitEncoded `ZetaNine.CoefficientMapJet.shiftedClearedDenominator_eval false
  emitEncoded `ZetaNine.CoefficientMapJet.shiftedVariable_eval false
  emitEncoded `ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_all_local_coefficients_zero_implies_zero false
  emitEncoded `ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_global_partial_fractions false
  emitEncoded `ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_local_coefficients_injective false
  emitEncoded `ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_polynomial_partial_fractions false
  emitEncoded `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorClearedSeries_denominator_identity false
  emitEncoded `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalCoefficient_sub false
  emitEncoded `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalTruncation_comp_eq_sum false
  emitEncoded `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalTruncation_natDegree_le false
  emitEncoded `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock_comp_own_shift false
  emitEncoded `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock_natDegree_le false
  emitEncoded `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialNumerator_eq_sum_blocks false
  emitEncoded `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialNumerator_natDegree_le false
  emitEncoded `ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_denominator_divides_actual_candidate_difference false
  emitEncoded `ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_different_block_pole_divisibility false
  emitEncoded `ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_different_block_shift_X_pow_dvd false
  emitEncoded `ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_full_candidate_matches_nine_jets false
  emitEncoded `ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_own_block_matches_nine_jets false
  emitEncoded `ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_partial_term_division false
  emitEncoded `ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial_comp_shift false
  emitEncoded `ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial_natDegree false
  emitEncoded `ZetaNine.CoefficientMapPartialFractions.polePolynomial_eval false
  emitEncoded `ZetaNine.CoefficientMapPartialFractions.polePolynomial_eval_factor false
  emitEncoded `ZetaNine.CoefficientMapPartialFractions.polePolynomial_eval_ne_zero false
  emitEncoded `ZetaNine.CoefficientMapPartialFractions.polynomial_X_pow_dvd_of_series false
  emitEncoded `ZetaNine.CoefficientMapPartialFractions.shifted_divisibility_implies_pole_divisibility false
  emitEncoded `ZetaNine.CoefficientMapPartialFractions.truncation_remainder_X_pow_dvd false
  emitEncoded `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock.eq_1 false
