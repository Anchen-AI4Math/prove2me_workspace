import missions.zeta9.formalization.CoefficientMapAggregate
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapAggregateValueComparison

open scoped BigOperators
open Finset Polynomial
open CoefficientMapJet CoefficientMapInjectivity CoefficientMapReflection

def aggregate (n : ℕ) (W : ℚ[X]) (i : Fin 5) : ℚ :=
  match i.val with
  | 0 => CoefficientMapFiniteSum.constantTerm n W
  | 1 => CoefficientMapFiniteSum.rho n 3 W
  | 2 => CoefficientMapFiniteSum.rho n 5 W
  | 3 => CoefficientMapFiniteSum.rho n 7 W
  | _ => CoefficientMapFiniteSum.rho n 9 W

def coordinatePolynomial (a : Fin 5 → ℚ) : ℚ[X] :=
  ∑ i : Fin 5, C (a i) * X ^ i.val

def polynomialCoordinates (W : ℚ[X]) (i : Fin 5) : ℚ := W.coeff i.val

end ZetaNine.CoefficientMapAggregateValueComparison

open Lean Meta
set_option pp.fullNames true
set_option pp.universes false

private def remapAggregateName (n : Name) : Name :=
  if n == `ZetaNine.CoefficientMapAggregate then
    `ZetaNine.CoefficientMapAggregateValueComparison
  else match n with
    | .str p s => .str (remapAggregateName p) s
    | .num p i => .num (remapAggregateName p) i
    | .anonymous => .anonymous
run_meta do
  for name in [`ZetaNine.CoefficientMapAggregate.actual_constant_add, `ZetaNine.CoefficientMapAggregate.actual_constant_smul, `ZetaNine.CoefficientMapAggregate.actual_local_coefficient_add, `ZetaNine.CoefficientMapAggregate.actual_local_coefficient_smul, `ZetaNine.CoefficientMapAggregate.actual_rho_add, `ZetaNine.CoefficientMapAggregate.actual_rho_smul, `ZetaNine.CoefficientMapAggregate.aggregate_add, `ZetaNine.CoefficientMapAggregate.aggregate_smul, `ZetaNine.CoefficientMapAggregate.coordinatePolynomial_add, `ZetaNine.CoefficientMapAggregate.coordinatePolynomial_smul] do
    let ci ← getConstInfo name
    let typ ← ppExpr ci.type
    let aliasExpr := ci.type.replace fun e => match e with
      | .const n ls => if (`ZetaNine.CoefficientMapAggregate).isPrefixOf n then
          some (.const (remapAggregateName n) ls) else none
      | _ => none
    let aliasType ← ppExpr aliasExpr
    let axs ← Lean.collectAxioms name
    IO.println (Json.mkObj [("declaration",Json.str name.toString),
      ("original_type",Json.str typ.pretty),("alias_type",Json.str aliasType.pretty),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
