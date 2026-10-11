import missions.zeta9.formalization.CoefficientMapConnection
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open Polynomial

namespace ZetaNine.CoefficientMapConnectionValueComparison

def connectionU (n : ℕ) : ℚ[X] := X * (X + C (n : ℚ))

def connectionV (n : ℕ) : ℚ[X] := X * (X + C ((n - 1 : ℕ) : ℚ))

def connectionD (n : ℕ) : ℚ[X] := (connectionU n - C ((n : ℚ) + 1)) ^ 10

def connectionH (n : ℕ) (q : ℚ[X]) : ℚ[X] :=
  (X - C ((n : ℚ) + 1)) * (X + C ((n : ℚ) + 1)) ^ 10 * q.comp (connectionV n) -
    (X + C (2 * (n : ℚ) + 1)) * (X - 1) ^ 10 *
      q.comp ((X + 1) * (X + C (n : ℚ)))

def connectionReflection (n : ℕ) : ℚ[X] := -X - C (n : ℚ)

def coefficientPolynomial (d : ℕ) (c : Fin d → ℚ) : ℚ[X] :=
  ∑ i : Fin d, c i • (X ^ i.val)

def inputP (c : Fin 15 → ℚ) : ℚ[X] :=
  coefficientPolynomial 5 (fun i => c ⟨i.val, by omega⟩)

def inputQ (c : Fin 15 → ℚ) : ℚ[X] :=
  coefficientPolynomial 10 (fun i => c ⟨i.val + 5, by omega⟩)

def connectionOperator (n : ℕ) (P q : ℚ[X]) : ℚ[X] :=
  connectionD n * P.comp (connectionU n) + connectionH n q

def connectionZ (n : ℕ) : ℚ[X] :=
  (X - C (((n : ℚ) + 1) * (2 * (n : ℚ) + 1))) *
    (X - C (((n : ℚ) + 2) * (2 * (n : ℚ) + 2))) *
    (X - C (((n : ℚ) + 3) * (2 * (n : ℚ) + 3)))

def connectionTarget (n r : ℕ) : ℚ[X] :=
  C ((((n : ℚ) + 1) * ((n : ℚ) + 2)) ^ 7) * connectionZ n *
    (X - C ((n : ℚ) + 1)) ^ r

end ZetaNine.CoefficientMapConnectionValueComparison

open Lean Meta
set_option pp.fullNames true
set_option pp.universes false
set_option pp.proofs true

private def remapConnectionName (n : Name) : Name :=
  if n == `ZetaNine.CoefficientMapConnection then
    `ZetaNine.CoefficientMapConnectionValueComparison
  else match n with
    | .str p s => .str (remapConnectionName p) s
    | .num p i => .num (remapConnectionName p) i
    | .anonymous => .anonymous

run_meta do
  for name in [`ZetaNine.CoefficientMapConnection.coefficientPolynomial_add, `ZetaNine.CoefficientMapConnection.coefficientPolynomial_smul, `ZetaNine.CoefficientMapConnection.connectionOperator_add, `ZetaNine.CoefficientMapConnection.connectionOperator_smul] do
    let ci ← getConstInfo name
    let type ← ppExpr ci.type
    let aliasExpr := ci.type.replace fun e => match e with
      | .const n ls =>
          if (`ZetaNine.CoefficientMapConnection).isPrefixOf n then
            some (.const (remapConnectionName n) ls)
          else none
      | _ => none
    let aliasType ← ppExpr aliasExpr
    let axs ← Lean.collectAxioms name
    IO.println (Json.mkObj [("declaration",Json.str name.toString),
      ("original_type",Json.str type.pretty),("alias_type",Json.str aliasType.pretty),
      ("original_type_expression_repr",Json.str (reprStr ci.type)),
      ("remapped_type_expression_repr",Json.str (reprStr aliasExpr)),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
