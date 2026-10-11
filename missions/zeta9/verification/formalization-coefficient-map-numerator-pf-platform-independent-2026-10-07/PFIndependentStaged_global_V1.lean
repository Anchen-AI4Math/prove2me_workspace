import Solutions.Sol_ZetaNine_CoefficientMapNumeratorPF_global
import Lean
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
noncomputable section
open scoped BigOperators
open Finset Polynomial ZetaNine
open ZetaNine.CoefficientMapJet ZetaNine.CoefficientMapInjectivity
open ZetaNine.CoefficientMapPartialFractions
open ZetaNine.CoefficientMapFormalTransportData
open ZetaNine.CoefficientMapNumeratorPartialFractions
namespace PFIndependentFormula
def numeratorClearedSeries (m j : ℕ) (A : ℚ[X]) : PowerSeries ℚ :=
  ((A.comp (ZetaNine.CoefficientMapJet.shiftedVariable j) : ℚ[X]) : PowerSeries ℚ) *
    ((ZetaNine.CoefficientMapJet.shiftedClearedDenominator m j : PowerSeries ℚ) ^ 9)⁻¹
def numeratorLocalCoefficient (m j s : ℕ) (A : ℚ[X]) : ℚ :=
  PowerSeries.coeff (9 - s) (ZetaNine.CoefficientMapFormalTransportData.numeratorClearedSeries m j A)
def numeratorLocalTruncation (m j : ℕ) (A : ℚ[X]) : ℚ[X] :=
  PowerSeries.trunc 9 (ZetaNine.CoefficientMapFormalTransportData.numeratorClearedSeries m j A)
def numeratorPartialBlock (m j : ℕ) (A : ℚ[X]) : ℚ[X] :=
  ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial m j ^ 9 *
    (ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalTruncation m j A).comp (X + C (j : ℚ))
def numeratorPartialNumerator (m : ℕ) (A : ℚ[X]) : ℚ[X] :=
  ∑ j ∈ range (m + 1), ∑ s ∈ Icc 1 9,
    C (ZetaNine.CoefficientMapFormalTransportData.numeratorLocalCoefficient m j s A) *
      ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial m j ^ 9 * (X + C (j : ℚ)) ^ (9 - s)
end PFIndependentFormula
theorem whole_rfl_numeratorClearedSeries : ZetaNine.CoefficientMapFormalTransportData.numeratorClearedSeries = PFIndependentFormula.numeratorClearedSeries := by rfl
theorem whole_rfl_numeratorLocalCoefficient : ZetaNine.CoefficientMapFormalTransportData.numeratorLocalCoefficient = PFIndependentFormula.numeratorLocalCoefficient := by rfl
theorem whole_rfl_numeratorLocalTruncation : ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalTruncation = PFIndependentFormula.numeratorLocalTruncation := by rfl
theorem whole_rfl_numeratorPartialBlock : ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock = PFIndependentFormula.numeratorPartialBlock := by rfl
theorem whole_rfl_numeratorPartialNumerator : ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialNumerator = PFIndependentFormula.numeratorPartialNumerator := by rfl
namespace PFIndependentExpected
theorem expected_polynomial : ∀ (m : ℕ) (A : ℚ[X]),
    A.natDegree < 9 * (m + 1) → A = numeratorPartialNumerator m A :=
  ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_polynomial_partial_fractions
theorem expected_global : ∀ (m : ℕ) (A : ℚ[X]),
    A.natDegree < 9 * (m + 1) → ∀ (t : ℚ), (∀ k ≤ m, t + (k : ℚ) ≠ 0) →
      A.eval t / (polePolynomial m).eval t ^ 9 =
        ∑ j ∈ range (m + 1), ∑ s ∈ Icc 1 9,
          numeratorLocalCoefficient m j s A / (t + (j : ℚ)) ^ s :=
  ZetaNine.CoefficientMapNumeratorPartialFractions.checked_actual_numerator_global_partial_fractions
theorem expected_injective : ∀ (m : ℕ) (A B : ℚ[X]),
    A.natDegree < 9 * (m + 1) → B.natDegree < 9 * (m + 1) →
    (∀ j ≤ m, ∀ s, 1 ≤ s → s ≤ 9 →
      numeratorLocalCoefficient m j s A = numeratorLocalCoefficient m j s B) → A = B :=
  ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_local_coefficients_injective
end PFIndependentExpected
namespace PFIndependentBoundary
theorem zero_jet (m j s : ℕ) : numeratorLocalCoefficient m j s (0 : ℚ[X]) = 0 := by
  simp [numeratorLocalCoefficient, numeratorClearedSeries]
theorem zero_reconstruction (m : ℕ) : (0 : ℚ[X]) = numeratorPartialNumerator m 0 :=
  ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_polynomial_partial_fractions m 0 (by simp)
theorem m0_one : (1 : ℚ[X]) = numeratorPartialNumerator 0 1 :=
  ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_polynomial_partial_fractions 0 1 (by norm_num)
theorem m0_critical_X8 : (X ^ 8 : ℚ[X]) = numeratorPartialNumerator 0 (X ^ 8) :=
  ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_polynomial_partial_fractions 0 (X ^ 8) (by norm_num)
theorem m0_X9_outside_proper : ¬ (X ^ 9 : ℚ[X]).natDegree < 9 * (0 + 1) := by norm_num
theorem m0_highest_pole_one : numeratorLocalCoefficient 0 0 9 (1 : ℚ[X]) = 1 := by
  simp [numeratorLocalCoefficient, numeratorClearedSeries,
    ZetaNine.CoefficientMapJet.shiftedClearedDenominator, ZetaNine.CoefficientMapJet.shiftedVariable]
theorem m0_simple_pole_X8 : numeratorLocalCoefficient 0 0 1 (X ^ 8 : ℚ[X]) = 1 := by
  simp [numeratorLocalCoefficient, numeratorClearedSeries,
    ZetaNine.CoefficientMapJet.shiftedClearedDenominator, ZetaNine.CoefficientMapJet.shiftedVariable]
theorem m0_regular_simple_PF (t : ℚ) (ht : t ≠ 0) :
    (1 : ℚ) / t = ∑ j ∈ range (0 + 1), ∑ s ∈ Icc 1 9,
      numeratorLocalCoefficient 0 j s (X ^ 8 : ℚ[X]) / (t + (j : ℚ)) ^ s := by
  have h := ZetaNine.CoefficientMapNumeratorPartialFractions.checked_actual_numerator_global_partial_fractions 0 (X ^ 8) (by norm_num) t (by
    intro k hk
    have hk0 : k = 0 := by omega
    simpa only [hk0, Nat.cast_zero, add_zero] using ht)
  have eval_identity : (X ^ 8 : ℚ[X]).eval t / (polePolynomial 0).eval t ^ 9 = (1 : ℚ) / t := by
    have pole_identity : (polePolynomial 0).eval t = t := by simp [polePolynomial]
    rw [pole_identity]
    simp only [eval_pow, eval_X]
    field_simp [ht] <;> ring
  rw [eval_identity] at h
  exact h
theorem two_pole_one : (1 : ℚ[X]) = numeratorPartialNumerator 1 1 :=
  ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_polynomial_partial_fractions 1 1 (by norm_num)
end PFIndependentBoundary
open Lean Meta
private def requireStd3 (name : Name) : MetaM (Array Name) := do
  let axioms ← Lean.collectAxioms name
  unless axioms.toList.all (fun n => ([`propext, `Classical.choice, `Quot.sound] : List Name).contains n) do
    throwError "Nonstandard axiom in actual declaration: {name}"
  return axioms
private def requireClosed (name : Name) (ty : Expr) (value : Expr) : MetaM Unit := do
  unless !(ty.hasFVar || ty.hasMVar || value.hasFVar || value.hasMVar) do
    throwError "Actual declaration has unclosed type or value: {name}"
private def emitDefinition (name : Name) : MetaM Unit := do
  let .defnInfo info ← getConstInfo name | throwError "Expected actual definition {name}"
  requireClosed name info.type info.value
  let axioms ← requireStd3 name
  IO.println (Json.mkObj [("kind",Json.str "independent_full_definition"),
    ("declaration",Json.str name.toString),("closed",toJson true),
    ("level_parameters",toJson (info.levelParams.map Name.toString)),
    ("full_type_raw_Expr",Json.str (reprStr info.type)),
    ("full_value_raw_Expr",Json.str (reprStr info.value)),
    ("axioms",toJson (axioms.toList.map Name.toString))]).compress
private def emitProof (name : Name) (kind : String) : MetaM Unit := do
  let .thmInfo info ← getConstInfo name | throwError "Expected actual theorem {name}"
  requireClosed name info.type info.value
  let axioms ← requireStd3 name
  IO.println (Json.mkObj [("kind",Json.str kind),("declaration",Json.str name.toString),
    ("closed",toJson true),("full_type_raw_Expr",Json.str (reprStr info.type)),
    ("axioms",toJson (axioms.toList.map Name.toString))]).compress
private def compareWhole (name expected : Name) : MetaM Unit := do
  let .defnInfo actualInfo ← getConstInfo name | throwError "Expected actual definition"
  let .defnInfo expectedInfo ← getConstInfo expected | throwError "Expected independently written definition"
  let typeKernel ← isDefEq actualInfo.type expectedInfo.type
  let valueKernel ← isDefEq actualInfo.value expectedInfo.value
  let typeRaw := Expr.equal actualInfo.type expectedInfo.type
  let valueRaw := Expr.equal actualInfo.value expectedInfo.value
  unless typeKernel && valueKernel && typeRaw && valueRaw do
    throwError "Full-function Expr/kernel mismatch: {name}"
  IO.println (Json.mkObj [("kind",Json.str "independent_whole_definition_comparison"),
    ("declaration",Json.str name.toString),("expected",Json.str expected.toString),
    ("type_kernel_equal",toJson typeKernel),("value_kernel_equal",toJson valueKernel),
    ("type_Expr_equal",toJson typeRaw),("value_Expr_equal",toJson valueRaw),
    ("actual_full_type_raw_Expr",Json.str (reprStr actualInfo.type)),
    ("expected_full_type_raw_Expr",Json.str (reprStr expectedInfo.type)),
    ("actual_full_value_raw_Expr",Json.str (reprStr actualInfo.value)),
    ("expected_full_value_raw_Expr",Json.str (reprStr expectedInfo.value))]).compress
private def compareType (name expected : Name) : MetaM Unit := do
  let actualInfo ← getConstInfo name
  let expectedInfo ← getConstInfo expected
  let same ← isDefEq actualInfo.type expectedInfo.type
  unless same do throwError "Whole forall type mismatch: {name}"
  IO.println (Json.mkObj [("kind",Json.str "independent_complete_forall_kernel_comparison"),
    ("declaration",Json.str name.toString),("expected",Json.str expected.toString),
    ("whole_type_kernel_equal",toJson same),
    ("actual_full_type_raw_Expr",Json.str (reprStr actualInfo.type)),
    ("expected_full_type_raw_Expr",Json.str (reprStr expectedInfo.type))]).compress
private def compareDefinitionSnapshot (name : Name) (nativeType nativeValue : Expr) : MetaM Unit := do
  let .defnInfo actualInfo ← getConstInfo name | throwError "Expected actual definition"
  let typeKernel ← isDefEq actualInfo.type nativeType
  let valueKernel ← isDefEq actualInfo.value nativeValue
  let typeRaw := Expr.equal actualInfo.type nativeType
  let valueRaw := Expr.equal actualInfo.value nativeValue
  unless typeKernel && valueKernel && typeRaw && valueRaw do
    throwError "Fresh native/staged full definition mismatch: {name}"
  IO.println (Json.mkObj [("kind",Json.str "independent_native_staged_definition_snapshot"),
    ("declaration",Json.str name.toString),("type_kernel_equal",toJson typeKernel),
    ("value_kernel_equal",toJson valueKernel),("type_Expr_equal",toJson typeRaw),
    ("value_Expr_equal",toJson valueRaw),
    ("native_full_type_raw_Expr",Json.str (reprStr nativeType)),
    ("native_full_value_raw_Expr",Json.str (reprStr nativeValue))]).compress
private def compareProofSnapshot (name : Name) (nativeType : Expr) : MetaM Unit := do
  let actualInfo ← getConstInfo name
  let same ← isDefEq actualInfo.type nativeType
  unless same do throwError "Fresh native/staged whole proof type mismatch: {name}"
  IO.println (Json.mkObj [("kind",Json.str "independent_native_staged_proof_snapshot"),
    ("declaration",Json.str name.toString),("whole_type_kernel_equal",toJson same),
    ("native_full_type_raw_Expr",Json.str (reprStr nativeType)),
    ("actual_full_type_raw_Expr",Json.str (reprStr actualInfo.type))]).compress
private def emitInternalHelpers (modules : List Name) : MetaM Unit := do
  let env ← getEnv
  let mut found : List Name := []
  for (name, info) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let some moduleName := env.header.moduleNames[index.toNat]? | continue
    if modules.contains moduleName && (name.isInternal || (privateToUserName? name).isSome) then
      found := name :: found
      if ← isProp info.type then
        let proofValue ← match info with
          | .thmInfo actual => pure actual.value
          | .defnInfo actual => pure actual.value
          | .opaqueInfo actual => pure actual.value
          | _ => throwError "Unexpected proof helper kind: {name}"
        requireClosed name info.type proofValue
        let axioms ← requireStd3 name
        IO.println (Json.mkObj [("kind",Json.str "independent_internal_helper_proof"),
          ("declaration",Json.str name.toString),("closed",toJson true),
          ("full_type_raw_Expr",Json.str (reprStr info.type)),
          ("axioms",toJson (axioms.toList.map Name.toString))]).compress
      else if let .defnInfo _ := info then
        emitDefinition name
      else
        let axioms ← requireStd3 name
        IO.println (Json.mkObj [("kind",Json.str "independent_internal_helper_other"),
          ("declaration",Json.str name.toString),("full_type_raw_Expr",Json.str (reprStr info.type)),
          ("axioms",toJson (axioms.toList.map Name.toString))]).compress
  IO.println (Json.mkObj [("kind",Json.str "independent_actual_internal_helper_inventory"),
    ("modules",toJson (modules.map Name.toString)),("names",toJson (found.map Name.toString))]).compress

run_meta do
  emitDefinition `ZetaNine.CoefficientMap.clearedPoleProduct
  compareDefinitionSnapshot `ZetaNine.CoefficientMap.clearedPoleProduct (Lean.Expr.forallE
  `n
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `j
    (Lean.Expr.const `Nat [])
    (Lean.Expr.forallE `t (Lean.Expr.const `Rat []) (Lean.Expr.const `Rat []) (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)) (Lean.Expr.lam
  `n
  (Lean.Expr.const `Nat [])
  (Lean.Expr.lam
    `j
    (Lean.Expr.const `Nat [])
    (Lean.Expr.lam
      `t
      (Lean.Expr.const `Rat [])
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `Finset.prod [Lean.Level.zero, Lean.Level.zero])
                (Lean.Expr.const `Nat []))
              (Lean.Expr.const `Rat []))
            (Lean.Expr.const `Rat.commMonoid []))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Finset.erase [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                (Lean.Expr.const `instDecidableEqNat []))
              (Lean.Expr.app
                (Lean.Expr.const `Finset.range [])
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.const `Nat []))
                          (Lean.Expr.const `Nat []))
                        (Lean.Expr.const `Nat []))
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `instHAdd [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                        (Lean.Expr.const `instAddNat [])))
                    (Lean.Expr.bvar 2))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                      (Lean.Expr.lit (Lean.Literal.natVal 1)))
                    (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 1)))))))
            (Lean.Expr.bvar 1)))
        (Lean.Expr.lam
          `k
          (Lean.Expr.const `Nat [])
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat []))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `instHAdd [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.instAdd [])))
              (Lean.Expr.bvar 1))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.instNatCast []))
              (Lean.Expr.bvar 0)))
          (Lean.BinderInfo.default)))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  emitDefinition `ZetaNine.CoefficientMap.poleProduct
  compareDefinitionSnapshot `ZetaNine.CoefficientMap.poleProduct (Lean.Expr.forallE
  `n
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE `t (Lean.Expr.const `Rat []) (Lean.Expr.const `Rat []) (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)) (Lean.Expr.lam
  `n
  (Lean.Expr.const `Nat [])
  (Lean.Expr.lam
    `t
    (Lean.Expr.const `Rat [])
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `Finset.prod [Lean.Level.zero, Lean.Level.zero]) (Lean.Expr.const `Nat []))
            (Lean.Expr.const `Rat []))
          (Lean.Expr.const `Rat.commMonoid []))
        (Lean.Expr.app
          (Lean.Expr.const `Finset.range [])
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.const `Nat []))
                    (Lean.Expr.const `Nat []))
                  (Lean.Expr.const `Nat []))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `instHAdd [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                  (Lean.Expr.const `instAddNat [])))
              (Lean.Expr.bvar 1))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                (Lean.Expr.lit (Lean.Literal.natVal 1)))
              (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 1)))))))
      (Lean.Expr.lam
        `k
        (Lean.Expr.const `Nat [])
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat []))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `instHAdd [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.instAdd [])))
            (Lean.Expr.bvar 1))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.instNatCast []))
            (Lean.Expr.bvar 0)))
        (Lean.BinderInfo.default)))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  emitDefinition `ZetaNine.CoefficientMapFormalTransportData.numeratorClearedSeries
  compareDefinitionSnapshot `ZetaNine.CoefficientMapFormalTransportData.numeratorClearedSeries (Lean.Expr.forallE
  `m
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `j
    (Lean.Expr.const `Nat [])
    (Lean.Expr.forallE
      `A
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
        (Lean.Expr.const `Rat.semiring []))
      (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat []))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)) (Lean.Expr.lam
  `m
  (Lean.Expr.const `Nat [])
  (Lean.Expr.lam
    `j
    (Lean.Expr.const `Nat [])
    (Lean.Expr.lam
      `A
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
        (Lean.Expr.const `Rat.semiring []))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `HMul.hMul [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                  (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
              (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `instHMul [Lean.Level.zero])
                (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `MvPowerSeries.instMul [Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.const `Unit []))
                  (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.semiring []))))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Polynomial.toPowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.semiring []))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial.comp [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring []))
                (Lean.Expr.bvar 0))
              (Lean.Expr.app (Lean.Expr.const `ZetaNine.CoefficientMapJet.shiftedVariable []) (Lean.Expr.bvar 1)))))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.const `Inv.inv [Lean.Level.zero])
              (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `MvPowerSeries.instInv [Lean.Level.zero, Lean.Level.zero])
                  (Lean.Expr.const `Unit []))
                (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.instField [])))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `HPow.hPow [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                    (Lean.Expr.const `Nat []))
                  (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `instHPow [Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                    (Lean.Expr.const `Nat []))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `NPow.toPow [Lean.Level.zero])
                      (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Monoid.toNPow [Lean.Level.zero])
                        (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Semiring.toMonoid [Lean.Level.zero])
                          (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `MvPowerSeries.instSemiring [Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.const `Unit []))
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))))))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `Polynomial.toPowerSeries [Lean.Level.zero])
                    (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring []))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `ZetaNine.CoefficientMapJet.shiftedClearedDenominator [])
                    (Lean.Expr.bvar 2))
                  (Lean.Expr.bvar 1))))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                (Lean.Expr.lit (Lean.Literal.natVal 9)))
              (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9)))))))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  emitDefinition `ZetaNine.CoefficientMapFormalTransportData.numeratorLocalCoefficient
  compareDefinitionSnapshot `ZetaNine.CoefficientMapFormalTransportData.numeratorLocalCoefficient (Lean.Expr.forallE
  `m
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `j
    (Lean.Expr.const `Nat [])
    (Lean.Expr.forallE
      `s
      (Lean.Expr.const `Nat [])
      (Lean.Expr.forallE
        `A
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
          (Lean.Expr.const `Rat.semiring []))
        (Lean.Expr.const `Rat [])
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)) (Lean.Expr.lam
  `m
  (Lean.Expr.const `Nat [])
  (Lean.Expr.lam
    `j
    (Lean.Expr.const `Nat [])
    (Lean.Expr.lam
      `s
      (Lean.Expr.const `Nat [])
      (Lean.Expr.lam
        `A
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
          (Lean.Expr.const `Rat.semiring []))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const
                      `DFunLike.coe
                      [Lean.Level.succ (Lean.Level.zero),
                       Lean.Level.succ (Lean.Level.zero),
                       Lean.Level.succ (Lean.Level.zero)])
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `LinearMap
                                            [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                          (Lean.Expr.const `Rat []))
                                        (Lean.Expr.const `Rat []))
                                      (Lean.Expr.const `Rat.semiring []))
                                    (Lean.Expr.const `Rat.semiring []))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `RingHom.id [Lean.Level.zero])
                                      (Lean.Expr.const `Rat []))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                                        (Lean.Expr.const `Rat []))
                                      (Lean.Expr.const `Rat.semiring []))))
                                (Lean.Expr.app
                                  (Lean.Expr.const `PowerSeries [Lean.Level.zero])
                                  (Lean.Expr.const `Rat [])))
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `MvPowerSeries.instAddCommMonoid [Lean.Level.zero, Lean.Level.zero])
                                  (Lean.Expr.const `Unit []))
                                (Lean.Expr.const `Rat []))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.semiring []))))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.zero])
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `MvPowerSeries.instModule
                                      [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                    (Lean.Expr.const `Unit []))
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring []))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.zero])
                                (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring [])))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Semiring.toModule [Lean.Level.zero])
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring []))))
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Semiring.toModule [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring []))))
                  (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                (Lean.Expr.lam
                  (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Data.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
                  (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat [])
                  (Lean.BinderInfo.default)))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `LinearMap.instFunLike
                                      [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.app
                                  (Lean.Expr.const `PowerSeries [Lean.Level.zero])
                                  (Lean.Expr.const `Rat [])))
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring []))
                          (Lean.Expr.const `Rat.semiring []))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `MvPowerSeries.instAddCommMonoid [Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.const `Unit []))
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.zero])
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring []))))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.zero])
                          (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const
                                  `MvPowerSeries.instModule
                                  [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                (Lean.Expr.const `Unit []))
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring []))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.zero])
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Semiring.toModule [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring []))))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Semiring.toModule [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring [])))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `RingHom.id [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                      (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring [])))))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `PowerSeries.coeff [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.semiring []))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `HSub.hSub [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.const `Nat []))
                        (Lean.Expr.const `Nat []))
                      (Lean.Expr.const `Nat []))
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `instHSub [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                      (Lean.Expr.const `instSubNat [])))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                      (Lean.Expr.lit (Lean.Literal.natVal 9)))
                    (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9)))))
                (Lean.Expr.bvar 1))))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `ZetaNine.CoefficientMapFormalTransportData.numeratorClearedSeries [])
                (Lean.Expr.bvar 3))
              (Lean.Expr.bvar 2))
            (Lean.Expr.bvar 0)))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  emitDefinition `ZetaNine.CoefficientMapInjectivity.polePolynomial
  compareDefinitionSnapshot `ZetaNine.CoefficientMapInjectivity.polePolynomial (Lean.Expr.forallE
  `n
  (Lean.Expr.const `Nat [])
  (Lean.Expr.app
    (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
    (Lean.Expr.const `Rat.semiring []))
  (Lean.BinderInfo.default)) (Lean.Expr.lam
  `n
  (Lean.Expr.const `Nat [])
  (Lean.Expr.app
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `Finset.prod [Lean.Level.zero, Lean.Level.zero]) (Lean.Expr.const `Nat []))
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
            (Lean.Expr.const `Rat.semiring [])))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.const `CommRing.toCommMonoid [Lean.Level.zero])
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.semiring [])))
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `Polynomial.commRing [Lean.Level.zero]) (Lean.Expr.const `Rat []))
            (Lean.Expr.const `Rat.commRing []))))
      (Lean.Expr.app
        (Lean.Expr.const `Finset.range [])
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.const `Nat []))
                  (Lean.Expr.const `Nat []))
                (Lean.Expr.const `Nat []))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `instHAdd [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                (Lean.Expr.const `instAddNat [])))
            (Lean.Expr.bvar 0))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
              (Lean.Expr.lit (Lean.Literal.natVal 1)))
            (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 1)))))))
    (Lean.Expr.lam
      `j
      (Lean.Expr.const `Nat [])
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring [])))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring [])))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.semiring [])))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `instHAdd [Lean.Level.zero])
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring [])))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Polynomial.instAdd [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.semiring []))))
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `Polynomial.X [Lean.Level.zero]) (Lean.Expr.const `Rat []))
            (Lean.Expr.const `Rat.semiring [])))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const
                      `DFunLike.coe
                      [Lean.Level.succ (Lean.Level.zero),
                       Lean.Level.succ (Lean.Level.zero),
                       Lean.Level.succ (Lean.Level.zero)])
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `RingHom [Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))))
                  (Lean.Expr.const `Rat []))
                (Lean.Expr.lam
                  (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Data.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
                  (Lean.Expr.const `Rat [])
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring []))
                  (Lean.BinderInfo.default)))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `RingHom.instFunLike [Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.const `Rat []))
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                      (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring [])))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring [])))))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Polynomial.C [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.semiring [])))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.instNatCast []))
            (Lean.Expr.bvar 0))))
      (Lean.BinderInfo.default)))
  (Lean.BinderInfo.default))
  emitDefinition `ZetaNine.CoefficientMapJet.shiftedClearedDenominator
  compareDefinitionSnapshot `ZetaNine.CoefficientMapJet.shiftedClearedDenominator (Lean.Expr.forallE
  `n
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `j
    (Lean.Expr.const `Nat [])
    (Lean.Expr.app
      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
      (Lean.Expr.const `Rat.semiring []))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)) (Lean.Expr.lam
  `n
  (Lean.Expr.const `Nat [])
  (Lean.Expr.lam
    `j
    (Lean.Expr.const `Nat [])
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `Finset.prod [Lean.Level.zero, Lean.Level.zero]) (Lean.Expr.const `Nat []))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.semiring [])))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.const `CommRing.toCommMonoid [Lean.Level.zero])
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.semiring [])))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Polynomial.commRing [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.commRing []))))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Finset.erase [Lean.Level.zero]) (Lean.Expr.const `Nat []))
              (Lean.Expr.const `instDecidableEqNat []))
            (Lean.Expr.app
              (Lean.Expr.const `Finset.range [])
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.const `Nat []))
                        (Lean.Expr.const `Nat []))
                      (Lean.Expr.const `Nat []))
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `instHAdd [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                      (Lean.Expr.const `instAddNat [])))
                  (Lean.Expr.bvar 1))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                    (Lean.Expr.lit (Lean.Literal.natVal 1)))
                  (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 1)))))))
          (Lean.Expr.bvar 0)))
      (Lean.Expr.lam
        `k
        (Lean.Expr.const `Nat [])
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring [])))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring [])))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `instHAdd [Lean.Level.zero])
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring [])))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial.instAdd [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring []))))
            (Lean.Expr.app (Lean.Expr.const `ZetaNine.CoefficientMapJet.shiftedVariable []) (Lean.Expr.bvar 1)))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const
                        `DFunLike.coe
                        [Lean.Level.succ (Lean.Level.zero),
                         Lean.Level.succ (Lean.Level.zero),
                         Lean.Level.succ (Lean.Level.zero)])
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `RingHom [Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.app
                              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring [])))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                            (Lean.Expr.app
                              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring [])))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))))
                    (Lean.Expr.const `Rat []))
                  (Lean.Expr.lam
                    (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Data.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
                    (Lean.Expr.const `Rat [])
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring []))
                    (Lean.BinderInfo.default)))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `RingHom.instFunLike [Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.const `Rat []))
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                        (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Polynomial.C [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.semiring [])))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.instNatCast []))
              (Lean.Expr.bvar 0))))
        (Lean.BinderInfo.default)))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  emitDefinition `ZetaNine.CoefficientMapJet.shiftedVariable
  compareDefinitionSnapshot `ZetaNine.CoefficientMapJet.shiftedVariable (Lean.Expr.forallE
  `j
  (Lean.Expr.const `Nat [])
  (Lean.Expr.app
    (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
    (Lean.Expr.const `Rat.semiring []))
  (Lean.BinderInfo.default)) (Lean.Expr.lam
  `j
  (Lean.Expr.const `Nat [])
  (Lean.Expr.app
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.const `HSub.hSub [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.semiring [])))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.semiring [])))
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
            (Lean.Expr.const `Rat.semiring [])))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.const `instHSub [Lean.Level.zero])
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.semiring [])))
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `Polynomial.instSub [Lean.Level.zero]) (Lean.Expr.const `Rat []))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `DivisionRing.toRing [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.instDivisionRing [])))))
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Polynomial.X [Lean.Level.zero]) (Lean.Expr.const `Rat []))
        (Lean.Expr.const `Rat.semiring [])))
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const
                  `DFunLike.coe
                  [Lean.Level.succ (Lean.Level.zero),
                   Lean.Level.succ (Lean.Level.zero),
                   Lean.Level.succ (Lean.Level.zero)])
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `RingHom [Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.const `Rat []))
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                        (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))))
              (Lean.Expr.const `Rat []))
            (Lean.Expr.lam
              (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Data.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
              (Lean.Expr.const `Rat [])
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.semiring []))
              (Lean.BinderInfo.default)))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `RingHom.instFunLike [Lean.Level.zero, Lean.Level.zero])
                  (Lean.Expr.const `Rat []))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring [])))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                  (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.semiring [])))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring [])))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.semiring [])))))
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `Polynomial.C [Lean.Level.zero]) (Lean.Expr.const `Rat []))
          (Lean.Expr.const `Rat.semiring [])))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Rat []))
          (Lean.Expr.const `Rat.instNatCast []))
        (Lean.Expr.bvar 0))))
  (Lean.BinderInfo.default))
  emitDefinition `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalTruncation
  compareDefinitionSnapshot `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalTruncation (Lean.Expr.forallE
  `m
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `j
    (Lean.Expr.const `Nat [])
    (Lean.Expr.forallE
      `A
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
        (Lean.Expr.const `Rat.semiring []))
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
        (Lean.Expr.const `Rat.semiring []))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)) (Lean.Expr.lam
  `m
  (Lean.Expr.const `Nat [])
  (Lean.Expr.lam
    `j
    (Lean.Expr.const `Nat [])
    (Lean.Expr.lam
      `A
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
        (Lean.Expr.const `Rat.semiring []))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const
                    `DFunLike.coe
                    [Lean.Level.succ (Lean.Level.zero),
                     Lean.Level.succ (Lean.Level.zero),
                     Lean.Level.succ (Lean.Level.zero)])
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const
                                          `LinearMap
                                          [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                        (Lean.Expr.const `Rat []))
                                      (Lean.Expr.const `Rat []))
                                    (Lean.Expr.const `Rat.semiring []))
                                  (Lean.Expr.const `Rat.semiring []))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `RingHom.id [Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                                      (Lean.Expr.const `Rat []))
                                    (Lean.Expr.const `Rat.semiring []))))
                              (Lean.Expr.app
                                (Lean.Expr.const `PowerSeries [Lean.Level.zero])
                                (Lean.Expr.const `Rat [])))
                            (Lean.Expr.app
                              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring [])))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `MvPowerSeries.instAddCommMonoid [Lean.Level.zero, Lean.Level.zero])
                                (Lean.Expr.const `Unit []))
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.zero])
                                (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring []))))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.zero])
                            (Lean.Expr.app
                              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring [])))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring []))))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `MvPowerSeries.instModule
                                    [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                  (Lean.Expr.const `Unit []))
                                (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring []))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.zero])
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Semiring.toModule [Lean.Level.zero])
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring []))))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Polynomial.module [Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring []))
                          (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring []))
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Semiring.toModule [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))))
                (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
              (Lean.Expr.lam
                (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Data.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
                (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring []))
                (Lean.BinderInfo.default)))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `LinearMap.instFunLike
                                    [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat []))
                              (Lean.Expr.app
                                (Lean.Expr.const `PowerSeries [Lean.Level.zero])
                                (Lean.Expr.const `Rat [])))
                            (Lean.Expr.app
                              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring [])))
                          (Lean.Expr.const `Rat.semiring []))
                        (Lean.Expr.const `Rat.semiring []))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `MvPowerSeries.instAddCommMonoid [Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.const `Unit []))
                          (Lean.Expr.const `Rat []))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.zero])
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring []))))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                          (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring []))))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const
                                `MvPowerSeries.instModule
                                [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.const `Unit []))
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring []))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.zero])
                          (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Semiring.toModule [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring []))))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Polynomial.module [Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring []))
                      (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring []))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Semiring.toModule [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring []))))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `RingHom.id [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                    (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring [])))))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `PowerSeries.trunc [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.semiring []))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                (Lean.Expr.lit (Lean.Literal.natVal 9)))
              (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9))))))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.const `ZetaNine.CoefficientMapFormalTransportData.numeratorClearedSeries [])
              (Lean.Expr.bvar 2))
            (Lean.Expr.bvar 1))
          (Lean.Expr.bvar 0)))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  emitDefinition `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock
  compareDefinitionSnapshot `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock (Lean.Expr.forallE
  `m
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `j
    (Lean.Expr.const `Nat [])
    (Lean.Expr.forallE
      `A
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
        (Lean.Expr.const `Rat.semiring []))
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
        (Lean.Expr.const `Rat.semiring []))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)) (Lean.Expr.lam
  `m
  (Lean.Expr.const `Nat [])
  (Lean.Expr.lam
    `j
    (Lean.Expr.const `Nat [])
    (Lean.Expr.lam
      `A
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
        (Lean.Expr.const `Rat.semiring []))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `HMul.hMul [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring [])))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring [])))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.semiring [])))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `instHMul [Lean.Level.zero])
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring [])))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Polynomial.instMul [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.semiring []))))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `HPow.hPow [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.const `Nat []))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring [])))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `instHPow [Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.const `Nat []))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `NPow.toPow [Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Monoid.toNPow [Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Semiring.toMonoid [Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))))))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial [])
                  (Lean.Expr.bvar 2))
                (Lean.Expr.bvar 1)))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                (Lean.Expr.lit (Lean.Literal.natVal 9)))
              (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9))))))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Polynomial.comp [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.semiring []))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalTruncation [])
                  (Lean.Expr.bvar 2))
                (Lean.Expr.bvar 1))
              (Lean.Expr.bvar 0)))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring [])))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `instHAdd [Lean.Level.zero])
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Polynomial.instAdd [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring []))))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Polynomial.X [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.semiring [])))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const
                          `DFunLike.coe
                          [Lean.Level.succ (Lean.Level.zero),
                           Lean.Level.succ (Lean.Level.zero),
                           Lean.Level.succ (Lean.Level.zero)])
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `RingHom [Lean.Level.zero, Lean.Level.zero])
                                (Lean.Expr.const `Rat []))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.semiring [])))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                                (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring [])))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.semiring [])))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                                (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring [])))))
                      (Lean.Expr.const `Rat []))
                    (Lean.Expr.lam
                      (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Data.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
                      (Lean.Expr.const `Rat [])
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring []))
                      (Lean.BinderInfo.default)))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `RingHom.instFunLike [Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.const `Rat []))
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                          (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                          (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial.C [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring [])))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.instNatCast []))
                (Lean.Expr.bvar 1))))))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  emitDefinition `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialNumerator
  compareDefinitionSnapshot `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialNumerator (Lean.Expr.forallE
  `m
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `A
    (Lean.Expr.app
      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
      (Lean.Expr.const `Rat.semiring []))
    (Lean.Expr.app
      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
      (Lean.Expr.const `Rat.semiring []))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)) (Lean.Expr.lam
  `m
  (Lean.Expr.const `Nat [])
  (Lean.Expr.lam
    `A
    (Lean.Expr.app
      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
      (Lean.Expr.const `Rat.semiring []))
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `Finset.sum [Lean.Level.zero, Lean.Level.zero]) (Lean.Expr.const `Nat []))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.semiring [])))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.zero])
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.semiring [])))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.semiring []))))
        (Lean.Expr.app
          (Lean.Expr.const `Finset.range [])
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.const `Nat []))
                    (Lean.Expr.const `Nat []))
                  (Lean.Expr.const `Nat []))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `instHAdd [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                  (Lean.Expr.const `instAddNat [])))
              (Lean.Expr.bvar 1))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                (Lean.Expr.lit (Lean.Literal.natVal 1)))
              (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 1)))))))
      (Lean.Expr.lam
        `j
        (Lean.Expr.const `Nat [])
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Finset.sum [Lean.Level.zero, Lean.Level.zero])
                  (Lean.Expr.const `Nat []))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring [])))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.zero])
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring [])))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring []))))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Finset.Icc [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                    (Lean.Expr.const `Nat.instPreorder []))
                  (Lean.Expr.const `Nat.instLocallyFiniteOrder []))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                    (Lean.Expr.lit (Lean.Literal.natVal 1)))
                  (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 1)))))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                  (Lean.Expr.lit (Lean.Literal.natVal 9)))
                (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9))))))
          (Lean.Expr.lam
            `s
            (Lean.Expr.const `Nat [])
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `HMul.hMul [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `instHMul [Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial.instMul [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring []))))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `HMul.hMul [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.app
                              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring [])))
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `instHMul [Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Polynomial.instMul [Lean.Level.zero])
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring []))))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const
                                  `DFunLike.coe
                                  [Lean.Level.succ (Lean.Level.zero),
                                   Lean.Level.succ (Lean.Level.zero),
                                   Lean.Level.succ (Lean.Level.zero)])
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `RingHom [Lean.Level.zero, Lean.Level.zero])
                                        (Lean.Expr.const `Rat []))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                          (Lean.Expr.const `Rat []))
                                        (Lean.Expr.const `Rat.semiring [])))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                                        (Lean.Expr.const `Rat []))
                                      (Lean.Expr.const `Rat.semiring [])))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                          (Lean.Expr.const `Rat []))
                                        (Lean.Expr.const `Rat.semiring [])))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                                        (Lean.Expr.const `Rat []))
                                      (Lean.Expr.const `Rat.semiring [])))))
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.lam
                              (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Data.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
                              (Lean.Expr.const `Rat [])
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.semiring []))
                              (Lean.BinderInfo.default)))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `RingHom.instFunLike [Lean.Level.zero, Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Rat.semiring [])))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.semiring [])))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Rat.semiring [])))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.semiring [])))))
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial.C [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `ZetaNine.CoefficientMapFormalTransportData.numeratorLocalCoefficient [])
                              (Lean.Expr.bvar 3))
                            (Lean.Expr.bvar 1))
                          (Lean.Expr.bvar 0))
                        (Lean.Expr.bvar 2))))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `HPow.hPow [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.semiring [])))
                            (Lean.Expr.const `Nat []))
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `instHPow [Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.semiring [])))
                            (Lean.Expr.const `Nat []))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `NPow.toPow [Lean.Level.zero])
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.semiring [])))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Monoid.toNPow [Lean.Level.zero])
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Rat.semiring [])))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Semiring.toMonoid [Lean.Level.zero])
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                      (Lean.Expr.const `Rat []))
                                    (Lean.Expr.const `Rat.semiring [])))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Rat.semiring [])))))))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial [])
                          (Lean.Expr.bvar 3))
                        (Lean.Expr.bvar 1)))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                        (Lean.Expr.lit (Lean.Literal.natVal 9)))
                      (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9)))))))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `HPow.hPow [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.const `Nat []))
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `instHPow [Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.const `Nat []))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `NPow.toPow [Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Monoid.toNPow [Lean.Level.zero])
                            (Lean.Expr.app
                              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring [])))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Semiring.toMonoid [Lean.Level.zero])
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.semiring [])))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                                (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring [])))))))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.semiring [])))
                            (Lean.Expr.app
                              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring [])))
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `instHAdd [Lean.Level.zero])
                            (Lean.Expr.app
                              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring [])))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Polynomial.instAdd [Lean.Level.zero])
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring []))))
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial.X [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const
                                  `DFunLike.coe
                                  [Lean.Level.succ (Lean.Level.zero),
                                   Lean.Level.succ (Lean.Level.zero),
                                   Lean.Level.succ (Lean.Level.zero)])
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `RingHom [Lean.Level.zero, Lean.Level.zero])
                                        (Lean.Expr.const `Rat []))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                          (Lean.Expr.const `Rat []))
                                        (Lean.Expr.const `Rat.semiring [])))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                                        (Lean.Expr.const `Rat []))
                                      (Lean.Expr.const `Rat.semiring [])))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                          (Lean.Expr.const `Rat []))
                                        (Lean.Expr.const `Rat.semiring [])))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                                        (Lean.Expr.const `Rat []))
                                      (Lean.Expr.const `Rat.semiring [])))))
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.lam
                              (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Data.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
                              (Lean.Expr.const `Rat [])
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.semiring []))
                              (Lean.BinderInfo.default)))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `RingHom.instFunLike [Lean.Level.zero, Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Rat.semiring [])))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.semiring [])))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Rat.semiring [])))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.semiring [])))))
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial.C [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.instNatCast []))
                        (Lean.Expr.bvar 1)))))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `HSub.hSub [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.const `Nat []))
                          (Lean.Expr.const `Nat []))
                        (Lean.Expr.const `Nat []))
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `instHSub [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                        (Lean.Expr.const `instSubNat [])))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                        (Lean.Expr.lit (Lean.Literal.natVal 9)))
                      (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9)))))
                  (Lean.Expr.bvar 0))))
            (Lean.BinderInfo.default)))
        (Lean.BinderInfo.default)))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  emitDefinition `ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial
  compareDefinitionSnapshot `ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial (Lean.Expr.forallE
  `n
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `j
    (Lean.Expr.const `Nat [])
    (Lean.Expr.app
      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
      (Lean.Expr.const `Rat.semiring []))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)) (Lean.Expr.lam
  `n
  (Lean.Expr.const `Nat [])
  (Lean.Expr.lam
    `j
    (Lean.Expr.const `Nat [])
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `Finset.prod [Lean.Level.zero, Lean.Level.zero]) (Lean.Expr.const `Nat []))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.semiring [])))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.const `CommRing.toCommMonoid [Lean.Level.zero])
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.semiring [])))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Polynomial.commRing [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.commRing []))))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Finset.erase [Lean.Level.zero]) (Lean.Expr.const `Nat []))
              (Lean.Expr.const `instDecidableEqNat []))
            (Lean.Expr.app
              (Lean.Expr.const `Finset.range [])
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.const `Nat []))
                        (Lean.Expr.const `Nat []))
                      (Lean.Expr.const `Nat []))
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `instHAdd [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                      (Lean.Expr.const `instAddNat [])))
                  (Lean.Expr.bvar 1))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                    (Lean.Expr.lit (Lean.Literal.natVal 1)))
                  (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 1)))))))
          (Lean.Expr.bvar 0)))
      (Lean.Expr.lam
        `k
        (Lean.Expr.const `Nat [])
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring [])))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring [])))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `instHAdd [Lean.Level.zero])
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring [])))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial.instAdd [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring []))))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Polynomial.X [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.semiring [])))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const
                        `DFunLike.coe
                        [Lean.Level.succ (Lean.Level.zero),
                         Lean.Level.succ (Lean.Level.zero),
                         Lean.Level.succ (Lean.Level.zero)])
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `RingHom [Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.app
                              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring [])))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                            (Lean.Expr.app
                              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring [])))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))))
                    (Lean.Expr.const `Rat []))
                  (Lean.Expr.lam
                    (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Data.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
                    (Lean.Expr.const `Rat [])
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring []))
                    (Lean.BinderInfo.default)))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `RingHom.instFunLike [Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.const `Rat []))
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                        (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Polynomial.C [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.semiring [])))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.instNatCast []))
              (Lean.Expr.bvar 0))))
        (Lean.BinderInfo.default)))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  emitProof `ZetaNine.CoefficientMap.clearedPoleProduct_ne_zero "independent_staged_reached_proof"
  compareProofSnapshot `ZetaNine.CoefficientMap.clearedPoleProduct_ne_zero (Lean.Expr.forallE
  `n
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `j
    (Lean.Expr.const `Nat [])
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Ne [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Rat []))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `ZetaNine.CoefficientMap.clearedPoleProduct []) (Lean.Expr.bvar 1))
            (Lean.Expr.bvar 0))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Neg.neg [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.instNeg []))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.instNatCast []))
              (Lean.Expr.bvar 0)))))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Rat []))
          (Lean.Expr.lit (Lean.Literal.natVal 0)))
        (Lean.Expr.app (Lean.Expr.const `Rat.instOfNat []) (Lean.Expr.lit (Lean.Literal.natVal 0)))))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  emitProof `ZetaNine.CoefficientMapInjectivity.polePolynomial_natDegree "independent_staged_reached_proof"
  compareProofSnapshot `ZetaNine.CoefficientMapInjectivity.polePolynomial_natDegree (Lean.Expr.forallE
  `n
  (Lean.Expr.const `Nat [])
  (Lean.Expr.app
    (Lean.Expr.app
      (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Nat []))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `Polynomial.natDegree [Lean.Level.zero]) (Lean.Expr.const `Rat []))
          (Lean.Expr.const `Rat.semiring []))
        (Lean.Expr.app (Lean.Expr.const `ZetaNine.CoefficientMapInjectivity.polePolynomial []) (Lean.Expr.bvar 0))))
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                (Lean.Expr.const `Nat []))
              (Lean.Expr.const `Nat []))
            (Lean.Expr.const `Nat []))
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `instHAdd [Lean.Level.zero]) (Lean.Expr.const `Nat []))
            (Lean.Expr.const `instAddNat [])))
        (Lean.Expr.bvar 0))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
          (Lean.Expr.lit (Lean.Literal.natVal 1)))
        (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 1))))))
  (Lean.BinderInfo.default))
  emitProof `ZetaNine.CoefficientMapInjectivity.polePolynomial_pow_natDegree "independent_staged_reached_proof"
  compareProofSnapshot `ZetaNine.CoefficientMapInjectivity.polePolynomial_pow_natDegree (Lean.Expr.forallE
  `n
  (Lean.Expr.const `Nat [])
  (Lean.Expr.app
    (Lean.Expr.app
      (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Nat []))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `Polynomial.natDegree [Lean.Level.zero]) (Lean.Expr.const `Rat []))
          (Lean.Expr.const `Rat.semiring []))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `HPow.hPow [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.const `Nat []))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring [])))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `instHPow [Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.const `Nat []))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `NPow.toPow [Lean.Level.zero])
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Monoid.toNPow [Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Semiring.toMonoid [Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                          (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))))))
            (Lean.Expr.app (Lean.Expr.const `ZetaNine.CoefficientMapInjectivity.polePolynomial []) (Lean.Expr.bvar 0)))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
              (Lean.Expr.lit (Lean.Literal.natVal 9)))
            (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9)))))))
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `HMul.hMul [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                (Lean.Expr.const `Nat []))
              (Lean.Expr.const `Nat []))
            (Lean.Expr.const `Nat []))
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `instHMul [Lean.Level.zero]) (Lean.Expr.const `Nat []))
            (Lean.Expr.const `instMulNat [])))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
            (Lean.Expr.lit (Lean.Literal.natVal 9)))
          (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9)))))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                  (Lean.Expr.const `Nat []))
                (Lean.Expr.const `Nat []))
              (Lean.Expr.const `Nat []))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `instHAdd [Lean.Level.zero]) (Lean.Expr.const `Nat []))
              (Lean.Expr.const `instAddNat [])))
          (Lean.Expr.bvar 0))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
            (Lean.Expr.lit (Lean.Literal.natVal 1)))
          (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 1)))))))
  (Lean.BinderInfo.default))
  emitProof `ZetaNine.CoefficientMapInjectivity.pole_factors_coprime "independent_staged_reached_proof"
  compareProofSnapshot `ZetaNine.CoefficientMapInjectivity.pole_factors_coprime (Lean.Expr.forallE
  `a
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `b
    (Lean.Expr.const `Nat [])
    (Lean.Expr.forallE
      `hab
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `Ne [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Nat []))
          (Lean.Expr.bvar 1))
        (Lean.Expr.bvar 0))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.const `IsCoprime [Lean.Level.zero])
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.semiring [])))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Polynomial.commSemiring [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.commSemiring [])))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `HPow.hPow [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.const `Nat []))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring [])))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `instHPow [Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.const `Nat []))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `NPow.toPow [Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Monoid.toNPow [Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Semiring.toMonoid [Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))))))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `instHAdd [Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Polynomial.instAdd [Lean.Level.zero])
                          (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring []))))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Polynomial.X [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring [])))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const
                              `DFunLike.coe
                              [Lean.Level.succ (Lean.Level.zero),
                               Lean.Level.succ (Lean.Level.zero),
                               Lean.Level.succ (Lean.Level.zero)])
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `RingHom [Lean.Level.zero, Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                      (Lean.Expr.const `Rat []))
                                    (Lean.Expr.const `Rat.semiring [])))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Rat.semiring [])))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                      (Lean.Expr.const `Rat []))
                                    (Lean.Expr.const `Rat.semiring [])))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Rat.semiring [])))))
                          (Lean.Expr.const `Rat []))
                        (Lean.Expr.lam
                          (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Data.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
                          (Lean.Expr.const `Rat [])
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring []))
                          (Lean.BinderInfo.default)))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `RingHom.instFunLike [Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.app
                              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring [])))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                            (Lean.Expr.app
                              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring [])))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))))
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial.C [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.instNatCast []))
                    (Lean.Expr.bvar 2)))))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                (Lean.Expr.lit (Lean.Literal.natVal 9)))
              (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9))))))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `HPow.hPow [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.const `Nat []))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring [])))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `instHPow [Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.const `Nat []))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `NPow.toPow [Lean.Level.zero])
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Monoid.toNPow [Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Semiring.toMonoid [Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                          (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))))))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `instHAdd [Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial.instAdd [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring []))))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial.X [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring [])))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const
                            `DFunLike.coe
                            [Lean.Level.succ (Lean.Level.zero),
                             Lean.Level.succ (Lean.Level.zero),
                             Lean.Level.succ (Lean.Level.zero)])
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `RingHom [Lean.Level.zero, Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Rat.semiring [])))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.semiring [])))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Rat.semiring [])))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.semiring [])))))
                        (Lean.Expr.const `Rat []))
                      (Lean.Expr.lam
                        (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Data.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
                        (Lean.Expr.const `Rat [])
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring []))
                        (Lean.BinderInfo.default)))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `RingHom.instFunLike [Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Polynomial.C [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring [])))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.instNatCast []))
                  (Lean.Expr.bvar 1)))))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
              (Lean.Expr.lit (Lean.Literal.natVal 9)))
            (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9))))))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  emitProof `ZetaNine.CoefficientMapJet.shiftedClearedDenominator_constant "independent_staged_reached_proof"
  compareProofSnapshot `ZetaNine.CoefficientMapJet.shiftedClearedDenominator_constant (Lean.Expr.forallE
  `n
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `j
    (Lean.Expr.const `Nat [])
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Rat []))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const
                      `DFunLike.coe
                      [Lean.Level.succ (Lean.Level.zero),
                       Lean.Level.succ (Lean.Level.zero),
                       Lean.Level.succ (Lean.Level.zero)])
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `RingHom [Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                          (Lean.Expr.const `Rat []))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                            (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `MvPowerSeries.instSemiring [Lean.Level.zero, Lean.Level.zero])
                                (Lean.Expr.const `Unit []))
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring []))))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                          (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring []))))
                  (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                (Lean.Expr.lam
                  (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Data.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
                  (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat [])
                  (Lean.BinderInfo.default)))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `RingHom.instFunLike [Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                    (Lean.Expr.const `Rat []))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                      (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `MvPowerSeries.instSemiring [Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.const `Unit []))
                        (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring []))))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                    (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring []))))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `PowerSeries.constantCoeff [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.semiring [])))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Polynomial.toPowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.semiring []))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `ZetaNine.CoefficientMapJet.shiftedClearedDenominator [])
                (Lean.Expr.bvar 1))
              (Lean.Expr.bvar 0)))))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `ZetaNine.CoefficientMap.clearedPoleProduct []) (Lean.Expr.bvar 1))
          (Lean.Expr.bvar 0))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `Neg.neg [Lean.Level.zero]) (Lean.Expr.const `Rat []))
            (Lean.Expr.const `Rat.instNeg []))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.instNatCast []))
            (Lean.Expr.bvar 0)))))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  emitProof `ZetaNine.CoefficientMapJet.shiftedClearedDenominator_constant_ne_zero "independent_staged_reached_proof"
  compareProofSnapshot `ZetaNine.CoefficientMapJet.shiftedClearedDenominator_constant_ne_zero (Lean.Expr.forallE
  `n
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `j
    (Lean.Expr.const `Nat [])
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Ne [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Rat []))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const
                      `DFunLike.coe
                      [Lean.Level.succ (Lean.Level.zero),
                       Lean.Level.succ (Lean.Level.zero),
                       Lean.Level.succ (Lean.Level.zero)])
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `RingHom [Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                          (Lean.Expr.const `Rat []))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                            (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `MvPowerSeries.instSemiring [Lean.Level.zero, Lean.Level.zero])
                                (Lean.Expr.const `Unit []))
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring []))))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                          (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring []))))
                  (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                (Lean.Expr.lam
                  (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Data.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
                  (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat [])
                  (Lean.BinderInfo.default)))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `RingHom.instFunLike [Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                    (Lean.Expr.const `Rat []))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                      (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `MvPowerSeries.instSemiring [Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.const `Unit []))
                        (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring []))))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                    (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring []))))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `PowerSeries.constantCoeff [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.semiring [])))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Polynomial.toPowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.semiring []))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `ZetaNine.CoefficientMapJet.shiftedClearedDenominator [])
                (Lean.Expr.bvar 1))
              (Lean.Expr.bvar 0)))))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Rat []))
          (Lean.Expr.lit (Lean.Literal.natVal 0)))
        (Lean.Expr.app (Lean.Expr.const `Rat.instOfNat []) (Lean.Expr.lit (Lean.Literal.natVal 0)))))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  emitProof `ZetaNine.CoefficientMapJet.shiftedClearedDenominator_eval "independent_staged_reached_proof"
  compareProofSnapshot `ZetaNine.CoefficientMapJet.shiftedClearedDenominator_eval (Lean.Expr.forallE
  `n
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `j
    (Lean.Expr.const `Nat [])
    (Lean.Expr.forallE
      `z
      (Lean.Expr.const `Rat [])
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Rat []))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Polynomial.eval [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.semiring []))
              (Lean.Expr.bvar 0))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `ZetaNine.CoefficientMapJet.shiftedClearedDenominator [])
                (Lean.Expr.bvar 2))
              (Lean.Expr.bvar 1))))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `ZetaNine.CoefficientMap.clearedPoleProduct []) (Lean.Expr.bvar 2))
            (Lean.Expr.bvar 1))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat []))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `instHAdd [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.instAdd [])))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Neg.neg [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.instNeg []))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.instNatCast []))
                  (Lean.Expr.bvar 1))))
            (Lean.Expr.bvar 0))))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  emitProof `ZetaNine.CoefficientMapJet.shiftedVariable_eval "independent_staged_reached_proof"
  compareProofSnapshot `ZetaNine.CoefficientMapJet.shiftedVariable_eval (Lean.Expr.forallE
  `j
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `z
    (Lean.Expr.const `Rat [])
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Rat []))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Polynomial.eval [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.semiring []))
            (Lean.Expr.bvar 0))
          (Lean.Expr.app (Lean.Expr.const `ZetaNine.CoefficientMapJet.shiftedVariable []) (Lean.Expr.bvar 1))))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                  (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat []))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `instHAdd [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.instAdd [])))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Neg.neg [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.instNeg []))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.instNatCast []))
              (Lean.Expr.bvar 1))))
        (Lean.Expr.bvar 0)))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  emitProof `ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_all_local_coefficients_zero_implies_zero "independent_staged_reached_proof"
  compareProofSnapshot `ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_all_local_coefficients_zero_implies_zero (Lean.Expr.forallE
  `m
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `A
    (Lean.Expr.app
      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
      (Lean.Expr.const `Rat.semiring []))
    (Lean.Expr.forallE
      `hproper
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Nat []))
            (Lean.Expr.const `instLTNat []))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Polynomial.natDegree [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.semiring []))
            (Lean.Expr.bvar 0)))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `HMul.hMul [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.const `Nat []))
                  (Lean.Expr.const `Nat []))
                (Lean.Expr.const `Nat []))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `instHMul [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                (Lean.Expr.const `instMulNat [])))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                (Lean.Expr.lit (Lean.Literal.natVal 9)))
              (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9)))))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.const `Nat []))
                    (Lean.Expr.const `Nat []))
                  (Lean.Expr.const `Nat []))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `instHAdd [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                  (Lean.Expr.const `instAddNat [])))
              (Lean.Expr.bvar 1))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                (Lean.Expr.lit (Lean.Literal.natVal 1)))
              (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 1)))))))
      (Lean.Expr.forallE
        `hzero
        (Lean.Expr.forallE
          `j
          (Lean.Expr.const `Nat [])
          (Lean.Expr.forallE
            (Lean.Name.mkNum `a._@._internal._hyg 0)
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                  (Lean.Expr.const `instLENat []))
                (Lean.Expr.bvar 0))
              (Lean.Expr.bvar 3))
            (Lean.Expr.forallE
              `s
              (Lean.Expr.const `Nat [])
              (Lean.Expr.forallE
                (Lean.Name.mkNum `a._@._internal._hyg 0)
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                      (Lean.Expr.const `instLENat []))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                        (Lean.Expr.lit (Lean.Literal.natVal 1)))
                      (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 1)))))
                  (Lean.Expr.bvar 0))
                (Lean.Expr.forallE
                  (Lean.Name.mkNum `a._@._internal._hyg 0)
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                        (Lean.Expr.const `instLENat []))
                      (Lean.Expr.bvar 1))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                        (Lean.Expr.lit (Lean.Literal.natVal 9)))
                      (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9)))))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                        (Lean.Expr.const `Rat []))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `ZetaNine.CoefficientMapFormalTransportData.numeratorLocalCoefficient [])
                              (Lean.Expr.bvar 7))
                            (Lean.Expr.bvar 4))
                          (Lean.Expr.bvar 2))
                        (Lean.Expr.bvar 6)))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.lit (Lean.Literal.natVal 0)))
                      (Lean.Expr.app (Lean.Expr.const `Rat.instOfNat []) (Lean.Expr.lit (Lean.Literal.natVal 0)))))
                  (Lean.BinderInfo.default))
                (Lean.BinderInfo.default))
              (Lean.BinderInfo.default))
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.default))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.semiring [])))
            (Lean.Expr.bvar 2))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero])
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring [])))
              (Lean.Expr.lit (Lean.Literal.natVal 0)))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `Zero.toOfNat0 [Lean.Level.zero])
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring [])))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Polynomial.instZero [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.semiring [])))))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  emitProof `ZetaNine.CoefficientMapNumeratorPartialFractions.checked_actual_numerator_global_partial_fractions "independent_staged_reached_proof"
  compareProofSnapshot `ZetaNine.CoefficientMapNumeratorPartialFractions.checked_actual_numerator_global_partial_fractions (Lean.Expr.forallE
  `m
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `A
    (Lean.Expr.app
      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
      (Lean.Expr.const `Rat.semiring []))
    (Lean.Expr.forallE
      `hproper
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Nat []))
            (Lean.Expr.const `instLTNat []))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Polynomial.natDegree [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.semiring []))
            (Lean.Expr.bvar 0)))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `HMul.hMul [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.const `Nat []))
                  (Lean.Expr.const `Nat []))
                (Lean.Expr.const `Nat []))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `instHMul [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                (Lean.Expr.const `instMulNat [])))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                (Lean.Expr.lit (Lean.Literal.natVal 9)))
              (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9)))))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.const `Nat []))
                    (Lean.Expr.const `Nat []))
                  (Lean.Expr.const `Nat []))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `instHAdd [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                  (Lean.Expr.const `instAddNat [])))
              (Lean.Expr.bvar 1))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                (Lean.Expr.lit (Lean.Literal.natVal 1)))
              (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 1)))))))
      (Lean.Expr.forallE
        `t
        (Lean.Expr.const `Rat [])
        (Lean.Expr.forallE
          `hregular
          (Lean.Expr.forallE
            `k
            (Lean.Expr.const `Nat [])
            (Lean.Expr.forallE
              (Lean.Name.mkNum `a._@._internal._hyg 0)
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                    (Lean.Expr.const `instLENat []))
                  (Lean.Expr.bvar 0))
                (Lean.Expr.bvar 4))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Ne [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat []))
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `instHAdd [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.instAdd [])))
                      (Lean.Expr.bvar 2))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.instNatCast []))
                      (Lean.Expr.bvar 1))))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.lit (Lean.Literal.natVal 0)))
                  (Lean.Expr.app (Lean.Expr.const `Rat.instOfNat []) (Lean.Expr.lit (Lean.Literal.natVal 0)))))
              (Lean.BinderInfo.default))
            (Lean.BinderInfo.default))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Rat []))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `HDiv.hDiv [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat []))
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `instHDiv [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.instDiv [])))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial.eval [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring []))
                      (Lean.Expr.bvar 1))
                    (Lean.Expr.bvar 3)))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `HPow.hPow [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Nat []))
                        (Lean.Expr.const `Rat []))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `instHPow [Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Nat []))
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `NPow.toPow [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Monoid.toNPow [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.monoid [])))))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial.eval [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring []))
                        (Lean.Expr.bvar 1))
                      (Lean.Expr.app
                        (Lean.Expr.const `ZetaNine.CoefficientMapInjectivity.polePolynomial [])
                        (Lean.Expr.bvar 4))))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                      (Lean.Expr.lit (Lean.Literal.natVal 9)))
                    (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9)))))))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Finset.sum [Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.const `Nat []))
                    (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.addCommMonoid []))
                (Lean.Expr.app
                  (Lean.Expr.const `Finset.range [])
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.const `Nat []))
                            (Lean.Expr.const `Nat []))
                          (Lean.Expr.const `Nat []))
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `instHAdd [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                          (Lean.Expr.const `instAddNat [])))
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                        (Lean.Expr.lit (Lean.Literal.natVal 1)))
                      (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 1)))))))
              (Lean.Expr.lam
                `j
                (Lean.Expr.const `Nat [])
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Finset.sum [Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.const `Nat []))
                        (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.addCommMonoid []))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Finset.Icc [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                            (Lean.Expr.const `Nat.instPreorder []))
                          (Lean.Expr.const `Nat.instLocallyFiniteOrder []))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                            (Lean.Expr.lit (Lean.Literal.natVal 1)))
                          (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 1)))))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                          (Lean.Expr.lit (Lean.Literal.natVal 9)))
                        (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9))))))
                  (Lean.Expr.lam
                    `s
                    (Lean.Expr.const `Nat [])
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `HDiv.hDiv [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `instHDiv [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.instDiv [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const
                                  `ZetaNine.CoefficientMapFormalTransportData.numeratorLocalCoefficient
                                  [])
                                (Lean.Expr.bvar 6))
                              (Lean.Expr.bvar 1))
                            (Lean.Expr.bvar 0))
                          (Lean.Expr.bvar 5)))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `HPow.hPow [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Nat []))
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `instHPow [Lean.Level.zero, Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Nat []))
                              (Lean.Expr.const `Rat.instPowNat [])))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                      (Lean.Expr.const `Rat []))
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `instHAdd [Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Rat.instAdd [])))
                              (Lean.Expr.bvar 3))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.instNatCast []))
                              (Lean.Expr.bvar 1))))
                        (Lean.Expr.bvar 0)))
                    (Lean.BinderInfo.default)))
                (Lean.BinderInfo.default))))
          (Lean.BinderInfo.default))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  emitProof `ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_local_coefficients_injective "independent_staged_reached_proof"
  compareProofSnapshot `ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_local_coefficients_injective (Lean.Expr.forallE
  `m
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `A
    (Lean.Expr.app
      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
      (Lean.Expr.const `Rat.semiring []))
    (Lean.Expr.forallE
      `B
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
        (Lean.Expr.const `Rat.semiring []))
      (Lean.Expr.forallE
        `hA
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Nat []))
              (Lean.Expr.const `instLTNat []))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Polynomial.natDegree [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.semiring []))
              (Lean.Expr.bvar 1)))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `HMul.hMul [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.const `Nat []))
                    (Lean.Expr.const `Nat []))
                  (Lean.Expr.const `Nat []))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `instHMul [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                  (Lean.Expr.const `instMulNat [])))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                  (Lean.Expr.lit (Lean.Literal.natVal 9)))
                (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9)))))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.const `Nat []))
                      (Lean.Expr.const `Nat []))
                    (Lean.Expr.const `Nat []))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `instHAdd [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                    (Lean.Expr.const `instAddNat [])))
                (Lean.Expr.bvar 2))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                  (Lean.Expr.lit (Lean.Literal.natVal 1)))
                (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 1)))))))
        (Lean.Expr.forallE
          `hB
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                (Lean.Expr.const `instLTNat []))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial.natDegree [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring []))
                (Lean.Expr.bvar 1)))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `HMul.hMul [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.const `Nat []))
                      (Lean.Expr.const `Nat []))
                    (Lean.Expr.const `Nat []))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `instHMul [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                    (Lean.Expr.const `instMulNat [])))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                    (Lean.Expr.lit (Lean.Literal.natVal 9)))
                  (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9)))))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.const `Nat []))
                        (Lean.Expr.const `Nat []))
                      (Lean.Expr.const `Nat []))
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `instHAdd [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                      (Lean.Expr.const `instAddNat [])))
                  (Lean.Expr.bvar 3))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                    (Lean.Expr.lit (Lean.Literal.natVal 1)))
                  (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 1)))))))
          (Lean.Expr.forallE
            `heq
            (Lean.Expr.forallE
              `j
              (Lean.Expr.const `Nat [])
              (Lean.Expr.forallE
                (Lean.Name.mkNum `a._@._internal._hyg 0)
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                      (Lean.Expr.const `instLENat []))
                    (Lean.Expr.bvar 0))
                  (Lean.Expr.bvar 5))
                (Lean.Expr.forallE
                  `s
                  (Lean.Expr.const `Nat [])
                  (Lean.Expr.forallE
                    (Lean.Name.mkNum `a._@._internal._hyg 0)
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                          (Lean.Expr.const `instLENat []))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                            (Lean.Expr.lit (Lean.Literal.natVal 1)))
                          (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 1)))))
                      (Lean.Expr.bvar 0))
                    (Lean.Expr.forallE
                      (Lean.Name.mkNum `a._@._internal._hyg 0)
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                            (Lean.Expr.const `instLENat []))
                          (Lean.Expr.bvar 1))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                            (Lean.Expr.lit (Lean.Literal.natVal 9)))
                          (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9)))))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `ZetaNine.CoefficientMapFormalTransportData.numeratorLocalCoefficient
                                    [])
                                  (Lean.Expr.bvar 9))
                                (Lean.Expr.bvar 4))
                              (Lean.Expr.bvar 2))
                            (Lean.Expr.bvar 8)))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const
                                  `ZetaNine.CoefficientMapFormalTransportData.numeratorLocalCoefficient
                                  [])
                                (Lean.Expr.bvar 9))
                              (Lean.Expr.bvar 4))
                            (Lean.Expr.bvar 2))
                          (Lean.Expr.bvar 7)))
                      (Lean.BinderInfo.default))
                    (Lean.BinderInfo.default))
                  (Lean.BinderInfo.default))
                (Lean.BinderInfo.default))
              (Lean.BinderInfo.default))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring [])))
                (Lean.Expr.bvar 4))
              (Lean.Expr.bvar 3))
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.default))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  emitProof `ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_polynomial_partial_fractions "independent_staged_reached_proof"
  compareProofSnapshot `ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_polynomial_partial_fractions (Lean.Expr.forallE
  `m
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `A
    (Lean.Expr.app
      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
      (Lean.Expr.const `Rat.semiring []))
    (Lean.Expr.forallE
      `hproper
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Nat []))
            (Lean.Expr.const `instLTNat []))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Polynomial.natDegree [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.semiring []))
            (Lean.Expr.bvar 0)))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `HMul.hMul [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.const `Nat []))
                  (Lean.Expr.const `Nat []))
                (Lean.Expr.const `Nat []))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `instHMul [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                (Lean.Expr.const `instMulNat [])))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                (Lean.Expr.lit (Lean.Literal.natVal 9)))
              (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9)))))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.const `Nat []))
                    (Lean.Expr.const `Nat []))
                  (Lean.Expr.const `Nat []))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `instHAdd [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                  (Lean.Expr.const `instAddNat [])))
              (Lean.Expr.bvar 1))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                (Lean.Expr.lit (Lean.Literal.natVal 1)))
              (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 1)))))))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.semiring [])))
          (Lean.Expr.bvar 1))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.const `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialNumerator [])
            (Lean.Expr.bvar 2))
          (Lean.Expr.bvar 1)))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  emitProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorClearedSeries_denominator_identity "independent_staged_reached_proof"
  compareProofSnapshot `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorClearedSeries_denominator_identity (Lean.Expr.forallE
  `m
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `j
    (Lean.Expr.const `Nat [])
    (Lean.Expr.forallE
      `A
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
        (Lean.Expr.const `Rat.semiring []))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
            (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `HMul.hMul [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                    (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                  (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `instHMul [Lean.Level.zero])
                    (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `MvPowerSeries.instMul [Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.const `Unit []))
                      (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring []))))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `ZetaNine.CoefficientMapFormalTransportData.numeratorClearedSeries [])
                    (Lean.Expr.bvar 2))
                  (Lean.Expr.bvar 1))
                (Lean.Expr.bvar 0)))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `HPow.hPow [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                      (Lean.Expr.const `Nat []))
                    (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `instHPow [Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                      (Lean.Expr.const `Nat []))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `NPow.toPow [Lean.Level.zero])
                        (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Monoid.toNPow [Lean.Level.zero])
                          (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Semiring.toMonoid [Lean.Level.zero])
                            (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `MvPowerSeries.instSemiring [Lean.Level.zero, Lean.Level.zero])
                                (Lean.Expr.const `Unit []))
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))))))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Polynomial.toPowerSeries [Lean.Level.zero])
                      (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring []))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `ZetaNine.CoefficientMapJet.shiftedClearedDenominator [])
                      (Lean.Expr.bvar 2))
                    (Lean.Expr.bvar 1))))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                  (Lean.Expr.lit (Lean.Literal.natVal 9)))
                (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9)))))))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `Polynomial.toPowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat []))
            (Lean.Expr.const `Rat.semiring []))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Polynomial.comp [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.semiring []))
              (Lean.Expr.bvar 0))
            (Lean.Expr.app (Lean.Expr.const `ZetaNine.CoefficientMapJet.shiftedVariable []) (Lean.Expr.bvar 1)))))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  emitProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalCoefficient_sub "independent_staged_reached_proof"
  compareProofSnapshot `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalCoefficient_sub (Lean.Expr.forallE
  `m
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `j
    (Lean.Expr.const `Nat [])
    (Lean.Expr.forallE
      `s
      (Lean.Expr.const `Nat [])
      (Lean.Expr.forallE
        `A
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
          (Lean.Expr.const `Rat.semiring []))
        (Lean.Expr.forallE
          `B
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
            (Lean.Expr.const `Rat.semiring []))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Rat []))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `ZetaNine.CoefficientMapFormalTransportData.numeratorLocalCoefficient [])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.bvar 3))
                  (Lean.Expr.bvar 2))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `HSub.hSub [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.app
                              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring [])))
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `instHSub [Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Polynomial.instSub [Lean.Level.zero])
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `DivisionRing.toRing [Lean.Level.zero])
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.instDivisionRing [])))))
                    (Lean.Expr.bvar 1))
                  (Lean.Expr.bvar 0))))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `HSub.hSub [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat []))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `instHSub [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.instSub [])))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `ZetaNine.CoefficientMapFormalTransportData.numeratorLocalCoefficient [])
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.bvar 2))
                  (Lean.Expr.bvar 1)))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `ZetaNine.CoefficientMapFormalTransportData.numeratorLocalCoefficient [])
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.bvar 3))
                  (Lean.Expr.bvar 2))
                (Lean.Expr.bvar 0))))
          (Lean.BinderInfo.default))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  emitProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalTruncation_comp_eq_sum "independent_staged_reached_proof"
  compareProofSnapshot `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalTruncation_comp_eq_sum (Lean.Expr.forallE
  `m
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `j
    (Lean.Expr.const `Nat [])
    (Lean.Expr.forallE
      `A
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
        (Lean.Expr.const `Rat.semiring []))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.semiring [])))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Polynomial.comp [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.semiring []))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalTruncation [])
                    (Lean.Expr.bvar 2))
                  (Lean.Expr.bvar 1))
                (Lean.Expr.bvar 0)))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `instHAdd [Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial.instAdd [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring []))))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial.X [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring [])))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const
                            `DFunLike.coe
                            [Lean.Level.succ (Lean.Level.zero),
                             Lean.Level.succ (Lean.Level.zero),
                             Lean.Level.succ (Lean.Level.zero)])
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `RingHom [Lean.Level.zero, Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Rat.semiring [])))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.semiring [])))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Rat.semiring [])))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.semiring [])))))
                        (Lean.Expr.const `Rat []))
                      (Lean.Expr.lam
                        (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Data.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
                        (Lean.Expr.const `Rat [])
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring []))
                        (Lean.BinderInfo.default)))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `RingHom.instFunLike [Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Polynomial.C [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring [])))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.instNatCast []))
                  (Lean.Expr.bvar 1))))))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Finset.sum [Lean.Level.zero, Lean.Level.zero])
                  (Lean.Expr.const `Nat []))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring [])))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.zero])
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring [])))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring []))))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Finset.Icc [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                    (Lean.Expr.const `Nat.instPreorder []))
                  (Lean.Expr.const `Nat.instLocallyFiniteOrder []))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                    (Lean.Expr.lit (Lean.Literal.natVal 1)))
                  (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 1)))))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                  (Lean.Expr.lit (Lean.Literal.natVal 9)))
                (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9))))))
          (Lean.Expr.lam
            `s
            (Lean.Expr.const `Nat [])
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `HMul.hMul [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `instHMul [Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial.instMul [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring []))))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const
                              `DFunLike.coe
                              [Lean.Level.succ (Lean.Level.zero),
                               Lean.Level.succ (Lean.Level.zero),
                               Lean.Level.succ (Lean.Level.zero)])
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `RingHom [Lean.Level.zero, Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                      (Lean.Expr.const `Rat []))
                                    (Lean.Expr.const `Rat.semiring [])))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Rat.semiring [])))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                      (Lean.Expr.const `Rat []))
                                    (Lean.Expr.const `Rat.semiring [])))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Rat.semiring [])))))
                          (Lean.Expr.const `Rat []))
                        (Lean.Expr.lam
                          (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Data.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
                          (Lean.Expr.const `Rat [])
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring []))
                          (Lean.BinderInfo.default)))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `RingHom.instFunLike [Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.app
                              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring [])))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                            (Lean.Expr.app
                              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring [])))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))))
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial.C [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `ZetaNine.CoefficientMapFormalTransportData.numeratorLocalCoefficient [])
                          (Lean.Expr.bvar 3))
                        (Lean.Expr.bvar 2))
                      (Lean.Expr.bvar 0))
                    (Lean.Expr.bvar 1))))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `HPow.hPow [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.const `Nat []))
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `instHPow [Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.const `Nat []))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `NPow.toPow [Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Monoid.toNPow [Lean.Level.zero])
                            (Lean.Expr.app
                              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring [])))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Semiring.toMonoid [Lean.Level.zero])
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.semiring [])))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                                (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring [])))))))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.semiring [])))
                            (Lean.Expr.app
                              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring [])))
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `instHAdd [Lean.Level.zero])
                            (Lean.Expr.app
                              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring [])))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Polynomial.instAdd [Lean.Level.zero])
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring []))))
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial.X [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const
                                  `DFunLike.coe
                                  [Lean.Level.succ (Lean.Level.zero),
                                   Lean.Level.succ (Lean.Level.zero),
                                   Lean.Level.succ (Lean.Level.zero)])
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `RingHom [Lean.Level.zero, Lean.Level.zero])
                                        (Lean.Expr.const `Rat []))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                          (Lean.Expr.const `Rat []))
                                        (Lean.Expr.const `Rat.semiring [])))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                                        (Lean.Expr.const `Rat []))
                                      (Lean.Expr.const `Rat.semiring [])))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                          (Lean.Expr.const `Rat []))
                                        (Lean.Expr.const `Rat.semiring [])))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                                        (Lean.Expr.const `Rat []))
                                      (Lean.Expr.const `Rat.semiring [])))))
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.lam
                              (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Data.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
                              (Lean.Expr.const `Rat [])
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.semiring []))
                              (Lean.BinderInfo.default)))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `RingHom.instFunLike [Lean.Level.zero, Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Rat.semiring [])))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.semiring [])))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Rat.semiring [])))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.semiring [])))))
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial.C [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.instNatCast []))
                        (Lean.Expr.bvar 2)))))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `HSub.hSub [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.const `Nat []))
                          (Lean.Expr.const `Nat []))
                        (Lean.Expr.const `Nat []))
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `instHSub [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                        (Lean.Expr.const `instSubNat [])))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                        (Lean.Expr.lit (Lean.Literal.natVal 9)))
                      (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9)))))
                  (Lean.Expr.bvar 0))))
            (Lean.BinderInfo.default))))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  emitProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalTruncation_natDegree_le "independent_staged_reached_proof"
  compareProofSnapshot `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalTruncation_natDegree_le (Lean.Expr.forallE
  `m
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `j
    (Lean.Expr.const `Nat [])
    (Lean.Expr.forallE
      `A
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
        (Lean.Expr.const `Rat.semiring []))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Nat []))
            (Lean.Expr.const `instLENat []))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Polynomial.natDegree [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.semiring []))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalTruncation [])
                  (Lean.Expr.bvar 2))
                (Lean.Expr.bvar 1))
              (Lean.Expr.bvar 0))))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
            (Lean.Expr.lit (Lean.Literal.natVal 8)))
          (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 8)))))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  emitProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock_comp_own_shift "independent_staged_reached_proof"
  compareProofSnapshot `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock_comp_own_shift (Lean.Expr.forallE
  `m
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `j
    (Lean.Expr.const `Nat [])
    (Lean.Expr.forallE
      `A
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
        (Lean.Expr.const `Rat.semiring []))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.semiring [])))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Polynomial.comp [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.semiring []))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock [])
                    (Lean.Expr.bvar 2))
                  (Lean.Expr.bvar 1))
                (Lean.Expr.bvar 0)))
            (Lean.Expr.app (Lean.Expr.const `ZetaNine.CoefficientMapJet.shiftedVariable []) (Lean.Expr.bvar 1))))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `HMul.hMul [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring [])))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring [])))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `instHMul [Lean.Level.zero])
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring [])))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial.instMul [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring []))))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `HPow.hPow [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.const `Nat []))
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `instHPow [Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.const `Nat []))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `NPow.toPow [Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Monoid.toNPow [Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Semiring.toMonoid [Lean.Level.zero])
                            (Lean.Expr.app
                              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring [])))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))))))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `ZetaNine.CoefficientMapJet.shiftedClearedDenominator [])
                    (Lean.Expr.bvar 2))
                  (Lean.Expr.bvar 1)))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                  (Lean.Expr.lit (Lean.Literal.natVal 9)))
                (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9))))))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalTruncation [])
                (Lean.Expr.bvar 2))
              (Lean.Expr.bvar 1))
            (Lean.Expr.bvar 0))))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  emitProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock_natDegree_le "independent_staged_reached_proof"
  compareProofSnapshot `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock_natDegree_le (Lean.Expr.forallE
  `m
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `j
    (Lean.Expr.const `Nat [])
    (Lean.Expr.forallE
      `A
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
        (Lean.Expr.const `Rat.semiring []))
      (Lean.Expr.forallE
        `hj
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Nat []))
              (Lean.Expr.const `instLENat []))
            (Lean.Expr.bvar 1))
          (Lean.Expr.bvar 2))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Nat []))
              (Lean.Expr.const `instLENat []))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Polynomial.natDegree [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.semiring []))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock [])
                    (Lean.Expr.bvar 3))
                  (Lean.Expr.bvar 2))
                (Lean.Expr.bvar 1))))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.const `Nat []))
                    (Lean.Expr.const `Nat []))
                  (Lean.Expr.const `Nat []))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `instHAdd [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                  (Lean.Expr.const `instAddNat [])))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `HMul.hMul [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.const `Nat []))
                        (Lean.Expr.const `Nat []))
                      (Lean.Expr.const `Nat []))
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `instHMul [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                      (Lean.Expr.const `instMulNat [])))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                      (Lean.Expr.lit (Lean.Literal.natVal 9)))
                    (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9)))))
                (Lean.Expr.bvar 3)))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                (Lean.Expr.lit (Lean.Literal.natVal 8)))
              (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 8))))))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  emitProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialNumerator_eq_sum_blocks "independent_staged_reached_proof"
  compareProofSnapshot `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialNumerator_eq_sum_blocks (Lean.Expr.forallE
  `m
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `A
    (Lean.Expr.app
      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
      (Lean.Expr.const `Rat.semiring []))
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
            (Lean.Expr.const `Rat.semiring [])))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.const `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialNumerator [])
            (Lean.Expr.bvar 1))
          (Lean.Expr.bvar 0)))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Finset.sum [Lean.Level.zero, Lean.Level.zero]) (Lean.Expr.const `Nat []))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.semiring [])))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.zero])
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring [])))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.semiring []))))
          (Lean.Expr.app
            (Lean.Expr.const `Finset.range [])
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.const `Nat []))
                      (Lean.Expr.const `Nat []))
                    (Lean.Expr.const `Nat []))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `instHAdd [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                    (Lean.Expr.const `instAddNat [])))
                (Lean.Expr.bvar 1))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                  (Lean.Expr.lit (Lean.Literal.natVal 1)))
                (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 1)))))))
        (Lean.Expr.lam
          `j
          (Lean.Expr.const `Nat [])
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock [])
                (Lean.Expr.bvar 2))
              (Lean.Expr.bvar 0))
            (Lean.Expr.bvar 1))
          (Lean.BinderInfo.default))))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  emitProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialNumerator_natDegree_le "independent_staged_reached_proof"
  compareProofSnapshot `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialNumerator_natDegree_le (Lean.Expr.forallE
  `m
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `A
    (Lean.Expr.app
      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
      (Lean.Expr.const `Rat.semiring []))
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Nat []))
          (Lean.Expr.const `instLENat []))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `Polynomial.natDegree [Lean.Level.zero]) (Lean.Expr.const `Rat []))
            (Lean.Expr.const `Rat.semiring []))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.const `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialNumerator [])
              (Lean.Expr.bvar 1))
            (Lean.Expr.bvar 0))))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                  (Lean.Expr.const `Nat []))
                (Lean.Expr.const `Nat []))
              (Lean.Expr.const `Nat []))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `instHAdd [Lean.Level.zero]) (Lean.Expr.const `Nat []))
              (Lean.Expr.const `instAddNat [])))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `HMul.hMul [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.const `Nat []))
                    (Lean.Expr.const `Nat []))
                  (Lean.Expr.const `Nat []))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `instHMul [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                  (Lean.Expr.const `instMulNat [])))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                  (Lean.Expr.lit (Lean.Literal.natVal 9)))
                (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9)))))
            (Lean.Expr.bvar 1)))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
            (Lean.Expr.lit (Lean.Literal.natVal 8)))
          (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 8))))))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  emitProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_denominator_divides_actual_candidate_difference "independent_staged_reached_proof"
  compareProofSnapshot `ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_denominator_divides_actual_candidate_difference (Lean.Expr.forallE
  `m
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `A
    (Lean.Expr.app
      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
      (Lean.Expr.const `Rat.semiring []))
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.const `Dvd.dvd [Lean.Level.zero])
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.semiring [])))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.const `semigroupDvd [Lean.Level.zero])
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.semiring [])))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `SemigroupWithZero.toSemigroup [Lean.Level.zero])
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring [])))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `NonUnitalSemiring.toSemigroupWithZero [Lean.Level.zero])
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring [])))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `NonUnitalCommSemiring.toNonUnitalSemiring [Lean.Level.zero])
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `NonUnitalCommRing.toNonUnitalCommSemiring [Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toNonUnitalCommRing [Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Polynomial.commRing [Lean.Level.zero])
                          (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.commRing [])))))))))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `HPow.hPow [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.const `Nat []))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring [])))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `instHPow [Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.const `Nat []))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `NPow.toPow [Lean.Level.zero])
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Monoid.toNPow [Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Semiring.toMonoid [Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                          (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))))))
            (Lean.Expr.app (Lean.Expr.const `ZetaNine.CoefficientMapInjectivity.polePolynomial []) (Lean.Expr.bvar 1)))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
              (Lean.Expr.lit (Lean.Literal.natVal 9)))
            (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9))))))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `HSub.hSub [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring [])))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring [])))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.semiring [])))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `instHSub [Lean.Level.zero])
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring [])))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Polynomial.instSub [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `DivisionRing.toRing [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.instDivisionRing [])))))
          (Lean.Expr.bvar 0))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.const `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialNumerator [])
            (Lean.Expr.bvar 1))
          (Lean.Expr.bvar 0))))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  emitProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_different_block_pole_divisibility "independent_staged_reached_proof"
  compareProofSnapshot `ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_different_block_pole_divisibility (Lean.Expr.forallE
  `m
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `i
    (Lean.Expr.const `Nat [])
    (Lean.Expr.forallE
      `j
      (Lean.Expr.const `Nat [])
      (Lean.Expr.forallE
        `A
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
          (Lean.Expr.const `Rat.semiring []))
        (Lean.Expr.forallE
          `hj
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                (Lean.Expr.const `instLENat []))
              (Lean.Expr.bvar 1))
            (Lean.Expr.bvar 3))
          (Lean.Expr.forallE
            `hji
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Ne [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Nat []))
                (Lean.Expr.bvar 2))
              (Lean.Expr.bvar 3))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `Dvd.dvd [Lean.Level.zero])
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `semigroupDvd [Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `SemigroupWithZero.toSemigroup [Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `NonUnitalSemiring.toSemigroupWithZero [Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `NonUnitalCommSemiring.toNonUnitalSemiring [Lean.Level.zero])
                            (Lean.Expr.app
                              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring [])))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `NonUnitalCommRing.toNonUnitalCommSemiring [Lean.Level.zero])
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.semiring [])))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommRing.toNonUnitalCommRing [Lean.Level.zero])
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Rat.semiring [])))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Polynomial.commRing [Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.commRing [])))))))))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `HPow.hPow [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.app
                              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring [])))
                          (Lean.Expr.const `Nat []))
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `instHPow [Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.app
                              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring [])))
                          (Lean.Expr.const `Nat []))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `NPow.toPow [Lean.Level.zero])
                            (Lean.Expr.app
                              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring [])))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Monoid.toNPow [Lean.Level.zero])
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.semiring [])))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Semiring.toMonoid [Lean.Level.zero])
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Rat.semiring [])))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.semiring [])))))))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Rat.semiring [])))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.semiring [])))
                            (Lean.Expr.app
                              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring [])))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `instHAdd [Lean.Level.zero])
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.semiring [])))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Polynomial.instAdd [Lean.Level.zero])
                                (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring []))))
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial.X [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const
                                    `DFunLike.coe
                                    [Lean.Level.succ (Lean.Level.zero),
                                     Lean.Level.succ (Lean.Level.zero),
                                     Lean.Level.succ (Lean.Level.zero)])
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `RingHom [Lean.Level.zero, Lean.Level.zero])
                                          (Lean.Expr.const `Rat []))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                            (Lean.Expr.const `Rat []))
                                          (Lean.Expr.const `Rat.semiring [])))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                                          (Lean.Expr.const `Rat []))
                                        (Lean.Expr.const `Rat.semiring [])))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                            (Lean.Expr.const `Rat []))
                                          (Lean.Expr.const `Rat.semiring [])))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                                          (Lean.Expr.const `Rat []))
                                        (Lean.Expr.const `Rat.semiring [])))))
                                (Lean.Expr.const `Rat []))
                              (Lean.Expr.lam
                                (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Data.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
                                (Lean.Expr.const `Rat [])
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Rat.semiring []))
                                (Lean.BinderInfo.default)))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `RingHom.instFunLike [Lean.Level.zero, Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                      (Lean.Expr.const `Rat []))
                                    (Lean.Expr.const `Rat.semiring [])))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Rat.semiring [])))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                      (Lean.Expr.const `Rat []))
                                    (Lean.Expr.const `Rat.semiring [])))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Rat.semiring [])))))
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial.C [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.instNatCast []))
                          (Lean.Expr.bvar 3)))))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                      (Lean.Expr.lit (Lean.Literal.natVal 9)))
                    (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9))))))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock [])
                    (Lean.Expr.bvar 5))
                  (Lean.Expr.bvar 4))
                (Lean.Expr.bvar 2)))
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.default))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  emitProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_different_block_shift_X_pow_dvd "independent_staged_reached_proof"
  compareProofSnapshot `ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_different_block_shift_X_pow_dvd (Lean.Expr.forallE
  `m
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `i
    (Lean.Expr.const `Nat [])
    (Lean.Expr.forallE
      `j
      (Lean.Expr.const `Nat [])
      (Lean.Expr.forallE
        `A
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
          (Lean.Expr.const `Rat.semiring []))
        (Lean.Expr.forallE
          `hj
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                (Lean.Expr.const `instLENat []))
              (Lean.Expr.bvar 1))
            (Lean.Expr.bvar 3))
          (Lean.Expr.forallE
            `hji
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Ne [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Nat []))
                (Lean.Expr.bvar 2))
              (Lean.Expr.bvar 3))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `Dvd.dvd [Lean.Level.zero])
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `semigroupDvd [Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `SemigroupWithZero.toSemigroup [Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `NonUnitalSemiring.toSemigroupWithZero [Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `NonUnitalCommSemiring.toNonUnitalSemiring [Lean.Level.zero])
                            (Lean.Expr.app
                              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring [])))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `NonUnitalCommRing.toNonUnitalCommSemiring [Lean.Level.zero])
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.semiring [])))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `CommRing.toNonUnitalCommRing [Lean.Level.zero])
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Rat.semiring [])))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Polynomial.commRing [Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.commRing [])))))))))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `HPow.hPow [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.app
                              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring [])))
                          (Lean.Expr.const `Nat []))
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `instHPow [Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.app
                              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring [])))
                          (Lean.Expr.const `Nat []))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `NPow.toPow [Lean.Level.zero])
                            (Lean.Expr.app
                              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring [])))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Monoid.toNPow [Lean.Level.zero])
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.semiring [])))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Semiring.toMonoid [Lean.Level.zero])
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Rat.semiring [])))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.semiring [])))))))
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial.X [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                      (Lean.Expr.lit (Lean.Literal.natVal 9)))
                    (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9))))))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Polynomial.comp [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring []))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock [])
                        (Lean.Expr.bvar 5))
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.bvar 2)))
                (Lean.Expr.app (Lean.Expr.const `ZetaNine.CoefficientMapJet.shiftedVariable []) (Lean.Expr.bvar 3))))
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.default))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  emitProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_full_candidate_matches_nine_jets "independent_staged_reached_proof"
  compareProofSnapshot `ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_full_candidate_matches_nine_jets (Lean.Expr.forallE
  `m
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `j
    (Lean.Expr.const `Nat [])
    (Lean.Expr.forallE
      `A
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
        (Lean.Expr.const `Rat.semiring []))
      (Lean.Expr.forallE
        `hj
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Nat []))
              (Lean.Expr.const `instLENat []))
            (Lean.Expr.bvar 1))
          (Lean.Expr.bvar 2))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `Dvd.dvd [Lean.Level.zero])
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring [])))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `semigroupDvd [Lean.Level.zero])
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring [])))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `SemigroupWithZero.toSemigroup [Lean.Level.zero])
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `NonUnitalSemiring.toSemigroupWithZero [Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `NonUnitalCommSemiring.toNonUnitalSemiring [Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `NonUnitalCommRing.toNonUnitalCommSemiring [Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `CommRing.toNonUnitalCommRing [Lean.Level.zero])
                            (Lean.Expr.app
                              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring [])))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Polynomial.commRing [Lean.Level.zero])
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.commRing [])))))))))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `HPow.hPow [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.const `Nat []))
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `instHPow [Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.const `Nat []))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `NPow.toPow [Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Monoid.toNPow [Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Semiring.toMonoid [Lean.Level.zero])
                            (Lean.Expr.app
                              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring [])))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))))))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial.X [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring [])))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                  (Lean.Expr.lit (Lean.Literal.natVal 9)))
                (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9))))))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Polynomial.comp [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.semiring []))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `HSub.hSub [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `instHSub [Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Polynomial.instSub [Lean.Level.zero])
                          (Lean.Expr.const `Rat []))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `DivisionRing.toRing [Lean.Level.zero])
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.instDivisionRing [])))))
                  (Lean.Expr.bvar 1))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialNumerator [])
                    (Lean.Expr.bvar 3))
                  (Lean.Expr.bvar 1))))
            (Lean.Expr.app (Lean.Expr.const `ZetaNine.CoefficientMapJet.shiftedVariable []) (Lean.Expr.bvar 2))))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  emitProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_own_block_matches_nine_jets "independent_staged_reached_proof"
  compareProofSnapshot `ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_own_block_matches_nine_jets (Lean.Expr.forallE
  `m
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `j
    (Lean.Expr.const `Nat [])
    (Lean.Expr.forallE
      `A
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
        (Lean.Expr.const `Rat.semiring []))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.const `Dvd.dvd [Lean.Level.zero])
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.semiring [])))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `semigroupDvd [Lean.Level.zero])
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring [])))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `SemigroupWithZero.toSemigroup [Lean.Level.zero])
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring [])))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `NonUnitalSemiring.toSemigroupWithZero [Lean.Level.zero])
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `NonUnitalCommSemiring.toNonUnitalSemiring [Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `NonUnitalCommRing.toNonUnitalCommSemiring [Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toNonUnitalCommRing [Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Polynomial.commRing [Lean.Level.zero])
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.commRing [])))))))))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `HPow.hPow [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.const `Nat []))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring [])))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `instHPow [Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.const `Nat []))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `NPow.toPow [Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Monoid.toNPow [Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Semiring.toMonoid [Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))))))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Polynomial.X [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.semiring [])))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                (Lean.Expr.lit (Lean.Literal.natVal 9)))
              (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9))))))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `HSub.hSub [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring [])))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring [])))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `instHSub [Lean.Level.zero])
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring [])))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial.instSub [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `DivisionRing.toRing [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.instDivisionRing [])))))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial.comp [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring []))
                (Lean.Expr.bvar 0))
              (Lean.Expr.app (Lean.Expr.const `ZetaNine.CoefficientMapJet.shiftedVariable []) (Lean.Expr.bvar 1))))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Polynomial.comp [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.semiring []))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock [])
                    (Lean.Expr.bvar 2))
                  (Lean.Expr.bvar 1))
                (Lean.Expr.bvar 0)))
            (Lean.Expr.app (Lean.Expr.const `ZetaNine.CoefficientMapJet.shiftedVariable []) (Lean.Expr.bvar 1)))))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  emitProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_partial_term_division "independent_staged_reached_proof"
  compareProofSnapshot `ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_partial_term_division (Lean.Expr.forallE
  `m
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `j
    (Lean.Expr.const `Nat [])
    (Lean.Expr.forallE
      `s
      (Lean.Expr.const `Nat [])
      (Lean.Expr.forallE
        `A
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
          (Lean.Expr.const `Rat.semiring []))
        (Lean.Expr.forallE
          `t
          (Lean.Expr.const `Rat [])
          (Lean.Expr.forallE
            `hj
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                  (Lean.Expr.const `instLENat []))
                (Lean.Expr.bvar 3))
              (Lean.Expr.bvar 4))
            (Lean.Expr.forallE
              `hs1
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                    (Lean.Expr.const `instLENat []))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                      (Lean.Expr.lit (Lean.Literal.natVal 1)))
                    (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 1)))))
                (Lean.Expr.bvar 3))
              (Lean.Expr.forallE
                `hs9
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                      (Lean.Expr.const `instLENat []))
                    (Lean.Expr.bvar 4))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                      (Lean.Expr.lit (Lean.Literal.natVal 9)))
                    (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9)))))
                (Lean.Expr.forallE
                  `hregular
                  (Lean.Expr.forallE
                    `k
                    (Lean.Expr.const `Nat [])
                    (Lean.Expr.forallE
                      (Lean.Name.mkNum `a._@._internal._hyg 0)
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                            (Lean.Expr.const `instLENat []))
                          (Lean.Expr.bvar 0))
                        (Lean.Expr.bvar 8))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Ne [Lean.Level.succ (Lean.Level.zero)])
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                      (Lean.Expr.const `Rat []))
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `instHAdd [Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Rat.instAdd [])))
                              (Lean.Expr.bvar 5))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.instNatCast []))
                              (Lean.Expr.bvar 1))))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.lit (Lean.Literal.natVal 0)))
                          (Lean.Expr.app (Lean.Expr.const `Rat.instOfNat []) (Lean.Expr.lit (Lean.Literal.natVal 0)))))
                      (Lean.BinderInfo.default))
                    (Lean.BinderInfo.default))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
                        (Lean.Expr.const `Rat []))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `HDiv.hDiv [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.app
                              (Lean.Expr.app (Lean.Expr.const `instHDiv [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.instDiv [])))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `HMul.hMul [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                      (Lean.Expr.const `Rat []))
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `instHMul [Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Rat.instMul [])))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `HMul.hMul
                                            [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                          (Lean.Expr.const `Rat []))
                                        (Lean.Expr.const `Rat []))
                                      (Lean.Expr.const `Rat []))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `instHMul [Lean.Level.zero])
                                        (Lean.Expr.const `Rat []))
                                      (Lean.Expr.const `Rat.instMul [])))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `ZetaNine.CoefficientMapFormalTransportData.numeratorLocalCoefficient
                                            [])
                                          (Lean.Expr.bvar 8))
                                        (Lean.Expr.bvar 7))
                                      (Lean.Expr.bvar 6))
                                    (Lean.Expr.bvar 5)))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `HPow.hPow
                                              [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                            (Lean.Expr.const `Rat []))
                                          (Lean.Expr.const `Nat []))
                                        (Lean.Expr.const `Rat []))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `instHPow [Lean.Level.zero, Lean.Level.zero])
                                            (Lean.Expr.const `Rat []))
                                          (Lean.Expr.const `Nat []))
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `NPow.toPow [Lean.Level.zero])
                                            (Lean.Expr.const `Rat []))
                                          (Lean.Expr.app
                                            (Lean.Expr.app
                                              (Lean.Expr.const `Monoid.toNPow [Lean.Level.zero])
                                              (Lean.Expr.const `Rat []))
                                            (Lean.Expr.const `Rat.monoid [])))))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const `Polynomial.eval [Lean.Level.zero])
                                            (Lean.Expr.const `Rat []))
                                          (Lean.Expr.const `Rat.semiring []))
                                        (Lean.Expr.bvar 4))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial
                                            [])
                                          (Lean.Expr.bvar 8))
                                        (Lean.Expr.bvar 7))))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero])
                                        (Lean.Expr.const `Nat []))
                                      (Lean.Expr.lit (Lean.Literal.natVal 9)))
                                    (Lean.Expr.app
                                      (Lean.Expr.const `instOfNatNat [])
                                      (Lean.Expr.lit (Lean.Literal.natVal 9)))))))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `HPow.hPow [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                        (Lean.Expr.const `Rat []))
                                      (Lean.Expr.const `Nat []))
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `instHPow [Lean.Level.zero, Lean.Level.zero])
                                        (Lean.Expr.const `Rat []))
                                      (Lean.Expr.const `Nat []))
                                    (Lean.Expr.const `Rat.instPowNat [])))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.app
                                            (Lean.Expr.const
                                              `HAdd.hAdd
                                              [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                            (Lean.Expr.const `Rat []))
                                          (Lean.Expr.const `Rat []))
                                        (Lean.Expr.const `Rat []))
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const `instHAdd [Lean.Level.zero])
                                          (Lean.Expr.const `Rat []))
                                        (Lean.Expr.const `Rat.instAdd [])))
                                    (Lean.Expr.bvar 4))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `Nat.cast [Lean.Level.zero])
                                        (Lean.Expr.const `Rat []))
                                      (Lean.Expr.const `Rat.instNatCast []))
                                    (Lean.Expr.bvar 7))))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `HSub.hSub
                                            [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                          (Lean.Expr.const `Nat []))
                                        (Lean.Expr.const `Nat []))
                                      (Lean.Expr.const `Nat []))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `instHSub [Lean.Level.zero])
                                        (Lean.Expr.const `Nat []))
                                      (Lean.Expr.const `instSubNat [])))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero])
                                        (Lean.Expr.const `Nat []))
                                      (Lean.Expr.lit (Lean.Literal.natVal 9)))
                                    (Lean.Expr.app
                                      (Lean.Expr.const `instOfNatNat [])
                                      (Lean.Expr.lit (Lean.Literal.natVal 9)))))
                                (Lean.Expr.bvar 6)))))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `HPow.hPow [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Nat []))
                                (Lean.Expr.const `Rat []))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `instHPow [Lean.Level.zero, Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Nat []))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `NPow.toPow [Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `Monoid.toNPow [Lean.Level.zero])
                                      (Lean.Expr.const `Rat []))
                                    (Lean.Expr.const `Rat.monoid [])))))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Polynomial.eval [Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Rat.semiring []))
                                (Lean.Expr.bvar 4))
                              (Lean.Expr.app
                                (Lean.Expr.const `ZetaNine.CoefficientMapInjectivity.polePolynomial [])
                                (Lean.Expr.bvar 8))))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                              (Lean.Expr.lit (Lean.Literal.natVal 9)))
                            (Lean.Expr.app
                              (Lean.Expr.const `instOfNatNat [])
                              (Lean.Expr.lit (Lean.Literal.natVal 9)))))))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `HDiv.hDiv [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `instHDiv [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.instDiv [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const
                                  `ZetaNine.CoefficientMapFormalTransportData.numeratorLocalCoefficient
                                  [])
                                (Lean.Expr.bvar 8))
                              (Lean.Expr.bvar 7))
                            (Lean.Expr.bvar 6))
                          (Lean.Expr.bvar 5)))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `HPow.hPow [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Nat []))
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `instHPow [Lean.Level.zero, Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Nat []))
                              (Lean.Expr.const `Rat.instPowNat [])))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                      (Lean.Expr.const `Rat []))
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `instHAdd [Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Rat.instAdd [])))
                              (Lean.Expr.bvar 4))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.instNatCast []))
                              (Lean.Expr.bvar 7))))
                        (Lean.Expr.bvar 6))))
                  (Lean.BinderInfo.default))
                (Lean.BinderInfo.default))
              (Lean.BinderInfo.default))
            (Lean.BinderInfo.default))
          (Lean.BinderInfo.default))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  emitProof `ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial_comp_shift "independent_staged_reached_proof"
  compareProofSnapshot `ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial_comp_shift (Lean.Expr.forallE
  `n
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `j
    (Lean.Expr.const `Nat [])
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
            (Lean.Expr.const `Rat.semiring [])))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Polynomial.comp [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.semiring []))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial [])
                (Lean.Expr.bvar 1))
              (Lean.Expr.bvar 0)))
          (Lean.Expr.app (Lean.Expr.const `ZetaNine.CoefficientMapJet.shiftedVariable []) (Lean.Expr.bvar 0))))
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `ZetaNine.CoefficientMapJet.shiftedClearedDenominator []) (Lean.Expr.bvar 1))
        (Lean.Expr.bvar 0)))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  emitProof `ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial_natDegree "independent_staged_reached_proof"
  compareProofSnapshot `ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial_natDegree (Lean.Expr.forallE
  `n
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `j
    (Lean.Expr.const `Nat [])
    (Lean.Expr.forallE
      `hj
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Nat []))
            (Lean.Expr.const `instLENat []))
          (Lean.Expr.bvar 0))
        (Lean.Expr.bvar 1))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Nat []))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Polynomial.natDegree [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.semiring []))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial [])
                (Lean.Expr.bvar 2))
              (Lean.Expr.bvar 1))))
        (Lean.Expr.bvar 2))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  emitProof `ZetaNine.CoefficientMapPartialFractions.polePolynomial_eval "independent_staged_reached_proof"
  compareProofSnapshot `ZetaNine.CoefficientMapPartialFractions.polePolynomial_eval (Lean.Expr.forallE
  `n
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `t
    (Lean.Expr.const `Rat [])
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Rat []))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Polynomial.eval [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.semiring []))
            (Lean.Expr.bvar 0))
          (Lean.Expr.app (Lean.Expr.const `ZetaNine.CoefficientMapInjectivity.polePolynomial []) (Lean.Expr.bvar 1))))
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `ZetaNine.CoefficientMap.poleProduct []) (Lean.Expr.bvar 1))
        (Lean.Expr.bvar 0)))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  emitProof `ZetaNine.CoefficientMapPartialFractions.polePolynomial_eval_factor "independent_staged_reached_proof"
  compareProofSnapshot `ZetaNine.CoefficientMapPartialFractions.polePolynomial_eval_factor (Lean.Expr.forallE
  `n
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `j
    (Lean.Expr.const `Nat [])
    (Lean.Expr.forallE
      `t
      (Lean.Expr.const `Rat [])
      (Lean.Expr.forallE
        `hj
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Nat []))
              (Lean.Expr.const `instLENat []))
            (Lean.Expr.bvar 1))
          (Lean.Expr.bvar 2))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Rat []))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial.eval [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring []))
                (Lean.Expr.bvar 1))
              (Lean.Expr.app
                (Lean.Expr.const `ZetaNine.CoefficientMapInjectivity.polePolynomial [])
                (Lean.Expr.bvar 3))))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `HMul.hMul [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat []))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `instHMul [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.instMul [])))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat []))
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `instHAdd [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.instAdd [])))
                  (Lean.Expr.bvar 1))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.instNatCast []))
                  (Lean.Expr.bvar 2))))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial.eval [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring []))
                (Lean.Expr.bvar 1))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial [])
                  (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 2)))))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  emitProof `ZetaNine.CoefficientMapPartialFractions.polePolynomial_eval_ne_zero "independent_staged_reached_proof"
  compareProofSnapshot `ZetaNine.CoefficientMapPartialFractions.polePolynomial_eval_ne_zero (Lean.Expr.forallE
  `n
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `t
    (Lean.Expr.const `Rat [])
    (Lean.Expr.forallE
      `hregular
      (Lean.Expr.forallE
        `k
        (Lean.Expr.const `Nat [])
        (Lean.Expr.forallE
          (Lean.Name.mkNum `a._@._internal._hyg 0)
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                (Lean.Expr.const `instLENat []))
              (Lean.Expr.bvar 0))
            (Lean.Expr.bvar 2))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Ne [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Rat []))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat []))
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `instHAdd [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.instAdd [])))
                  (Lean.Expr.bvar 2))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.instNatCast []))
                  (Lean.Expr.bvar 1))))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.lit (Lean.Literal.natVal 0)))
              (Lean.Expr.app (Lean.Expr.const `Rat.instOfNat []) (Lean.Expr.lit (Lean.Literal.natVal 0)))))
          (Lean.BinderInfo.default))
        (Lean.BinderInfo.default))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `Ne [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Rat []))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Polynomial.eval [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.semiring []))
              (Lean.Expr.bvar 1))
            (Lean.Expr.app (Lean.Expr.const `ZetaNine.CoefficientMapInjectivity.polePolynomial []) (Lean.Expr.bvar 2))))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Rat []))
            (Lean.Expr.lit (Lean.Literal.natVal 0)))
          (Lean.Expr.app (Lean.Expr.const `Rat.instOfNat []) (Lean.Expr.lit (Lean.Literal.natVal 0)))))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  emitProof `ZetaNine.CoefficientMapPartialFractions.polynomial_X_pow_dvd_of_series "independent_staged_reached_proof"
  compareProofSnapshot `ZetaNine.CoefficientMapPartialFractions.polynomial_X_pow_dvd_of_series (Lean.Expr.forallE
  `P
  (Lean.Expr.app
    (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
    (Lean.Expr.const `Rat.semiring []))
  (Lean.Expr.forallE
    `h
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.const `Dvd.dvd [Lean.Level.zero])
            (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.const `semigroupDvd [Lean.Level.zero])
              (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `SemigroupWithZero.toSemigroup [Lean.Level.zero])
                (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `NonUnitalSemiring.toSemigroupWithZero [Lean.Level.zero])
                  (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `NonUnitalCommSemiring.toNonUnitalSemiring [Lean.Level.zero])
                    (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `NonUnitalCommRing.toNonUnitalCommSemiring [Lean.Level.zero])
                      (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toNonUnitalCommRing [Lean.Level.zero])
                        (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `MvPowerSeries.instCommRing [Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.const `Unit []))
                          (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.commRing [])))))))))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `HPow.hPow [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                  (Lean.Expr.const `Nat []))
                (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `instHPow [Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                  (Lean.Expr.const `Nat []))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `NPow.toPow [Lean.Level.zero])
                    (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Monoid.toNPow [Lean.Level.zero])
                      (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Semiring.toMonoid [Lean.Level.zero])
                        (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `MvPowerSeries.instSemiring [Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.const `Unit []))
                          (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))))))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `PowerSeries.X [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.semiring [])))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
              (Lean.Expr.lit (Lean.Literal.natVal 9)))
            (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9))))))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `Polynomial.toPowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat []))
          (Lean.Expr.const `Rat.semiring []))
        (Lean.Expr.bvar 0)))
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.const `Dvd.dvd [Lean.Level.zero])
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.semiring [])))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.const `semigroupDvd [Lean.Level.zero])
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.semiring [])))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `SemigroupWithZero.toSemigroup [Lean.Level.zero])
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring [])))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `NonUnitalSemiring.toSemigroupWithZero [Lean.Level.zero])
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring [])))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `NonUnitalCommSemiring.toNonUnitalSemiring [Lean.Level.zero])
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `NonUnitalCommRing.toNonUnitalCommSemiring [Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `CommRing.toNonUnitalCommRing [Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Polynomial.commRing [Lean.Level.zero])
                          (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.commRing [])))))))))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `HPow.hPow [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.const `Nat []))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring [])))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `instHPow [Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.const `Nat []))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `NPow.toPow [Lean.Level.zero])
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Monoid.toNPow [Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Semiring.toMonoid [Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                          (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))))))
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Polynomial.X [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.semiring [])))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
              (Lean.Expr.lit (Lean.Literal.natVal 9)))
            (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9))))))
      (Lean.Expr.bvar 1))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  emitProof `ZetaNine.CoefficientMapPartialFractions.shifted_divisibility_implies_pole_divisibility "independent_staged_reached_proof"
  compareProofSnapshot `ZetaNine.CoefficientMapPartialFractions.shifted_divisibility_implies_pole_divisibility (Lean.Expr.forallE
  `P
  (Lean.Expr.app
    (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
    (Lean.Expr.const `Rat.semiring []))
  (Lean.Expr.forallE
    `j
    (Lean.Expr.const `Nat [])
    (Lean.Expr.forallE
      `h
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.const `Dvd.dvd [Lean.Level.zero])
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.semiring [])))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `semigroupDvd [Lean.Level.zero])
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring [])))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `SemigroupWithZero.toSemigroup [Lean.Level.zero])
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring [])))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `NonUnitalSemiring.toSemigroupWithZero [Lean.Level.zero])
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `NonUnitalCommSemiring.toNonUnitalSemiring [Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `NonUnitalCommRing.toNonUnitalCommSemiring [Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toNonUnitalCommRing [Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Polynomial.commRing [Lean.Level.zero])
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.commRing [])))))))))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `HPow.hPow [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.const `Nat []))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring [])))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `instHPow [Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.const `Nat []))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `NPow.toPow [Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Monoid.toNPow [Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Semiring.toMonoid [Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))))))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Polynomial.X [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.semiring [])))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                (Lean.Expr.lit (Lean.Literal.natVal 9)))
              (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9))))))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Polynomial.comp [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.semiring []))
            (Lean.Expr.bvar 1))
          (Lean.Expr.app (Lean.Expr.const `ZetaNine.CoefficientMapJet.shiftedVariable []) (Lean.Expr.bvar 0))))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.const `Dvd.dvd [Lean.Level.zero])
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.semiring [])))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `semigroupDvd [Lean.Level.zero])
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring [])))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `SemigroupWithZero.toSemigroup [Lean.Level.zero])
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring [])))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `NonUnitalSemiring.toSemigroupWithZero [Lean.Level.zero])
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `NonUnitalCommSemiring.toNonUnitalSemiring [Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `NonUnitalCommRing.toNonUnitalCommSemiring [Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `CommRing.toNonUnitalCommRing [Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Polynomial.commRing [Lean.Level.zero])
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.commRing [])))))))))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `HPow.hPow [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.const `Nat []))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring [])))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `instHPow [Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.const `Nat []))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `NPow.toPow [Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `Monoid.toNPow [Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Semiring.toMonoid [Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))))))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `instHAdd [Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Polynomial.instAdd [Lean.Level.zero])
                          (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring []))))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Polynomial.X [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring [])))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const
                              `DFunLike.coe
                              [Lean.Level.succ (Lean.Level.zero),
                               Lean.Level.succ (Lean.Level.zero),
                               Lean.Level.succ (Lean.Level.zero)])
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `RingHom [Lean.Level.zero, Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                      (Lean.Expr.const `Rat []))
                                    (Lean.Expr.const `Rat.semiring [])))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Rat.semiring [])))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                      (Lean.Expr.const `Rat []))
                                    (Lean.Expr.const `Rat.semiring [])))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Rat.semiring [])))))
                          (Lean.Expr.const `Rat []))
                        (Lean.Expr.lam
                          (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Data.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
                          (Lean.Expr.const `Rat [])
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring []))
                          (Lean.BinderInfo.default)))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `RingHom.instFunLike [Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.app
                              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring [])))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                            (Lean.Expr.app
                              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring [])))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))))
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial.C [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.instNatCast []))
                    (Lean.Expr.bvar 1)))))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                (Lean.Expr.lit (Lean.Literal.natVal 9)))
              (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9))))))
        (Lean.Expr.bvar 2))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  emitProof `ZetaNine.CoefficientMapPartialFractions.truncation_remainder_X_pow_dvd "independent_staged_reached_proof"
  compareProofSnapshot `ZetaNine.CoefficientMapPartialFractions.truncation_remainder_X_pow_dvd (Lean.Expr.forallE
  `S
  (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat []))
  (Lean.Expr.app
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.const `Dvd.dvd [Lean.Level.zero])
          (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.const `semigroupDvd [Lean.Level.zero])
            (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.const `SemigroupWithZero.toSemigroup [Lean.Level.zero])
              (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `NonUnitalSemiring.toSemigroupWithZero [Lean.Level.zero])
                (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `NonUnitalCommSemiring.toNonUnitalSemiring [Lean.Level.zero])
                  (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `NonUnitalCommRing.toNonUnitalCommSemiring [Lean.Level.zero])
                    (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `CommRing.toNonUnitalCommRing [Lean.Level.zero])
                      (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `MvPowerSeries.instCommRing [Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.const `Unit []))
                        (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.commRing [])))))))))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `HPow.hPow [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                  (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                (Lean.Expr.const `Nat []))
              (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `instHPow [Lean.Level.zero, Lean.Level.zero])
                  (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                (Lean.Expr.const `Nat []))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `NPow.toPow [Lean.Level.zero])
                  (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `Monoid.toNPow [Lean.Level.zero])
                    (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Semiring.toMonoid [Lean.Level.zero])
                      (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `MvPowerSeries.instSemiring [Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.const `Unit []))
                        (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))))))
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `PowerSeries.X [Lean.Level.zero]) (Lean.Expr.const `Rat []))
            (Lean.Expr.const `Rat.semiring [])))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
            (Lean.Expr.lit (Lean.Literal.natVal 9)))
          (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9))))))
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `HSub.hSub [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
              (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
            (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.const `instHSub [Lean.Level.zero])
              (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `SubNegMonoid.toSub [Lean.Level.zero])
                (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `AddGroup.toSubNegMonoid [Lean.Level.zero])
                  (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `MvPowerSeries.instAddGroup [Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.const `Unit []))
                    (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.addGroup []))))))
        (Lean.Expr.bvar 0))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app (Lean.Expr.const `Polynomial.toPowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat []))
          (Lean.Expr.const `Rat.semiring []))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const
                      `DFunLike.coe
                      [Lean.Level.succ (Lean.Level.zero),
                       Lean.Level.succ (Lean.Level.zero),
                       Lean.Level.succ (Lean.Level.zero)])
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.app
                                          (Lean.Expr.const
                                            `LinearMap
                                            [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                          (Lean.Expr.const `Rat []))
                                        (Lean.Expr.const `Rat []))
                                      (Lean.Expr.const `Rat.semiring []))
                                    (Lean.Expr.const `Rat.semiring []))
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `RingHom.id [Lean.Level.zero])
                                      (Lean.Expr.const `Rat []))
                                    (Lean.Expr.app
                                      (Lean.Expr.app
                                        (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                                        (Lean.Expr.const `Rat []))
                                      (Lean.Expr.const `Rat.semiring []))))
                                (Lean.Expr.app
                                  (Lean.Expr.const `PowerSeries [Lean.Level.zero])
                                  (Lean.Expr.const `Rat [])))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.semiring [])))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `MvPowerSeries.instAddCommMonoid [Lean.Level.zero, Lean.Level.zero])
                                  (Lean.Expr.const `Unit []))
                                (Lean.Expr.const `Rat []))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.semiring []))))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.zero])
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.semiring [])))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                                (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring []))))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `MvPowerSeries.instModule
                                      [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                    (Lean.Expr.const `Unit []))
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring []))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.zero])
                                (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring [])))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Semiring.toModule [Lean.Level.zero])
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring []))))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Polynomial.module [Lean.Level.zero, Lean.Level.zero])
                                (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring []))
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring []))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Semiring.toModule [Lean.Level.zero])
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))))
                  (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat [])))
                (Lean.Expr.lam
                  (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Data.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
                  (Lean.Expr.app (Lean.Expr.const `PowerSeries [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring []))
                  (Lean.BinderInfo.default)))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const
                                      `LinearMap.instFunLike
                                      [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.app
                                  (Lean.Expr.const `PowerSeries [Lean.Level.zero])
                                  (Lean.Expr.const `Rat [])))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.semiring [])))
                            (Lean.Expr.const `Rat.semiring []))
                          (Lean.Expr.const `Rat.semiring []))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `MvPowerSeries.instAddCommMonoid [Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.const `Unit []))
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.zero])
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring []))))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring []))))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const
                                  `MvPowerSeries.instModule
                                  [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                (Lean.Expr.const `Unit []))
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring []))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Semiring.toAddCommMonoid [Lean.Level.zero])
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Semiring.toModule [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring []))))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Polynomial.module [Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring []))
                        (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring []))
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Semiring.toModule [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring []))))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `RingHom.id [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                      (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring [])))))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `PowerSeries.trunc [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.semiring []))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                  (Lean.Expr.lit (Lean.Literal.natVal 9)))
                (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9))))))
          (Lean.Expr.bvar 0)))))
  (Lean.BinderInfo.default))
  emitProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock.eq_1 "independent_staged_reached_proof"
  compareProofSnapshot `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock.eq_1 (Lean.Expr.forallE
  `m
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `j
    (Lean.Expr.const `Nat [])
    (Lean.Expr.forallE
      `A
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
        (Lean.Expr.const `Rat.semiring []))
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)])
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.semiring [])))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.const `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock [])
                (Lean.Expr.bvar 2))
              (Lean.Expr.bvar 1))
            (Lean.Expr.bvar 0)))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `HMul.hMul [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring [])))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring [])))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.const `instHMul [Lean.Level.zero])
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring [])))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial.instMul [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring []))))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `HPow.hPow [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.const `Nat []))
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `instHPow [Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.const `Nat []))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `NPow.toPow [Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Monoid.toNPow [Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Semiring.toMonoid [Lean.Level.zero])
                            (Lean.Expr.app
                              (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat.semiring [])))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))))))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial [])
                    (Lean.Expr.bvar 2))
                  (Lean.Expr.bvar 1)))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                  (Lean.Expr.lit (Lean.Literal.natVal 9)))
                (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9))))))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `Polynomial.comp [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                (Lean.Expr.const `Rat.semiring []))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalTruncation [])
                    (Lean.Expr.bvar 2))
                  (Lean.Expr.bvar 1))
                (Lean.Expr.bvar 0)))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring [])))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `instHAdd [Lean.Level.zero])
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring [])))
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `Polynomial.instAdd [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.semiring []))))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Polynomial.X [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.semiring [])))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const
                            `DFunLike.coe
                            [Lean.Level.succ (Lean.Level.zero),
                             Lean.Level.succ (Lean.Level.zero),
                             Lean.Level.succ (Lean.Level.zero)])
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `RingHom [Lean.Level.zero, Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Rat.semiring [])))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.semiring [])))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `Polynomial [Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Rat.semiring [])))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.semiring [])))))
                        (Lean.Expr.const `Rat []))
                      (Lean.Expr.lam
                        (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Mathlib.Data.FunLike.Basic 2582841819) "_hygCtx") "_hyg") 11)
                        (Lean.Expr.const `Rat [])
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring []))
                        (Lean.BinderInfo.default)))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `RingHom.instFunLike [Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Semiring.toNonAssocSemiring [Lean.Level.zero])
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.semiring [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Polynomial.semiring [Lean.Level.zero])
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring [])))))
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Polynomial.C [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.semiring [])))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.const `Rat.instNatCast []))
                  (Lean.Expr.bvar 1)))))))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  compareProofSnapshot `solution (Lean.Expr.forallE
  `m
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `A
    (Lean.Expr.app
      (Lean.Expr.app (Lean.Expr.const `Polynomial [Lean.Level.zero]) (Lean.Expr.const `Rat []))
      (Lean.Expr.const `Rat.semiring []))
    (Lean.Expr.forallE
      `hproper
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `LT.lt [Lean.Level.zero]) (Lean.Expr.const `Nat []))
            (Lean.Expr.const `instLTNat []))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Polynomial.natDegree [Lean.Level.zero]) (Lean.Expr.const `Rat []))
              (Lean.Expr.const `Rat.semiring []))
            (Lean.Expr.bvar 0)))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.const `HMul.hMul [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                    (Lean.Expr.const `Nat []))
                  (Lean.Expr.const `Nat []))
                (Lean.Expr.const `Nat []))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `instHMul [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                (Lean.Expr.const `instMulNat [])))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                (Lean.Expr.lit (Lean.Literal.natVal 9)))
              (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9)))))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.const `Nat []))
                    (Lean.Expr.const `Nat []))
                  (Lean.Expr.const `Nat []))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `instHAdd [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                  (Lean.Expr.const `instAddNat [])))
              (Lean.Expr.bvar 1))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                (Lean.Expr.lit (Lean.Literal.natVal 1)))
              (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 1)))))))
      (Lean.Expr.forallE
        `t
        (Lean.Expr.const `Rat [])
        (Lean.Expr.forallE
          `hregular
          (Lean.Expr.forallE
            `k
            (Lean.Expr.const `Nat [])
            (Lean.Expr.forallE
              (Lean.Name.mkNum `a._@._internal._hyg 0)
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `LE.le [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                    (Lean.Expr.const `instLENat []))
                  (Lean.Expr.bvar 0))
                (Lean.Expr.bvar 4))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Ne [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Rat []))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat []))
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `instHAdd [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.instAdd [])))
                      (Lean.Expr.bvar 2))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.instNatCast []))
                      (Lean.Expr.bvar 1))))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                    (Lean.Expr.lit (Lean.Literal.natVal 0)))
                  (Lean.Expr.app (Lean.Expr.const `Rat.instOfNat []) (Lean.Expr.lit (Lean.Literal.natVal 0)))))
              (Lean.BinderInfo.default))
            (Lean.BinderInfo.default))
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Rat []))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `HDiv.hDiv [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat []))
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `instHDiv [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.instDiv [])))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Polynomial.eval [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                        (Lean.Expr.const `Rat.semiring []))
                      (Lean.Expr.bvar 1))
                    (Lean.Expr.bvar 3)))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `HPow.hPow [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Nat []))
                        (Lean.Expr.const `Rat []))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `instHPow [Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Nat []))
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `NPow.toPow [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Monoid.toNPow [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.monoid [])))))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `Polynomial.eval [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                          (Lean.Expr.const `Rat.semiring []))
                        (Lean.Expr.bvar 1))
                      (Lean.Expr.app
                        (Lean.Expr.const `ZetaNine.CoefficientMapInjectivity.polePolynomial [])
                        (Lean.Expr.bvar 4))))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                      (Lean.Expr.lit (Lean.Literal.natVal 9)))
                    (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9)))))))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `Finset.sum [Lean.Level.zero, Lean.Level.zero])
                      (Lean.Expr.const `Nat []))
                    (Lean.Expr.const `Rat []))
                  (Lean.Expr.const `Rat.addCommMonoid []))
                (Lean.Expr.app
                  (Lean.Expr.const `Finset.range [])
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                              (Lean.Expr.const `Nat []))
                            (Lean.Expr.const `Nat []))
                          (Lean.Expr.const `Nat []))
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `instHAdd [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                          (Lean.Expr.const `instAddNat [])))
                      (Lean.Expr.bvar 4))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                        (Lean.Expr.lit (Lean.Literal.natVal 1)))
                      (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 1)))))))
              (Lean.Expr.lam
                `j
                (Lean.Expr.const `Nat [])
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Finset.sum [Lean.Level.zero, Lean.Level.zero])
                          (Lean.Expr.const `Nat []))
                        (Lean.Expr.const `Rat []))
                      (Lean.Expr.const `Rat.addCommMonoid []))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `Finset.Icc [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                            (Lean.Expr.const `Nat.instPreorder []))
                          (Lean.Expr.const `Nat.instLocallyFiniteOrder []))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                            (Lean.Expr.lit (Lean.Literal.natVal 1)))
                          (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 1)))))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                          (Lean.Expr.lit (Lean.Literal.natVal 9)))
                        (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 9))))))
                  (Lean.Expr.lam
                    `s
                    (Lean.Expr.const `Nat [])
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `HDiv.hDiv [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                (Lean.Expr.const `Rat []))
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat []))
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `instHDiv [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                            (Lean.Expr.const `Rat.instDiv [])))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const
                                  `ZetaNine.CoefficientMapFormalTransportData.numeratorLocalCoefficient
                                  [])
                                (Lean.Expr.bvar 6))
                              (Lean.Expr.bvar 1))
                            (Lean.Expr.bvar 0))
                          (Lean.Expr.bvar 5)))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `HPow.hPow [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Nat []))
                              (Lean.Expr.const `Rat []))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `instHPow [Lean.Level.zero, Lean.Level.zero])
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Nat []))
                              (Lean.Expr.const `Rat.instPowNat [])))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                                      (Lean.Expr.const `Rat []))
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Rat []))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `instHAdd [Lean.Level.zero])
                                    (Lean.Expr.const `Rat []))
                                  (Lean.Expr.const `Rat.instAdd [])))
                              (Lean.Expr.bvar 3))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app (Lean.Expr.const `Nat.cast [Lean.Level.zero]) (Lean.Expr.const `Rat []))
                                (Lean.Expr.const `Rat.instNatCast []))
                              (Lean.Expr.bvar 1))))
                        (Lean.Expr.bvar 0)))
                    (Lean.BinderInfo.default)))
                (Lean.BinderInfo.default))))
          (Lean.BinderInfo.default))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default))
  compareWhole `ZetaNine.CoefficientMapFormalTransportData.numeratorClearedSeries `PFIndependentFormula.numeratorClearedSeries
  emitProof `whole_rfl_numeratorClearedSeries "independent_whole_function_rfl"
  compareWhole `ZetaNine.CoefficientMapFormalTransportData.numeratorLocalCoefficient `PFIndependentFormula.numeratorLocalCoefficient
  emitProof `whole_rfl_numeratorLocalCoefficient "independent_whole_function_rfl"
  compareWhole `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalTruncation `PFIndependentFormula.numeratorLocalTruncation
  emitProof `whole_rfl_numeratorLocalTruncation "independent_whole_function_rfl"
  compareWhole `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock `PFIndependentFormula.numeratorPartialBlock
  emitProof `whole_rfl_numeratorPartialBlock "independent_whole_function_rfl"
  compareWhole `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialNumerator `PFIndependentFormula.numeratorPartialNumerator
  emitProof `whole_rfl_numeratorPartialNumerator "independent_whole_function_rfl"
  emitProof `PFIndependentExpected.expected_polynomial "independent_expected_complete_forall"
  compareType `ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_polynomial_partial_fractions `PFIndependentExpected.expected_polynomial
  emitProof `PFIndependentExpected.expected_global "independent_expected_complete_forall"
  compareType `ZetaNine.CoefficientMapNumeratorPartialFractions.checked_actual_numerator_global_partial_fractions `PFIndependentExpected.expected_global
  emitProof `PFIndependentExpected.expected_injective "independent_expected_complete_forall"
  compareType `ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_local_coefficients_injective `PFIndependentExpected.expected_injective
  emitProof `PFIndependentBoundary.zero_jet "independent_actual_closed_boundary"
  emitProof `PFIndependentBoundary.zero_reconstruction "independent_actual_closed_boundary"
  emitProof `PFIndependentBoundary.m0_one "independent_actual_closed_boundary"
  emitProof `PFIndependentBoundary.m0_critical_X8 "independent_actual_closed_boundary"
  emitProof `PFIndependentBoundary.m0_X9_outside_proper "independent_actual_closed_boundary"
  emitProof `PFIndependentBoundary.m0_highest_pole_one "independent_actual_closed_boundary"
  emitProof `PFIndependentBoundary.m0_simple_pole_X8 "independent_actual_closed_boundary"
  emitProof `PFIndependentBoundary.m0_regular_simple_PF "independent_actual_closed_boundary"
  emitProof `PFIndependentBoundary.two_pole_one "independent_actual_closed_boundary"
  emitProof `solution "independent_actual_solution"
  compareType `solution `PFIndependentExpected.expected_global
  emitInternalHelpers [`Definitions.Def_ZetaNine_HarmonicStability, `Definitions.Def_ZetaNine_CoefficientMap, `Definitions.Def_ZetaNine_CoefficientMapJet, `Definitions.Def_ZetaNine_CoefficientMapInjectivity, `Definitions.Def_ZetaNine_CoefficientMapPartialFractions, `Definitions.Def_ZetaNine_CoefficientMapNumeratorPF, `Solutions.Sol_ZetaNine_CoefficientMapNumeratorPF_global]
