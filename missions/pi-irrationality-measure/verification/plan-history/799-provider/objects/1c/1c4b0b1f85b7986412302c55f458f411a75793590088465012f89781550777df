import OAI.NumberTheory.PiExponent.ProjectImports
import OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder
import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.RamificationInertia.Basic

namespace OAI

noncomputable section
open scoped BigOperators Polynomial nonZeroDivisors

namespace PiExponent.CurveZeroPole

private theorem transcendental_ne_zero {F E : Type*} [Field F] [Field E]
    [Algebra F E] {f : E} (hf : Transcendental F f) : f ≠ 0 := by
  intro h
  apply hf
  rw [h]
  exact isAlgebraic_zero

def fiberDegree {R : Type*} [CommRing R] (S : Type*) [CommRing S]
    [Algebra R S] [Algebra.QuasiFinite R S] (p : Ideal R) : ℕ :=
  let := (Algebra.QuasiFinite.finite_primesOver (R := R) (S := S) p).fintype
  ∑ q : p.primesOver S, q.1.ramificationIdx R * q.1.inertiaDeg R

theorem fiberDegree_eq_rank {R : Type*} [CommRing R] [IsDomain R]
    (S : Type*) [CommRing S] [Algebra R S]
    [Module.Finite R S] [Module.Flat R S]
    (p : Ideal R) [p.IsPrime] :
    fiberDegree S p = Module.finrank R S := by
  let := (Algebra.QuasiFinite.finite_primesOver (R := R) (S := S) p).fintype
  exact Ideal.sum_ramification_inertia_eq_finrank p S

theorem fiberDegree_eq_fractionField_rank
    (R K S L : Type*) [CommRing R] [IsDomain R] [Field K]
    [CommRing S] [Field L] [Algebra R S] [Algebra K L]
    [Algebra R K] [Algebra S L] [Algebra R L]
    [IsScalarTower R K L] [IsScalarTower R S L]
    [IsFractionRing R K] [IsFractionRing S L]
    [Module.Finite R S] [Module.Flat R S]
    (p : Ideal R) [p.IsPrime] :
    fiberDegree S p = Module.finrank K L := by
  rw [fiberDegree_eq_rank, IsFractionRing.finrank_eq R K S L]

theorem functionField_fiberDegree
    (F E : Type*) [Field F] [Field E]
    [Algebra F[X] E] [Algebra (RatFunc F) E]
    [IsScalarTower F[X] (RatFunc F) E]
    [FunctionField F E] [Algebra.IsSeparable (RatFunc F) E]
    (p : Ideal F[X]) [p.IsPrime] :
    fiberDegree (FunctionField.ringOfIntegers F E) p =
      Module.finrank (RatFunc F) E := by
  let : Module.IsTorsionFree F[X] (FunctionField.ringOfIntegers F E) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  exact fiberDegree_eq_fractionField_rank F[X] (RatFunc F)
    (FunctionField.ringOfIntegers F E) E p

theorem adjoin_inverse_eq {F E : Type*} [Field F] [Field E] [Algebra F E] (f : E) :
    IntermediateField.adjoin F {f⁻¹} = IntermediateField.adjoin F {f} := by
  apply le_antisymm
  · exact IntermediateField.adjoin_simple_le_iff.mpr
      (IntermediateField.inv_mem _ (IntermediateField.subset_adjoin F {f} (by simp)))
  · apply IntermediateField.adjoin_simple_le_iff.mpr
    simpa using IntermediateField.inv_mem (IntermediateField.adjoin F {f⁻¹})
      (show f⁻¹ ∈ IntermediateField.adjoin F {f⁻¹} from
        IntermediateField.subset_adjoin F {f⁻¹} (Set.mem_singleton _))

theorem parameter_inverse_degree_eq
    {F E : Type*} [Field F] [Field E] [Algebra F E] (f : E) :
    Module.finrank (IntermediateField.adjoin F {f⁻¹}) E =
      Module.finrank (IntermediateField.adjoin F {f}) E := by
  rw [adjoin_inverse_eq]

def parameterEmbedding {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) : RatFunc F →ₐ[F] E :=
  (IntermediateField.val (IntermediateField.adjoin F {f})).comp
    (RatFunc.algEquivOfTranscendental f hf).toAlgHom

@[simp] theorem parameterEmbedding_X {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) : parameterEmbedding f hf RatFunc.X = f := by
  simp [parameterEmbedding]

abbrev parameterAlgebra {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) : Algebra (RatFunc F) E :=
  (parameterEmbedding f hf).toRingHom.toAlgebra

theorem parameter_finrank {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) :
    let := parameterAlgebra f hf
    Module.finrank (RatFunc F) E = Module.finrank (IntermediateField.adjoin F {f}) E := by
  let := parameterAlgebra f hf
  apply Algebra.finrank_eq_of_equiv_equiv
    (RatFunc.algEquivOfTranscendental f hf).toRingEquiv (RingEquiv.refl E)
  rfl

theorem parameter_finite {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    let := parameterAlgebra f hf
    FiniteDimensional (RatFunc F) E := by
  let := parameterAlgebra f hf
  let e := RatFunc.algEquivOfTranscendental f hf
  let b := Module.finBasis (IntermediateField.adjoin F {f}) E
  apply (b.mapCoeffs e.symm.toRingEquiv ?_).finiteDimensional_of_finite
  intro c x
  change (↑(e (e.symm c)) : E) * x = (c : E) * x
  rw [e.apply_symm_apply]

abbrev parameterPolynomialAlgebra {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) : Algebra F[X] E :=
  ((parameterEmbedding f hf).toRingHom.comp (algebraMap F[X] (RatFunc F))).toAlgebra

theorem parameter_scalarTower {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) :
    let := parameterAlgebra f hf
    let := parameterPolynomialAlgebra f hf
    IsScalarTower F[X] (RatFunc F) E := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  apply IsScalarTower.of_algebraMap_eq
  intro x
  rfl

def zeroPrime (F : Type*) [Field F] : Ideal F[X] :=
  RingHom.ker Polynomial.constantCoeff

instance zeroPrime_isPrime (F : Type*) [Field F] : (zeroPrime F).IsPrime :=
  RingHom.ker_isPrime Polynomial.constantCoeff

theorem zeroPrime_eq_span_X (F : Type*) [Field F] :
    zeroPrime F = Ideal.span {Polynomial.X} := Polynomial.ker_constantCoeff

def parameterFiberDegree {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] : ℕ :=
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  fiberDegree (FunctionField.ringOfIntegers F E) (zeroPrime F)

theorem parameterFiberDegree_eq {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    parameterFiberDegree f hf = Module.finrank (IntermediateField.adjoin F {f}) E := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  change fiberDegree (FunctionField.ringOfIntegers F E) (zeroPrime F) = _
  rw [functionField_fiberDegree]
  exact parameter_finrank f hf

theorem transcendental_inverse {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) : Transcendental F f⁻¹ := by
  simpa only [Transcendental, IsAlgebraic.inv_iff] using hf

theorem zero_infinity_fiberDegree_eq
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    letI : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
      (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
    parameterFiberDegree f hf = parameterFiberDegree f⁻¹ (transcendental_inverse f hf) := by
  let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
    (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
  rw [parameterFiberDegree_eq, parameterFiberDegree_eq, parameter_inverse_degree_eq]

theorem constantCoeff_surjective (F : Type*) [Field F] :
    Function.Surjective (Polynomial.constantCoeff : F[X] →+* F) := by
  intro x
  exact ⟨Polynomial.C x, by simp⟩

instance zeroPrime_isMaximal (F : Type*) [Field F] : (zeroPrime F).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective Polynomial.constantCoeff (constantCoeff_surjective F)

def zeroPrimeQuotientEquiv (F : Type*) [Field F] : (F[X] ⧸ zeroPrime F) ≃+* F :=
  RingHom.quotientKerEquivOfSurjective (constantCoeff_surjective F)

theorem zeroFiber_inertiaDeg_eq_one (F S : Type*) [Field F] [IsAlgClosed F]
    [CommRing S] [Algebra F[X] S] [Module.Finite F[X] S]
    (q : Ideal S) [q.IsPrime] [q.LiesOver (zeroPrime F)] :
    q.inertiaDeg F[X] = 1 := by
  have : q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal q (zeroPrime F)
  let : Field (F[X] ⧸ zeroPrime F) := Ideal.Quotient.field _
  let : Field (S ⧸ q) := Ideal.Quotient.field _
  let : IsAlgClosed (F[X] ⧸ zeroPrime F) :=
    IsAlgClosed.of_ringEquiv F _ (zeroPrimeQuotientEquiv F).symm
  rw [Ideal.inertiaDeg_eq_of_isMaximal (zeroPrime F) q]
  apply Module.finrank_of_bijective_algebraMap
  apply IsAlgClosed.algebraMap_bijective_of_isIntegral

def zeroFiberLength (F S : Type*) [Field F] [CommRing S]
    [Algebra F[X] S] [Module.Finite F[X] S] : ℕ :=
  let := (Algebra.QuasiFinite.finite_primesOver (R := F[X]) (S := S) (zeroPrime F)).fintype
  ∑ q : (zeroPrime F).primesOver S,
    (Module.length (Localization.AtPrime q.1)
      ((Localization.AtPrime q.1) ⧸
        Ideal.span {algebraMap F[X] (Localization.AtPrime q.1) Polynomial.X})).toNat

theorem zeroFiberLength_eq_fiberDegree (F S : Type*) [Field F] [IsAlgClosed F]
    [CommRing S] [Algebra F[X] S] [Module.Finite F[X] S] :
    zeroFiberLength F S = fiberDegree S (zeroPrime F) := by
  unfold zeroFiberLength fiberDegree
  apply Finset.sum_congr rfl
  intro q _
  rw [zeroFiber_inertiaDeg_eq_one F S q.1, mul_one,
    Ideal.ramificationIdx_eq (zeroPrime F) q.1]
  have hm : (zeroPrime F).map (algebraMap F[X] (Localization.AtPrime q.1)) =
      Ideal.span {algebraMap F[X] (Localization.AtPrime q.1) Polynomial.X} := by
    calc
      _ = (Ideal.span {Polynomial.X}).map
          (algebraMap F[X] (Localization.AtPrime q.1)) :=
        congrArg (Ideal.map (algebraMap F[X] (Localization.AtPrime q.1))) (zeroPrime_eq_span_X F)
      _ = _ := by rw [Ideal.map_span, Set.image_singleton]
  exact congrArg (fun I : Ideal (Localization.AtPrime q.1) =>
    (Module.length (Localization.AtPrime q.1) ((Localization.AtPrime q.1) ⧸ I)).toNat) hm.symm

def parameterZeroLength {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] : ℕ :=
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  zeroFiberLength F (FunctionField.ringOfIntegers F E)

theorem parameterZeroLength_eq_degree
    {F E : Type*} [Field F] [CharZero F] [IsAlgClosed F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    parameterZeroLength f hf = Module.finrank (IntermediateField.adjoin F {f}) E := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  change zeroFiberLength F (FunctionField.ringOfIntegers F E) = _
  rw [zeroFiberLength_eq_fiberDegree]
  exact parameterFiberDegree_eq f hf

theorem zero_pole_length_eq
    {F E : Type*} [Field F] [CharZero F] [IsAlgClosed F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    letI : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
      (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
    parameterZeroLength f hf = parameterZeroLength f⁻¹ (transcendental_inverse f hf) := by
  let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
    (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
  rw [parameterZeroLength_eq_degree, parameterZeroLength_eq_degree, parameter_inverse_degree_eq]

def primeFieldValuation (S E : Type*) [CommRing S] [IsDedekindDomain S]
    [Field E] [Algebra S E] [IsFractionRing S E]
    (q : IsDedekindDomain.HeightOneSpectrum S) : AddValuation E (WithTop ℤ) :=
  let A := Localization.AtPrime q.asIdeal
  let := IsLocalization.localizationAlgebraOfSubmonoidLe A E
    q.asIdeal.primeCompl S⁰ q.asIdeal.primeCompl_le_nonZeroDivisors
  let := IsLocalization.localization_isScalarTower_of_submonoid_le A E
    q.asIdeal.primeCompl S⁰ q.asIdeal.primeCompl_le_nonZeroDivisors
  let := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.asIdeal.primeCompl A E
  let := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S q.ne_bot A
  CurveLocalOrder.fractionAddValuation A E

theorem primeFieldValuation_algebraMap
    (S E : Type*) [CommRing S] [IsDedekindDomain S]
    [Field E] [Algebra S E] [IsFractionRing S E]
    (q : IsDedekindDomain.HeightOneSpectrum S) (a : S) (ha : a ≠ 0) :
    primeFieldValuation S E q (algebraMap S E a) =
      CurveLocalOrder.enatToIntegerOrder
        (Module.length (Localization.AtPrime q.asIdeal)
          ((Localization.AtPrime q.asIdeal) ⧸
            Ideal.span {algebraMap S (Localization.AtPrime q.asIdeal) a})) := by
  let A := Localization.AtPrime q.asIdeal
  let := IsLocalization.localizationAlgebraOfSubmonoidLe A E
    q.asIdeal.primeCompl S⁰ q.asIdeal.primeCompl_le_nonZeroDivisors
  let := IsLocalization.localization_isScalarTower_of_submonoid_le A E
    q.asIdeal.primeCompl S⁰ q.asIdeal.primeCompl_le_nonZeroDivisors
  let := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.asIdeal.primeCompl A E
  let := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S q.ne_bot A
  change CurveLocalOrder.fractionAddValuation A E (algebraMap S E a) = _
  rw [IsScalarTower.algebraMap_apply S A E]
  apply CurveLocalOrder.fraction_order_eq_principal_colength
  exact (map_ne_zero_iff _ (IsLocalization.injective A
    q.asIdeal.primeCompl_le_nonZeroDivisors)).mpr ha

theorem primeField_integerOrder_algebraMap
    (S E : Type*) [CommRing S] [IsDedekindDomain S]
    [Field E] [Algebra S E] [IsFractionRing S E]
    (q : IsDedekindDomain.HeightOneSpectrum S) (a : S) (ha : a ≠ 0) :
    WeightedCurveDegree.integerOrder (primeFieldValuation S E q)
      (Units.mk0 (algebraMap S E a) ((map_ne_zero_iff _ (IsFractionRing.injective S E)).mpr ha)) =
      ((Module.length (Localization.AtPrime q.asIdeal)
        ((Localization.AtPrime q.asIdeal) ⧸
          Ideal.span {algebraMap S (Localization.AtPrime q.asIdeal) a})).toNat : ℤ) := by
  let A := Localization.AtPrime q.asIdeal
  let := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S q.ne_bot A
  have ha' : algebraMap S A a ≠ 0 :=
    (map_ne_zero_iff _ (IsLocalization.injective A
      q.asIdeal.primeCompl_le_nonZeroDivisors)).mpr ha
  apply WithTop.coe_injective
  rw [WeightedCurveDegree.coe_integerOrder]
  change primeFieldValuation S E q (algebraMap S E a) = _
  rw [primeFieldValuation_algebraMap S E q a ha]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp
    (CurveLocalOrder.principal_colength_ne_top ha')
  change CurveLocalOrder.enatToIntegerOrder
    (Module.length A (A ⧸ Ideal.span {algebraMap S A a})) = _
  rw [← hn]
  simp

theorem zeroPrime_ne_bot (F : Type*) [Field F] : zeroPrime F ≠ ⊥ := by
  intro h
  have hx : Polynomial.X ∈ zeroPrime F := by
    change Polynomial.constantCoeff Polynomial.X = (0 : F)
    simp
  rw [h, Ideal.mem_bot] at hx
  exact Polynomial.X_ne_zero hx

def zeroFiberHeightOne (F S : Type*) [Field F] [CommRing S] [IsDomain S]
    [Algebra F[X] S] [FaithfulSMul F[X] S]
    (q : (zeroPrime F).primesOver S) : IsDedekindDomain.HeightOneSpectrum S :=
  ⟨q.1, q.2.1, Ideal.ne_bot_of_mem_primesOver (zeroPrime_ne_bot F) q.2⟩

theorem baseParameter_nonzero (F S E : Type*) [Field F] [CommRing S] [IsDomain S]
    [Field E] [Algebra F[X] S] [FaithfulSMul F[X] S]
    [Algebra S E] [IsFractionRing S E] [Algebra F[X] E] [IsScalarTower F[X] S E] :
    algebraMap F[X] E Polynomial.X ≠ 0 := by
  rw [IsScalarTower.algebraMap_apply F[X] S E]
  exact (map_ne_zero_iff _ (IsFractionRing.injective S E)).mpr
    ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective F[X] S)).mpr Polynomial.X_ne_zero)

def zeroFiberIntegerOrderSum (F S E : Type*) [Field F] [CommRing S]
    [IsDedekindDomain S] [Field E] [Algebra F[X] S] [FaithfulSMul F[X] S]
    [Module.Finite F[X] S] [Algebra S E] [IsFractionRing S E]
    [Algebra F[X] E] [IsScalarTower F[X] S E] : ℤ :=
  let := (Algebra.QuasiFinite.finite_primesOver (R := F[X]) (S := S) (zeroPrime F)).fintype
  ∑ q : (zeroPrime F).primesOver S,
    WeightedCurveDegree.integerOrder (primeFieldValuation S E (zeroFiberHeightOne F S q))
      (Units.mk0 (algebraMap F[X] E Polynomial.X) (baseParameter_nonzero F S E))

theorem zeroFiberIntegerOrderSum_eq_length (F S E : Type*) [Field F] [CommRing S]
    [IsDedekindDomain S] [Field E] [Algebra F[X] S] [FaithfulSMul F[X] S]
    [Module.Finite F[X] S] [Algebra S E] [IsFractionRing S E]
    [Algebra F[X] E] [IsScalarTower F[X] S E] :
    zeroFiberIntegerOrderSum F S E = (zeroFiberLength F S : ℤ) := by
  unfold zeroFiberIntegerOrderSum zeroFiberLength
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro q _
  have hx : algebraMap F[X] S Polynomial.X ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective F[X] S)).mpr Polynomial.X_ne_zero
  have he := primeField_integerOrder_algebraMap S E
    (zeroFiberHeightOne F S q) (algebraMap F[X] S Polynomial.X) hx
  calc
    _ = WeightedCurveDegree.integerOrder
        (primeFieldValuation S E (zeroFiberHeightOne F S q))
        (Units.mk0 (algebraMap S E (algebraMap F[X] S Polynomial.X))
          ((map_ne_zero_iff _ (IsFractionRing.injective S E)).mpr hx)) := by
      congr 1
      ext
      exact IsScalarTower.algebraMap_apply F[X] S E Polynomial.X
    _ = _ := he
    _ = _ := by
      let A := Localization.AtPrime q.1
      have hi : Ideal.span {algebraMap S A (algebraMap F[X] S Polynomial.X)} =
          Ideal.span {algebraMap F[X] A Polynomial.X} :=
        congrArg (fun z : A => Ideal.span {z})
          (IsScalarTower.algebraMap_apply F[X] S A Polynomial.X).symm
      exact congrArg (fun I : Ideal A => ((Module.length A (A ⧸ I)).toNat : ℤ)) hi

def parameterZeroOrder {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] : ℤ :=
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let : Module.IsTorsionFree F[X] (FunctionField.ringOfIntegers F E) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  zeroFiberIntegerOrderSum F (FunctionField.ringOfIntegers F E) E

theorem parameterZeroOrder_eq_length
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    parameterZeroOrder f hf = (parameterZeroLength f hf : ℤ) := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let : Module.IsTorsionFree F[X] (FunctionField.ringOfIntegers F E) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  exact zeroFiberIntegerOrderSum_eq_length F (FunctionField.ringOfIntegers F E) E

theorem zero_pole_order_eq
    {F E : Type*} [Field F] [CharZero F] [IsAlgClosed F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    letI : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
      (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
    parameterZeroOrder f hf = parameterZeroOrder f⁻¹ (transcendental_inverse f hf) := by
  let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
    (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
  rw [parameterZeroOrder_eq_length, parameterZeroOrder_eq_length, zero_pole_length_eq]

abbrev parameterChart {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) : Type _ :=
  let := parameterPolynomialAlgebra f hf
  FunctionField.ringOfIntegers F E

abbrev parameterZeroPlaces {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) : Type _ :=
  let := parameterPolynomialAlgebra f hf
  (zeroPrime F).primesOver (parameterChart f hf)

abbrev parameterZeroPlacesFintype
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    Fintype (parameterZeroPlaces f hf) :=
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  (Algebra.QuasiFinite.finite_primesOver
    (R := F[X]) (S := FunctionField.ringOfIntegers F E) (zeroPrime F)).fintype

def parameterPlaceValuation
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : parameterZeroPlaces f hf) : AddValuation E (WithTop ℤ) :=
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let : Module.IsTorsionFree F[X] (FunctionField.ringOfIntegers F E) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  primeFieldValuation (parameterChart f hf) E
    (zeroFiberHeightOne F (parameterChart f hf) q)

theorem parameterPolynomialAlgebra_map
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : F[X]) :
    letI := parameterPolynomialAlgebra f hf
    algebraMap F[X] E p = Polynomial.aeval f p := by
  let := parameterPolynomialAlgebra f hf
  change parameterEmbedding f hf (algebraMap F[X] (RatFunc F) p) = Polynomial.aeval f p
  change (↑(RatFunc.algEquivOfTranscendental f hf (algebraMap F[X] (RatFunc F) p)) : E) = _
  rw [RatFunc.algEquivOfTranscendental_algebraMap]
  exact IntermediateField.AdjoinSimple.coe_aeval_gen_apply F f p

theorem parameterZeroOrder_eq_sum
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    letI := parameterZeroPlacesFintype f hf
    parameterZeroOrder f hf =
      ∑ q : parameterZeroPlaces f hf,
        WeightedCurveDegree.integerOrder (parameterPlaceValuation f hf q)
          (Units.mk0 f (transcendental_ne_zero hf)) := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let : Module.IsTorsionFree F[X] (FunctionField.ringOfIntegers F E) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  dsimp only [parameterZeroOrder, zeroFiberIntegerOrderSum, parameterPlaceValuation]
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  ext
  change parameterEmbedding f hf RatFunc.X = f
  exact parameterEmbedding_X f hf

private theorem sum_integerOrder_inverse {ι K : Type*} [Fintype ι] [Field K]
    (v : ι → AddValuation K (WithTop ℤ)) (x : Kˣ) :
    (∑ i, WeightedCurveDegree.integerOrder (v i) x⁻¹) =
      -(∑ i, WeightedCurveDegree.integerOrder (v i) x) := by
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => WeightedCurveDegree.integerOrder_inv (v i) x

private theorem parameterZeroOrder_eq_sum_fintype
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (g : E) (hg : Transcendental F g)
    [FiniteDimensional (IntermediateField.adjoin F {g}) E]
    [hplaces : Fintype (parameterZeroPlaces g hg)] :
    parameterZeroOrder g hg =
      ∑ q : parameterZeroPlaces g hg,
        WeightedCurveDegree.integerOrder (parameterPlaceValuation g hg q)
          (Units.mk0 g (transcendental_ne_zero hg)) := by
  have h : hplaces = parameterZeroPlacesFintype g hg := Subsingleton.elim _ _
  cases h
  exact parameterZeroOrder_eq_sum g hg

private theorem parameterPlaceSum_inverse
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (g : E) (hg : Transcendental F g)
    [FiniteDimensional (IntermediateField.adjoin F {g}) E]
    [Fintype (parameterZeroPlaces g hg)] :
    (∑ q : parameterZeroPlaces g hg,
      WeightedCurveDegree.integerOrder
        (parameterPlaceValuation g hg q)
        (Units.mk0 g (transcendental_ne_zero hg))⁻¹) = -parameterZeroOrder g hg := by
  have hs := sum_integerOrder_inverse
    (fun q : parameterZeroPlaces g hg => parameterPlaceValuation g hg q)
    (Units.mk0 g (transcendental_ne_zero hg))
  have he := parameterZeroOrder_eq_sum_fintype g hg
  exact hs.trans (congrArg (fun z : ℤ => -z) he.symm)

private theorem inverseParameter_finite
    {F E : Type*} [Field F] [Field E] [Algebra F E] (f : E)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
  (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance

private theorem zeroPoleOrder_eq_of_finite
    {F E : Type*} [Field F] [CharZero F] [IsAlgClosed F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    [FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E] :
    parameterZeroOrder f hf = parameterZeroOrder f⁻¹ (transcendental_inverse f hf) := by
  rw [parameterZeroOrder_eq_length, parameterZeroOrder_eq_length,
    parameterZeroLength_eq_degree, parameterZeroLength_eq_degree, parameter_inverse_degree_eq]

private theorem sum_zero_and_pole_orders_of_order_eq
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    [FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E]
    [Fintype (parameterZeroPlaces f hf)]
    [Fintype (parameterZeroPlaces f⁻¹ (transcendental_inverse f hf))]
    (heq : parameterZeroOrder f hf = parameterZeroOrder f⁻¹ (transcendental_inverse f hf)) :
    (∑ q : parameterZeroPlaces f hf,
      WeightedCurveDegree.integerOrder (parameterPlaceValuation f hf q)
        (Units.mk0 f (transcendental_ne_zero hf))) +
    (∑ q : parameterZeroPlaces f⁻¹ (transcendental_inverse f hf),
      WeightedCurveDegree.integerOrder
        (parameterPlaceValuation f⁻¹ (transcendental_inverse f hf) q)
        (Units.mk0 f (transcendental_ne_zero hf))) = 0 := by
  have hinv : (Units.mk0 f (transcendental_ne_zero hf) : Eˣ) =
      (Units.mk0 f⁻¹ (transcendental_ne_zero (transcendental_inverse f hf)))⁻¹ := by
    ext
    simp
  have hi := (congrArg (fun x : Eˣ =>
    ∑ q : parameterZeroPlaces f⁻¹ (transcendental_inverse f hf),
      WeightedCurveDegree.integerOrder
        (parameterPlaceValuation f⁻¹ (transcendental_inverse f hf) q) x) hinv).trans
    (parameterPlaceSum_inverse f⁻¹ (transcendental_inverse f hf))
  have hz := (parameterZeroOrder_eq_sum_fintype f hf).symm
  exact (congrArg₂ (fun a b : ℤ => a + b) hz hi).trans
    ((congrArg (fun z : ℤ => parameterZeroOrder f hf + -z) heq.symm).trans (add_neg_cancel _))

theorem sum_zero_and_pole_orders_eq_zero
    {F E : Type*} [Field F] [CharZero F] [IsAlgClosed F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    letI : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
      inverseParameter_finite (F := F) f
    letI := parameterZeroPlacesFintype f hf
    letI := parameterZeroPlacesFintype f⁻¹ (transcendental_inverse f hf)
    (∑ q : parameterZeroPlaces f hf,
      WeightedCurveDegree.integerOrder (parameterPlaceValuation f hf q)
        (Units.mk0 f (transcendental_ne_zero hf))) +
    (∑ q : parameterZeroPlaces f⁻¹ (transcendental_inverse f hf),
      WeightedCurveDegree.integerOrder
        (parameterPlaceValuation f⁻¹ (transcendental_inverse f hf) q)
        (Units.mk0 f (transcendental_ne_zero hf))) = 0 := by
  let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
    inverseParameter_finite (F := F) f
  let := parameterZeroPlacesFintype f hf
  let := parameterZeroPlacesFintype f⁻¹ (transcendental_inverse f hf)
  exact sum_zero_and_pole_orders_of_order_eq f hf (zeroPoleOrder_eq_of_finite f hf)

end PiExponent.CurveZeroPole

end

end OAI
