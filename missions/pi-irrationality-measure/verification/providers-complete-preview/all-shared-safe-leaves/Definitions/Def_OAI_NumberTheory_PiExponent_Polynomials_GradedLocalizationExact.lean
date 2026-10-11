import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.Algebra.Field.Equiv
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.Algebra.Module.SnakeLemma
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Eval.Subring
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Regular.Defs
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Rat
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Finsupp.SMulWithZero
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Card
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.DirectSum.Finite
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Logic.Equiv.Sum
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Order.Minimal
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.LocalRing
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.MvPowerSeries.Derivative
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.MvPowerSeries.Order
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Trace.Defs
import Mathlib.SetTheory.Cardinal.ToNat
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Conv
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas

namespace OAI

namespace PiExponent.GradedLocalizationExact

noncomputable section

variable {R M N P σR σM σN σP : Type*}
  [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
  [SetLike σR R]
  [SetLike σM M] [AddSubgroupClass σM M]
  [SetLike σN N] [AddSubgroupClass σN N]
  [SetLike σP P] [AddSubgroupClass σP P]

def powerDenominator (a : R) (n : ℕ) : Submonoid.powers a :=
  ⟨a ^ n, ⟨n, rfl⟩⟩

@[simp] theorem powerDenominator_val (a : R) (n : ℕ) :
    (powerDenominator a n : R) = a ^ n := rfl

@[simp] theorem powerDenominator_zero (a : R) : powerDenominator a 0 = 1 := by
  apply Subtype.ext
  simp [powerDenominator]

theorem powerDenominator_add (a : R) (n k : ℕ) :
    powerDenominator a (n + k) = powerDenominator a n * powerDenominator a k := by
  apply Subtype.ext
  exact pow_add a n k

def fraction (a : R) (m : M) (n : ℕ) : LocalizedModule (Submonoid.powers a) M :=
  LocalizedModule.mk m (powerDenominator a n)

@[simp] theorem fraction_zero (a : R) (n : ℕ) : fraction a (0 : M) n = 0 :=
  LocalizedModule.zero_mk _

@[simp] theorem fraction_neg (a : R) (m : M) (n : ℕ) :
    fraction a (-m) n = -fraction a m n := LocalizedModule.mk_neg

theorem fraction_add (a : R) (m m' : M) (n k : ℕ) :
    fraction a m n + fraction a m' k =
      fraction a (a ^ k • m + a ^ n • m') (n + k) := by
  simp only [fraction, powerDenominator_add, LocalizedModule.mk_add_mk,
    Submonoid.smul_def, powerDenominator_val]

theorem fraction_cancel (a : R) (m : M) (n k : ℕ) :
    fraction a (a ^ k • m) (n + k) = fraction a m n := by
  simpa only [fraction, powerDenominator_add, Submonoid.smul_def,
    powerDenominator_val] using
    LocalizedModule.mk_cancel_common_right (powerDenominator a n) (powerDenominator a k) m

theorem fraction_eq_zero (a : R) (m : M) (n : ℕ) :
    fraction a m n = 0 ↔ ∃ k : ℕ, a ^ k • m = 0 := by
  rw [← fraction_zero a 0, fraction, fraction, LocalizedModule.mk_eq]
  simp only [powerDenominator_zero, one_smul, smul_zero]
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨k, hk⟩ := s.property
    refine ⟨k, ?_⟩
    simpa only [Submonoid.smul_def, ← hk] using hs
  · rintro ⟨k, hk⟩
    exact ⟨powerDenominator a k, hk⟩

variable (𝒜 : ℤ → σR) (𝓜 : ℤ → σM)
  [SetLike.GradedMonoid 𝒜] [SetLike.GradedSMul 𝒜 𝓜]
  (a : R) (e : ℤ) (ha : a ∈ 𝒜 e)

omit [AddSubgroupClass σM M] in
include ha in
theorem power_smul_mem {d : ℤ} {m : M} (hm : m ∈ 𝓜 d) (n : ℕ) :
    a ^ n • m ∈ 𝓜 (d + (n : ℤ) * e) := by
  have h := SetLike.GradedSMul.smul_mem (SetLike.pow_mem_graded n ha) hm
  simpa only [nsmul_eq_mul, vadd_eq_add, add_comm] using h

def degreePiece (d : ℤ) : AddSubgroup (LocalizedModule (Submonoid.powers a) M) where
  carrier := {z | ∃ (n : ℕ) (m : M), m ∈ 𝓜 (d + (n : ℤ) * e) ∧ z = fraction a m n}
  zero_mem' := ⟨0, 0, zero_mem _, (fraction_zero a 0).symm⟩
  add_mem' := by
    rintro z z' ⟨n, m, hm, rfl⟩ ⟨k, m', hm', rfl⟩
    refine ⟨n + k, a ^ k • m + a ^ n • m', ?_, fraction_add a m m' n k⟩
    apply add_mem
    · have h := power_smul_mem 𝒜 𝓜 a e ha hm k
      convert h using 1
      push_cast
      ring_nf
    · have h := power_smul_mem 𝒜 𝓜 a e ha hm' n
      convert h using 1
      push_cast
      ring_nf
  neg_mem' := by
    rintro z ⟨n, m, hm, rfl⟩
    exact ⟨n, -m, neg_mem hm, (fraction_neg a m n).symm⟩



def localizedMap (f : M →ₗ[R] N) :
    LocalizedModule (Submonoid.powers a) M →ₗ[R] LocalizedModule (Submonoid.powers a) N :=
  IsLocalizedModule.map (Submonoid.powers a) (LocalizedModule.mkLinearMap _ M)
    (LocalizedModule.mkLinearMap _ N) f

@[simp] theorem localizedMap_fraction (f : M →ₗ[R] N) (m : M) (n : ℕ) :
    localizedMap a f (fraction a m n) = fraction a (f m) n :=
  IsLocalizedModule.map_LocalizedModules _ f m _

variable (𝓝 : ℤ → σN) [SetLike.GradedSMul 𝒜 𝓝]

def pieceMap (d : ℤ) (f : M →ₗ[R] N)
    (hf : ∀ i m, m ∈ 𝓜 i → f m ∈ 𝓝 i) :
    degreePiece 𝒜 𝓜 a e ha d →+ degreePiece 𝒜 𝓝 a e ha d where
  toFun z := ⟨localizedMap a f z.val, by
    obtain ⟨n, m, hm, hz⟩ := z.property
    refine ⟨n, f m, hf _ _ hm, ?_⟩
    rw [hz, localizedMap_fraction]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' z z' := Subtype.ext (map_add _ _ _)



section Decomposition
variable [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]

theorem preserves_of_compatible (f : M →ₗ[R] N)
    (hf : ∀ i x, f (DirectSum.decompose 𝓜 x i : M) =
      (DirectSum.decompose 𝓝 (f x) i : N)) :
    ∀ i m, m ∈ 𝓜 i → f m ∈ 𝓝 i := by
  intro i m hm
  have h := hf i m
  rw [DirectSum.decompose_of_mem_same 𝓜 hm] at h
  exact h.symm ▸ (DirectSum.decompose 𝓝 (f m) i).property

theorem homogeneous_preimage (f : M →ₗ[R] N)
    (hf : ∀ i x, f (DirectSum.decompose 𝓜 x i : M) =
      (DirectSum.decompose 𝓝 (f x) i : N))
    {d : ℤ} {y : N} (hy : y ∈ 𝓝 d) (hrange : y ∈ LinearMap.range f) :
    ∃ x : M, x ∈ 𝓜 d ∧ f x = y := by
  obtain ⟨x, hx⟩ := hrange
  refine ⟨DirectSum.decompose 𝓜 x d, (DirectSum.decompose 𝓜 x d).property, ?_⟩
  rw [hf, hx, DirectSum.decompose_of_mem_same 𝓝 hy]

theorem pieceMap_surjective (d : ℤ) (f : M →ₗ[R] N)
    (hf : ∀ i x, f (DirectSum.decompose 𝓜 x i : M) =
      (DirectSum.decompose 𝓝 (f x) i : N)) (hsurj : Function.Surjective f) :
    Function.Surjective
      (pieceMap 𝒜 𝓜 a e ha 𝓝 d f (preserves_of_compatible 𝓜 𝓝 f hf)) := by
  intro z
  obtain ⟨n, y, hy, hz⟩ := z.property
  obtain ⟨x, hx, hxy⟩ := homogeneous_preimage 𝓜 𝓝 f hf hy (hsurj y)
  refine ⟨⟨fraction a x n, n, x, hx, rfl⟩, ?_⟩
  apply Subtype.ext
  change localizedMap a f (fraction a x n) = z.val
  rw [localizedMap_fraction, hxy, ← hz]

variable (𝓟 : ℤ → σP) [SetLike.GradedSMul 𝒜 𝓟] [DirectSum.Decomposition 𝓟]

theorem pieceMap_exact (d : ℤ) (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : ∀ i x, f (DirectSum.decompose 𝓜 x i : M) =
      (DirectSum.decompose 𝓝 (f x) i : N))
    (hg : ∀ i x, g (DirectSum.decompose 𝓝 x i : N) =
      (DirectSum.decompose 𝓟 (g x) i : P))
    (hex : Function.Exact f g) :
    Function.Exact
      (pieceMap 𝒜 𝓜 a e ha 𝓝 d f (preserves_of_compatible 𝓜 𝓝 f hf))
      (pieceMap 𝒜 𝓝 a e ha 𝓟 d g (preserves_of_compatible 𝓝 𝓟 g hg)) := by
  intro z
  constructor
  · intro hz
    obtain ⟨n, y, hy, hzy⟩ := z.property
    have hzero : localizedMap a g z.val = 0 := congrArg Subtype.val hz
    rw [hzy, localizedMap_fraction, fraction_eq_zero] at hzero
    obtain ⟨k, hk⟩ := hzero
    have hclear : g (a ^ k • y) = 0 := by rw [map_smul, hk]
    have hy' : a ^ k • y ∈ 𝓝 (d + ((n + k : ℕ) : ℤ) * e) := by
      have h := power_smul_mem 𝒜 𝓝 a e ha hy k
      convert h using 1
      push_cast
      ring_nf
    obtain ⟨x, hx, hxy⟩ := homogeneous_preimage 𝓜 𝓝 f hf hy' ((hex _).mp hclear)
    refine ⟨⟨fraction a x (n + k), n + k, x, hx, rfl⟩, ?_⟩
    apply Subtype.ext
    change localizedMap a f (fraction a x (n + k)) = z.val
    rw [localizedMap_fraction, hxy, fraction_cancel, ← hzy]
  · rintro ⟨x, rfl⟩
    apply Subtype.ext
    obtain ⟨n, y, hy, hxy⟩ := x.property
    change localizedMap a g (localizedMap a f x.val) = 0
    rw [hxy, localizedMap_fraction, localizedMap_fraction,
      hex.apply_apply_eq_zero, fraction_zero]

end Decomposition

section FinitePresentation
variable [AddSubgroupClass σR R] [DirectSum.Decomposition 𝒜] [DirectSum.Decomposition 𝓜]
  [IsNoetherianRing R] [Module.Finite R M]



end FinitePresentation

end
end PiExponent.GradedLocalizationExact

end OAI
