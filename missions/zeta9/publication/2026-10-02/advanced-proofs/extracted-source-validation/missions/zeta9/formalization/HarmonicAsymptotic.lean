import missions.zeta9.formalization.HarmonicPrimeValuation
import Solutions.Sol_ZetaNine_HarmonicStability_harmonic_den_dvd_lcm_power
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# The actual harmonic denominator rate, conditional only on two PNT inputs

The fixed Mathlib revision supplies Chebyshev functions and elementary
bounds, but no theorem asserting their PNT asymptotics. We therefore keep
the two prime-distribution limits as explicit hypotheses. In particular,
the harmonic denominator baseline itself is never a hypothesis.

The finite prime interval is the real interval `(N/(K+1),N]`; the exceptional
cutoff is built from the actual reduced numerators of `H₁,…,H_K`.
-/

set_option autoImplicit false
open scoped BigOperators
open Filter

namespace ZetaNine.HarmonicStability

/-- Literal primes in `(N/(K+1),N]`, with a fixed floor-block cutoff `K`. -/
noncomputable def harmonicPrimeBlock (N K : ℕ) : Finset ℕ :=
  (Nat.primesLE N).filter (fun p => (N : ℝ) / (K + 1 : ℕ) < (p : ℝ))

theorem mem_harmonicPrimeBlock (N K p : ℕ) :
    p ∈ harmonicPrimeBlock N K ↔
      p ≤ N ∧ p.Prime ∧ N < (K + 1) * p := by
  simp only [harmonicPrimeBlock, Finset.mem_filter, Nat.mem_primesLE]
  have hK : (0 : ℝ) < (K + 1 : ℕ) := by positivity
  rw [div_lt_iff₀ hK]
  norm_cast
  simp only [mul_comm, and_assoc]

/-- The lower finite logarithmic sum is exactly a difference of the actual
Mathlib Chebyshev functions; no prime counting substitute is introduced. -/
theorem harmonicPrimeBlock_log_sum (N K : ℕ) :
    (∑ p ∈ harmonicPrimeBlock N K, Real.log (p : ℝ)) =
      Chebyshev.theta (N : ℝ) - Chebyshev.theta ((N : ℝ) / (K + 1 : ℕ)) := by
  classical
  have hK : (0 : ℝ) < (K + 1 : ℕ) := by positivity
  have hnonneg : 0 ≤ (N : ℝ) / (K + 1 : ℕ) := by positivity
  have hbound : (N : ℝ) / (K + 1 : ℕ) ≤ (N : ℝ) := by
    apply div_le_self (Nat.cast_nonneg N)
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le K)
  have hlow : (Nat.primesLE N).filter
      (fun p : ℕ => ¬ (N : ℝ) / (K + 1 : ℕ) < (p : ℝ)) =
        Nat.primesLE ⌊(N : ℝ) / (K + 1 : ℕ)⌋₊ := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesLE, not_lt]
    rw [Nat.le_floor_iff hnonneg]
    constructor
    · exact fun h => ⟨h.2, h.1.2⟩
    · intro h
      exact ⟨⟨by exact_mod_cast h.1.trans hbound, h.2⟩, h.1⟩
  have hsum := Finset.sum_filter_add_sum_filter_not (Nat.primesLE N)
    (fun p => (N : ℝ) / (K + 1 : ℕ) < (p : ℝ))
    (fun p => Real.log (p : ℝ))
  rw [hlow, ← Chebyshev.theta_eq_sum_primesLE,
    ← Chebyshev.theta_eq_sum_primesLE_log] at hsum
  exact eq_sub_iff_add_eq.mpr hsum

/-- An explicit endpoint after which every prime in the fixed interval is
beyond all actual finite exceptional numerator primes. -/
def harmonicPrimeBlockThreshold (s K : ℕ) : ℕ :=
  (K + 1) * (max K (harmonicExceptionalProduct s K) + 1)

theorem harmonicPrimeBlock_conditions (s K N p : ℕ)
    (hN : harmonicPrimeBlockThreshold s K ≤ N)
    (hp : p ∈ harmonicPrimeBlock N K) :
    p.Prime ∧ p ≤ N ∧ N / p ≤ K ∧ K < p ∧ harmonicExceptionalProduct s K < p := by
  obtain ⟨hpN, hprime, hblock⟩ := (mem_harmonicPrimeBlock N K p).mp hp
  have hlarge : max K (harmonicExceptionalProduct s K) < p := by
    by_contra hnot
    have hpbound : p ≤ max K (harmonicExceptionalProduct s K) := by omega
    have hmul := Nat.mul_le_mul_left (K + 1) hpbound
    unfold harmonicPrimeBlockThreshold at hN
    nlinarith
  refine ⟨hprime, hpN, ?_, lt_of_le_of_lt (le_max_left _ _) hlarge,
    lt_of_le_of_lt (le_max_right _ _) hlarge⟩
  exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hprime.pos).mpr hblock)

/-- Unconditional eventual lower bound for the actual reduced denominator,
with an explicit fixed exceptional cutoff and the literal prime interval. -/
theorem harmonic_log_den_lower_bound (s K N : ℕ) (hs : 0 < s)
    (hN : harmonicPrimeBlockThreshold s K ≤ N) :
    (s : ℝ) * (Chebyshev.theta (N : ℝ) -
      Chebyshev.theta ((N : ℝ) / (K + 1 : ℕ))) ≤ logDen (harmonicPower s N) := by
  rw [← harmonicPrimeBlock_log_sum]
  exact harmonic_finite_prime_log_lower_bound s K N (harmonicPrimeBlock N K) hs
    (fun p hp => harmonicPrimeBlock_conditions s K N p hN hp)

/-- The prime-number-theorem input for the actual first Chebyshev function.
It is a proposition supplied as an argument, not a declared axiom. -/
def ThetaPNT : Prop :=
  Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (nhds 1)

/-- The second PNT input, in the exact lcm form needed by the upper bound. -/
def LcmPNT : Prop :=
  Tendsto (fun N : ℕ => Real.log (Nat.lcmUpto N : ℝ) / (N : ℝ)) atTop (nhds 1)

private theorem theta_block_rate (K : ℕ) (hθ : ThetaPNT) :
    Tendsto (fun N : ℕ =>
      (Chebyshev.theta (N : ℝ) - Chebyshev.theta ((N : ℝ) / (K + 1 : ℕ))) /
        (N : ℝ)) atTop (nhds (1 - 1 / (K + 1 : ℕ))) := by
  have hK : (0 : ℝ) < (K + 1 : ℕ) := by positivity
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hscaled : Tendsto (fun N : ℕ => (N : ℝ) / (K + 1 : ℕ)) atTop atTop :=
    hnat.atTop_div_const hK
  have hcut := (hθ.comp hscaled).mul_const (1 / (K + 1 : ℕ) : ℝ)
  simp only [one_mul] at hcut
  have hcut' : Tendsto (fun N : ℕ =>
      Chebyshev.theta ((N : ℝ) / (K + 1 : ℕ)) / (N : ℝ))
        atTop (nhds (1 / (K + 1 : ℕ) : ℝ)) := by
    apply hcut.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hNz : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    dsimp only [Function.comp_def]
    field_simp
  convert (hθ.comp hnat).sub hcut' using 1
  ext N
  exact sub_div _ _ _

/-- The complete full-sequence baseline transfer: actual harmonic
denominators have rate `s`, conditional only on the stated two prime
distribution inputs. All arithmetic and exceptional-prime exclusions are
proved above, and there is no hypothesis about harmonic denominator growth. -/
theorem harmonic_log_den_rate_of_pnt (s : ℕ) (hs : 0 < s)
    (hθ : ThetaPNT) (hℓ : LcmPNT) :
    Tendsto (fun N : ℕ => logDen (harmonicPower s N) / (N : ℝ))
      atTop (nhds (s : ℝ)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hKlim : Tendsto (fun K : ℕ =>
        (s : ℝ) * (1 - 1 / (K + 1 : ℕ))) atTop (nhds (s : ℝ)) := by
      convert (tendsto_const_nhds (x := (s : ℝ))).mul
        ((tendsto_const_nhds (x := (1 : ℝ))).sub
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))) using 1 <;> simp
    obtain ⟨K, hKa⟩ := (hKlim.eventually (eventually_gt_nhds ha)).exists
    have hlowlim := (theta_block_rate K hθ).const_mul (s : ℝ)
    have hlowevent := hlowlim.eventually (eventually_gt_nhds hKa)
    filter_upwards [hlowevent, eventually_ge_atTop (harmonicPrimeBlockThreshold s K)]
      with N hlower hN
    have hbound := div_le_div_of_nonneg_right
      (harmonic_log_den_lower_bound s K N hs hN) (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    rw [mul_div_assoc] at hbound
    exact hlower.trans_le hbound
  · intro a ha
    have huplim := hℓ.const_mul (s : ℝ)
    have hupevent : ∀ᶠ N : ℕ in atTop,
        (s : ℝ) * (Real.log (Nat.lcmUpto N : ℝ) / (N : ℝ)) < a := by
      exact huplim.eventually (by simpa using eventually_lt_nhds ha)
    filter_upwards [hupevent] with N hupp
    have hbound := div_le_div_of_nonneg_right (harmonic_log_den_le_lcm s N)
      (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    rw [mul_div_assoc] at hbound
    exact hbound.trans_lt hupp

/-- The original actual-harmonic perturbation corollary now needs only the
two external PNT inputs and the perturbation's proved sublinear denominator
condition. The unperturbed baseline is derived, not postulated. -/
theorem harmonic_perturbed_log_den_rate_of_pnt (s : ℕ) (hs : 0 < s)
    (hθ : ThetaPNT) (hℓ : LcmPNT) (r : ℕ → ℚ)
    (hr : Tendsto (fun N => logDen (r N) / (N : ℝ)) atTop (nhds 0)) :
    Tendsto (fun N : ℕ => logDen (harmonicPower s N + r N) / (N : ℝ))
      atTop (nhds (s : ℝ)) := by
  exact harmonic_log_den_rate_stability s r (harmonic_log_den_rate_of_pnt s hs hθ hℓ) hr

/-- Positive integral reindexing, including the original `s=9,N=2M`
application. This is still the actual reduced harmonic denominator. -/
theorem harmonic_log_den_rate_nat_scale_of_pnt (s a : ℕ) (hs : 0 < s) (ha : 0 < a)
    (hθ : ThetaPNT) (hℓ : LcmPNT) :
    Tendsto (fun M : ℕ => logDen (harmonicPower s (a * M)) / (M : ℝ))
      atTop (nhds ((s : ℝ) * a)) := by
  have hindex : Tendsto (fun M : ℕ => a * M) atTop atTop := by
    apply tendsto_atTop_mono (fun M => Nat.le_mul_of_pos_left M ha) tendsto_id
  have hbase := ((harmonic_log_den_rate_of_pnt s hs hθ hℓ).comp hindex).mul_const (a : ℝ)
  apply hbase.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with M hM
  have hMz : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  have haz : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
  dsimp only [Function.comp_def]
  rw [Nat.cast_mul]
  field_simp

/-- The exact denominator rate used by the right-shifted Mellin route. -/
theorem harmonic_nine_double_log_den_rate_of_pnt (hθ : ThetaPNT) (hℓ : LcmPNT) :
    Tendsto (fun M : ℕ => logDen (harmonicPower 9 (2 * M)) / (M : ℝ))
      atTop (nhds 18) := by
  convert harmonic_log_den_rate_nat_scale_of_pnt 9 2 (by decide) (by decide) hθ hℓ using 1
  norm_num

#print axioms harmonicPrimeBlock_log_sum
#print axioms harmonicPrimeBlock_conditions
#print axioms harmonic_log_den_lower_bound
#print axioms harmonic_log_den_rate_of_pnt
#print axioms harmonic_perturbed_log_den_rate_of_pnt
#print axioms harmonic_log_den_rate_nat_scale_of_pnt
#print axioms harmonic_nine_double_log_den_rate_of_pnt

end ZetaNine.HarmonicStability
