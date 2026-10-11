import Definitions.Def_ZetaNine_HarmonicStability
import Definitions.Def_ZetaNine_HarmonicPrimeValuation
import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Tactic
open scoped BigOperators
open ZetaNine.HarmonicStability

set_option autoImplicit false

theorem ZetaNine.HarmonicStability.harmonic_finite_prime_product_dvd (s K N : ℕ) (S : Finset ℕ)
    (hs : 0 < s)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ N ∧ N / p ≤ K ∧ K < p ∧
      harmonicExceptionalProduct s K < p) :
    (∏ p ∈ S, p ^ s) ∣ (harmonicPower s N).den := by sorry
