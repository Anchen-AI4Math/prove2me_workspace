import Definitions.Def_ZetaNine_HarmonicStability
import Definitions.Def_ZetaNine_HarmonicPrimeValuation
import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Tactic
open scoped BigOperators
open ZetaNine.HarmonicStability

set_option autoImplicit false

theorem ZetaNine.HarmonicStability.harmonic_large_prime_den_valuation (s N p : ℕ) (hp : p.Prime)
    (hs : 0 < s) (hNp : p ≤ N) (hN : N < p ^ 2)
    (hunit : ¬ p ∣ (harmonicPower s (N / p)).num.natAbs) :
    padicValNat p (harmonicPower s N).den = s := by sorry
