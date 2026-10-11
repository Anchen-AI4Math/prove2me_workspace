import Mathlib

-- Unpublished local source placeholder; not a proved theorem.
-- Elementary (no PNT, no numerics, no external citation): with
-- T(N) = sum_{p<=N} (log(1-1/p)+1/p) and T(inf) the same series over all primes,
-- T(N) - T(inf) <= 1/N for x >= 2. Proved in
-- Solutions/Sol_TaoFivePrimes_mertens_tail_upper.lean.
namespace TaoFivePrimes

theorem mertens_tail_upper (x : ℝ) (hx : 2 ≤ x) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) ≤
      (∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) +
        1 / (⌊x⌋₊ : ℝ) := by sorry

end TaoFivePrimes
