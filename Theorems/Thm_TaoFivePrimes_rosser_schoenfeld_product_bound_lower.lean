import Mathlib

-- Local mirror of the published platform node
-- TaoFivePrimes.rosser_schoenfeld_product_bound_lower
-- (theorem id 537dc0ba-c00a-474d-ba93-8e76a6ea85f0, published 2026-09-27).
--
-- Rosser & Schoenfeld (1962), Illinois J. Math. 6, 64--94: the lower half of
-- their explicit Mertens product calculation,
--   e^gamma * log x < prod_{p <= floor x} p/(p-1)      for 2 <= x <= 10^8.
-- Quoted as eq. (1.1) of Lamzouri, arXiv:1410.3777. The range IS essential:
-- Diamond-Pintz (2009) proved the difference changes sign infinitely often.
namespace TaoFivePrimes

theorem rosser_schoenfeld_product_bound_lower (x : ℝ) (hx : 2 ≤ x) (hx' : x ≤ 10 ^ 8) :
    Real.exp Real.eulerMascheroniConstant * Real.log x <
      ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) := by sorry

end TaoFivePrimes
