import Submission.ThreeSum.LocalCoverBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum.LocalCoverBounds

theorem solution (h : ℕ) (hh : 0 < h) :
    Nat.Prime (localPrime h) ∧ Odd (localPrime h) ∧
    outputCount (464*h) h * 2^(2*h) ≤ localPrime h^2 ∧
    localPrime h^2 ≤ 16*(outputCount (464*h) h * 2^(2*h)) ∧
    degree (464*h) h < localPrime h ∧ groupSize h < localPrime h ∧
    1/(16*(2*(h : ℝ)+1)) ≤ mean (464*h) h (localPrime h) ∧
    4*(localPrime h+vertexCount (464*h) h) ≤ localBucketCap h*localPrime h := by
  exact ⟨localPrime_prime h,localPrime_odd hh,localPrime_sq_lower h,
    localPrime_sq_upper h,degree_lt_localPrime hh,groupSize_lt_localPrime hh,
    localMean_lower h,localBucketCap_threshold h⟩

#print axioms solution
