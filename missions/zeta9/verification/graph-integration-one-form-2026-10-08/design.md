# Concrete one-form graph branch, 2026-10-08

This is SOURCE and a mathematical integration design. No Lean compiler,
platform API or credentials were used. No shared modules, scope or current
documents were changed. The proposed Open contract is not a small-forms
restatement: it requires the actual inverse image of an integer selected
output to lie in an explicit Taylor cone and satisfy the genuine coefficient
height margin.

## Existing parent and actual objects

The target parent is `60c1cf49-6b01-448c-b38a-88dc2fcb8ba0`,
`ZetaNine.exponentially_small_nonzero_forms_of_zeta_nine`.

For an even `n >= 2`, the actual multiplier is

```
W := ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier n hn2 hn b a
```

Its source definition is the actual rational inverse multiplier applied to
`(b,0,0,0,a)`. It is a rational quartic. Integer polynomial coefficients are
neither necessary nor asserted. The integers occur in the actual output.
The weighted series is precisely

```
fun m : Nat =>
  (ZetaNine.CoefficientMap.weightedR n W ((m+1 : Nat) : Rat) : Real)
```

The real polynomial is `W.map (Rat.castHom Real)`, the Taylor center is
`u0=(n+1)*(2*n+1)`, and the first strictly beyond-center test point is
`u1=(n+2)*(2*n+2)`.

The height margin uses the same norm as the new complete weighted estimate:

```
sum r in Finset.range 5, abs (W.coeff r : Real) * (n : Real)^(2*r)
```

## Proposed Open leaf

`one-form-open-contract.lean` gives the complete candidate type:
`ZetaNine.GraphOneForm.unbounded_short_positive_actual_selected_inverse`.

There exists a fixed `delta > 0` such that for every threshold `N` there is
an even `n >= max(N,2)` and integer output `(b,a)` whose actual multiplier
has all Taylor coefficients at `u0` nonnegative, has strictly positive
evaluation at `u1`, and has height at most `exp((2641/250-delta)*n)`.

The quantifier is **unbounded even scales**. It does not strengthen the
notes to an eventual construction at every even scale.

The finite `u1` certificate can equivalently be replaced by nonzero `W`
under the Taylor cone assumption: Taylor shifting is injective, a nonzero
polynomial has a nonzero Taylor coefficient, and nonnegative coefficients
evaluated at the strictly positive displacement `u1-u0` give a positive
sum. The finite evaluation formulation avoids hiding nonvanishing of the
complete sum in the Open child.

## Existing public Proved children that will really be used

| ID | Theorem and exact platform module | Actual use |
| --- | --- | --- |
| `bb7477e4-5539-4015-b8cf-9bad57e1c8a0` | `ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_actual_HasSum_and_absolute`, `Theorems.Thm_ZetaNine_CoefficientMapMatrix_selectedIntegerMultiplier_actual_HasSum_and_absolute` | Identifies the actual full weighted series with `b+a*zetaReal 9` and gives its summability. This is the direct integer-output and higher-zeta-cancellation bridge. |
| `a8a15e54-0fca-4932-b4ea-171e7d02fc03` | `ZetaNine.taylor_sign_implies_kernel_sum_pos`, canonical preamble `import Mathlib` | Applied to the actual positive tail and actual Taylor polynomial; establishes strict positivity of the complete form. Its local wiring file is a statement catalog only, not a complete proof. Root must give a correctly registered platform reference module or use an explicit canonical local type fixture for a reduction check. |
| `134e564c-4327-43b0-9ecd-e7d08fa133ec` | `ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_coordinates_product`, `Theorems.Thm_ZetaNine_CoefficientMapMatrix_selectedIntegerMultiplier_coordinates_product` | Appropriate in a further decomposition of the new height-cone leaf: identifies the true lattice map `E = S*F^-1`. It need not be artificially imported into the immediate analytic assembly if that assembly does not use it. |

The actual bijection theorem `ce238b53-8b97-42f6-ac2e-191364bf4a42`
and determinant theorem `3e15df20-1023-4b72-95ab-1ad07c34b3e5`
belong further down the inverse-map proof chain. They should not be unused
imports in the immediate parent reduction.

## New A child awaiting platform publication

Actual target-plan name:
`ZetaNine.AnalyticWeightedBound.actual_weighted_uniform_o_one`.
Actual candidate module:
`Theorems.Thm_ZetaNine_AnalyticWeightedBound_actual_weighted_uniform_o_one`.
The name has no `AnalyticWeightedSumBound` component.

Its complete type is

```
exists eps : Nat -> Real,
  Tendsto eps atTop (nhds 0) and
  forall n, 1 <= n -> forall W : Rat[X], W.natDegree <= 4 ->
    abs (tsum (actualWeightedSequence n W)) <=
      exp ((-2641/250 + eps n)*n) * weightedCoefficientHeight n W
```

The full native proof and complete platform AUTHOR are known to Root. The
platform independent review and public theorem ID are not established by
this design. The frozen target plan still describes its historical SOURCE
preparation stage; its mathematical name and full type are what is reused.

## Mathematical assembly

1. Take `eps` from A and `delta` from the actual inverse-image Open child.
   Since `eps(n) -> 0`, fix `N0` so `eps(n) < delta/2` for every `n >= N0`.
2. For any requested parent index `m`, apply the unbounded-scale child
   with `N = max(N0,m+1)`. It supplies an even scale `n > m` and integers
   `(b,a)`, the true selected multiplier and its cone-height certificate.
3. The Matrix HasSum child identifies the full actual series with the
   integer form and supplies summability; `zetaReal 9` is definitionally
   `(riemannZeta (9 : Complex)).re`.
4. The first `n` summands vanish because `actualR n k = 0` for `1 <= k <= n`.
   For the remaining tail use `t=n+1+j`,
   `Rtail(j)=(actualR n t : Real)` and `u(j)=t*(t+n)`.
   The actual kernel is strictly positive for `t>n` and `u(j)>=u0`.
   The concrete sample `j=1` is exactly `u1` and is strictly positive.
   Apply the public Taylor-sign child and the finite-head-zero identity
   to obtain `0 < b+a*zetaReal 9`, hence nonzero.
5. The genuine degree of the selected multiplier is at most four.
   A and the height margin yield
   `abs(form) <= exp((-delta+eps(n))*n)`.
   Since `eps(n)<delta/2` and `n>=2`, this is at most
   `exp(-(delta/2)*n) < exp(-(delta/2)*m)`.
6. Choose the parent fixed rate `c=delta/2>0`. The construction actually
   gives the required pair for every `m`, hence the parent's eventual
   formulation. The proof does not assume any form is small or nonzero.

## New elementary bridge obligations

The following elementary facts must be present as actual proof bodies or
honest additional children; they must not be silently assumed from an
unpublished SOURCE module:

- the selected multiplier has `natDegree <= 4` (native Matrix source proves it);
- the initial actual kernel terms vanish (complete A source proves it);
- actual `R_n(t)>0` for natural `t>n` (complete rational-factorial A source proves it);
- tail shift preserves sum after the zero finite head, and preserves summability;
- coercing rational polynomial evaluation agrees with real mapped evaluation.

These require no new mathematical open conjecture. They can be proven
locally in the reduction or exported as a small complete actual-kernel
bridge. The already public Taylor-sign theorem has strictly positive
kernel hypotheses, so applying it directly to the full positive-integer
sequence would be wrong: that sequence has its first `n` terms zero.

## Publication order

Finish and independently verify the actual elementary bridge and A;
publish the one new Open construction child; build the reduction with
only the actual Open/Proved child imports; independently verify exact
canonical types and standard-axiom closure; then submit the sketch for
the existing one-form parent. Decompose the new Open construction further
through the actual row-inverse formula, lattice height and Taylor cone
leaves. Only real theorem uses should determine graph edges.
