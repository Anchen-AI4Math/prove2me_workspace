# Local jet insertion: independent mathematical and static review

Reviewed on 2026-10-04 by the platform-author agent, which did not write this
JetInsertion candidate. This review ran ordinary file/hash reads only: **zero
Lean/Lake invocations**. The result is a mathematical/static assessment, **not
a kernel PASS**, an elaboration result, or a completed transport theorem.
No candidate, native source, frozen preparation, scope, Root module or API was
changed. The sole new deliverable is this research note.

## Fixed inputs and exact boundary of the review

The appendix manifest has SHA-256
`cf98c0db95ef6c8517980f01bb9e9f3e45518d9d56e5c34551bff5ec9aeb81f2`.
Its two appendix files, four declared source dependencies and existing exact
check report were independently rehashed with matching lengths and digests:

- `JetInsertionCandidate.lean`: 8522 bytes,
  `2fc25799ea86b7951894f5c12d4fd0d9f1cacd934a8b9986febf35077c37ee08`.
- `README.md`: 1916 bytes,
  `2c6793fe937e4044c69d5f534b96e30383fbb7996467c4d66b82c0569f2a56b7`.
- `CoefficientMapFormalTransportNumerators.lean`: 11100 bytes,
  `ba71d6f2a0d761f1e468f8282205a9806411972a8209d619b1999a920d5ee81a`.
- `CoefficientMapNumeratorPartialFractions.lean`: 17848 bytes,
  `2dd97638ab3fbc86124db40b78ef2f38fd7536c630d0240cb33fb4f35f8ffc77`.
- `CoefficientMapPartialFractions.lean`: 18065 bytes,
  `eb0b8d54cd29ddaaa9404ee26a704bb6a47e8306741c49a6bba9b7232231f61a`.
- `CoefficientMapJet.lean`: 10033 bytes,
  `e50e11c0afd2eaac1d5c58c412e5e59bc5c2068c9826063eacee8dc88fc1735a`.
- Existing `exact-checks.json`: 89422 bytes,
  `4d571fbf3379303f63a2e70a474cb73fc063805272bfaaf9d37f95c296f549c0`.

The existing exact checks were hash-verified as a bound input; they were not
reused as a universal proof. Additional reads were restricted to the actual
Data/Bounds, pole/weighted-numerator definitions, finite harmonic output,
Aggregate and Matrix definitions, and the two needed pinned Mathlib interfaces.
The manifest's claim concerning the earlier nineteen-file design was not
expanded into a new nineteen-file audit here.

## Mathematical verdict and all twelve candidates

No mathematical counterexample was found within the stated domains. Each of
the twelve statements follows from actual polynomial pole products and the
actual cleared-series definition. In particular, the three final insertion
statements cover all nine actual orders, not an abstract coefficient array.
They remain meaningful for arbitrary, even improper, numerators. That does
not make an improper numerator eligible for the separate global PF theorem.

Write

\[
 M_m(x)=\prod_{k=0}^m(x+k),\quad
 D_{m,j}(z)=\prod_{\substack{0\le k\le m\\k\ne j}}(z+k-j),\quad
 S_{m,j}(A)=A(z-j)D_{m,j}(z)^{-9}.
\]

These are the actual `polePolynomial`, `shiftedClearedDenominator` and
`numeratorClearedSeries`. For `j <= m`, the constant term of `D` is a product
of nonzero integer differences, so its inverse is a genuine formal-series
inverse. The existing constant-term lemma is even stated for arbitrary `j`.
`numeratorLocalCoefficient m j s A` is `[z^(9-s)] S_{m,j}(A)`.

| Candidate | Independent reason and required domain |
|---|---|
| `pole_factor_candidate` | Remove the actual member `j` from `range(m+1)`; `j<=m` is essential. |
| `pole_comp_shift_factor_candidate` | Compose the preceding equality with `z-j`; the removed factor becomes `z`. |
| `pole_upper_candidate` | The full product gets exactly the new factor `x+m+1`, for every `m`, including zero. |
| `upper_cleared_denominator_candidate` | Shift the full product equality and cancel the nonzero polynomial `X`; valid `j<=m`. |
| `shift_successor_comp_candidate` | `(z-j)+1=z-(j-1)`; the guard `1<=j` is essential for Nat subtraction. |
| `lower_cleared_denominator_candidate` | `M_(m+1)(x)=x M_m(x+1)` shifted at `j`; cancel `X`, with `1<=j<=m+1`. |
| `upper_whole_actual_series_candidate` | Multiply by the actual new denominator, use uniqueness, and cancel the inserted factor; no degree assumption. |
| `lower_whole_actual_series_candidate` | The actual factor `(z-j)^9` cancels and the composed numerator becomes `A(z-(j-1))`; no degree assumption. |
| `local_zero_of_shift_X_nine_candidate` | `X^9` dividing the shifted numerator makes coefficients of degrees 0 through 8 zero after multiplication by the denominator inverse. |
| `upper_all_actual_jets_candidate` | Old indices retain the whole series; the new index `j=m+1` has a shifted `X^9` factor and all nine jets zero. |
| `lower_all_actual_jets_candidate` | At `j=0` the shifted numerator has `X^9`; all other poles use old index `j-1`. |
| `double_all_actual_jets_candidate` | Apply lower insertion followed by upper insertion; exactly `1<=j<=n+1` remains. |

The final formulas are consequently

\[
 a_{m+1,j,s}((x+m+1)^9A)=
 \begin{cases}a_{m,j,s}(A)&j\le m,\\0&j=m+1,\end{cases}
\]

\[
 a_{m+1,j,s}(x^9A(x+1))=
 \begin{cases}0&j=0,\\a_{m,j-1,s}(A)&1\le j\le m+1,\end{cases}
\]

and

\[
 a_{n+2,j,s}(x^9(x+n+2)^9A(x+1))=
 \begin{cases}a_{n,j-1,s}(A)&1\le j\le n+1,\\0&j=0\text{ or }j=n+2.\end{cases}
\]

All require `1<=s<=9` and the stated pole-index bound. The coefficient index
`9-s` then runs through 8 down to 0. There is no sign `(-1)^s`: the shift is
`x+1`, which moves old pole `-(j-1)` to new pole `-j`, with the same local
coordinate. Omitting the order guard would misread Nat subtraction; this
review makes no order-zero or order-above-nine assertion.

## Zero-size and endpoint probes by direct algebra

For `m=0`, `M_0=x` and `D_(0,0)=1`. For arbitrary `A`, upper insertion gives
old series `A(z)` at `j=0`, and a multiple of `z^9` at `j=1`. Lower insertion
gives a multiple of `z^9` at `j=0`, and series `A(z)` at `j=1`. Double insertion
with `n=0` leaves exactly the series `A(z)` at `j=1`, with zero nine-jets at
`j=0,2`. These deductions do not assume `A` is proper or a constant.

Generic insertion at zero does **not** extend the actual chosen Connection
transport to `n=0`. `connectionPair 0 r` is the fallback pair `(0,0)`; the
existing actual chosen numerator transport retains `1<=n`. Thus the generic
module must keep `m=0`, while the actual Connection bridge keeps `n>=1`.

At `j=n+2`, only the double-inserted old numerator and the upper-inserted
remainder have zero jets. The lower-inserted remainder contributes its final
old jet with a minus sign. The final actual coefficient is generally
`-c_(n+1,s)`, not zero. At `j=0`, it is `c_(0,s)`. These are the important
boundary terms for the subsequent finite-sum cancellation.

## Bridge to the actual local transport: still to be proved in Lean

Let `P=connectionP n r`, `q=connectionQ n r`,
`N=weightedNumerator n P`, and `C=shiftedRemainderNumerator n q`.
The actual Numerators dependency contains, for `n>=1`,

\[
 N_{n+2}(x^r)=x^9(x+n+2)^9N(x+1)+(x+n+2)^9C(x)-x^9C(x+1).
\]

Apply the actual `numeratorLocalCoefficient (n+2) j s` to this polynomial
equality. One short generic additivity lemma is missing from the insertion
file; subtraction is already available as `numeratorLocalCoefficient_sub`.
Use all three insertion statements and the existing
`numerator_local_coefficient_weighted_agreement`. This yields, for every
`n>=1`, `r : Fin 5`, `j<=n+2`, `1<=s<=9`,

\[
 a^{\rm new}_{j,s}=e^{\rm old}_{j,s}+e^c_{j,s}-e^c_{j-1,s},
\]

where the extensions are **exactly** Data's `extendedOldCoefficient`,
`extendedRemainderCoefficient`, and `previousRemainderCoefficient`. The last
one is zero at `j=0` by its explicit branch, rather than by unsafe `j-1`.

This does not use PF existence, coefficient transport as a hypothesis, degree
bounds, parity, infinite summation, or zeta independence. The actual chosen
numerator identity supplies the Connection premise internally.

Summing over `j in range(n+3)`, the old jets reindex from `j=1..n+1` to
`k=0..n`; the two remainder sums are both `k=0..n+1` and cancel. It follows
that every actual `rho_s` is transported, all `1<=s<=9`. A Lean proof must
retain `j=0` and `j=n+2` before this cancellation; dropping either endpoint
would leave a false boundary remainder.

## Constant term: an essential additional obligation

The insertion endpoints alone do not prove the first column of `F`. With
`H_s(j)=harmonicPower s j`, the actual constant is
`B=-sum_j sum_s a_(j,s) H_s(j)`. The finite harmonic successor identity gives

\[
 B_{n+2}(x^r)=B_n(P)
   -\sum_{k=0}^n\sum_{s=1}^9\frac{b_{k,s}}{(k+1)^s}
   +\sum_{k=0}^{n+1}\sum_{s=1}^9\frac{c_{k,s}}{(k+1)^s}.
\]

The correction signs agree with the actual numerator identity: **minus old
PF at 1, plus remainder PF at 1 in the shifted variable** (equivalently
`Q(2)` in the original `t` variable). This is a finite algebraic proof, and
does not need an equality of real zeta linear combinations.

For the actual quartic `P`, properness of its weighted numerator follows
from the existing degree bound. For the actual `q`, the Bounds dependency
provides the strict properness of `C` at pole parameter `n+1`, retaining
`n>=1` and `q.natDegree<=9`. Apply the actual generic PF theorem at the
regular rational point `x=1`:

- The old correction is `N.eval 1 / M_n.eval 1^9 = weightedR n P 1`.
  It is zero for `n>=1`, since the actual positive-root numerator includes
  the factor `x-1`.
- The remainder correction is `C.eval 1 / M_(n+1).eval 1^9`. It is zero by
  `shiftedRemainderNumerator_eval_one`, which includes the extra factor
  needed at `n=1`. Every denominator factor `1+k` is nonzero.

Thus `B_(n+2)(x^r)=B_n(P)` is supported by the existing dependencies, but
the finite harmonic regrouping and the actual PF evaluations still require
new Lean proofs. One must not invoke generic global PF for arbitrary
improper `A` merely because the insertion lemmas accept arbitrary `A`.

Absolute or infinite summation is not required to establish the **formal**
five-output matrix identity: all five entries are finite coefficient/harmonic
expressions. A later analytic interpretation of this matrix may separately
reuse actual HasSum/norm-summability and parity. This shorter finite route
avoids deriving coefficient equality from an equality involving zeta values.

## Matrix orientation and minimum next modules

The actual definitions fix

\[
 F_n(l,i)=\operatorname{aggregate}_n(x^l)_i,\qquad
 \Gamma_n(r,l)=[x^l]P_r.
\]

The Bounds dependency restores
`P_r=sum_l C(Gamma n r l) * X^l` with `P_r.natDegree<=4`.
Actual aggregate linearity gives

\[
 F_{n+2}(r,i)=\operatorname{aggregate}_n(P_r)_i
   =\sum_l\Gamma_n(r,l)F_n(l,i).
\]

The correct direction is therefore **`actualFMatrix (n+2) = connectionGamma n
* actualFMatrix n`**. It is neither `F_n*Gamma_n` nor a transpose. The rows
are monomial indices; the columns are `[B,rho_3,rho_5,rho_7,rho_9]`. No inverse,
determinant or injectivity assumption is needed. The requested final endpoint
can retain `Even n` and `n>=2`; the algebraic local and finite-output route
itself appears to support the stronger `n>=1` domain, without parity. This
stronger-domain observation is not a new verified theorem.

A minimal staged implementation is:

1. **`CoefficientMapFormalTransportJets.lean`**: move the twelve unchanged
   mathematical statements into a real native module after a lane grant;
   add generic jet additivity, the actual chosen all-jet transport theorem,
   and the finite all-nine-rho transport theorem. No PF degree assumptions
   belong in the generic insertion statements.
2. **`CoefficientMapFormalTransportOutputs.lean`**: prove the finite harmonic
   correction, discharge both point evaluations using the true degree and
   regularity bounds, obtain the actual five-output equality for each `r`,
   and finish the matrix equality by the existing quartic restoration and
   aggregate linearity. Its natural new dependencies are Jets, Bounds,
   generic numerator PF, FiniteSum/Aggregate and the actual Matrix definition.

The four remaining substantive Lean obligations are: elaborate the twelve
candidate scripts; prove the actual add/sub jet bridge and finite reindexing;
prove the harmonic constant correction with actual PF evaluations; assemble
the actual rows with the prescribed matrix orientation. None is an abstract
transport or PF-existence assumption.

## Static interface checks and compilation risks

Two pinned Mathlib source interfaces were checked directly:

- `Finset.mul_prod_erase` states `(f a * prod_(s.erase a) f)=prod_s f` under
  membership, so the candidate's `.symm` has the correct orientation.
- `PowerSeries.X_pow_dvd_iff` states `X^n | phi` iff every coefficient with
  index below `n` vanishes, so `(9-s)<9` under `1<=s<=9` is the correct gate.

The imported `clearedPolePolynomial_comp_shift`, actual-series denominator
identity/uniqueness, and `polePolynomial_successor_shift` have the required
mathematical directions. No immediate mathematical gap was found in the
twelve proposed scripts. Actual elaboration remains unknown: likely local
issues are Nat/rational casts, coercion rewrites into PowerSeries, composition
association, and cancellation expression association. In particular, the
`symm; apply numeratorClearedSeries_unique` steps must infer the **new** pole
parameter and inserted numerator; successful execution is still required.

This assessment supplies a faithful route to all actual jets and identifies
the missing finite-output proofs. It does not certify a Lean theorem, a kernel
audit, a completed formal transport, platform acceptance, heights or
irrationality.
