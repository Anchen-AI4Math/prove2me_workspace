# Actual local coefficient transport and the five Gamma outputs

This is an independent, **pure offline mathematical design**. No Lean invocation
was made for this work, and no frozen source, object, audit, Root candidate, scope
or API state was modified. Its exact theorem contracts and five written proof
candidates are in
`verification/coefficient-map-local-transport-offline-2026-10-04/LocalTransportContracts.lean`.
The contract definitions are propositions, not proved declarations or axioms.
The supplied proof candidates have not been compiled.

The inputs are point-in-time snapshots of the actual Data/Bounds/NumeratorPF
definitions and Root's Numerators candidate. The Numerators polynomial endpoint
is being compiled by Root separately; its presence here is a design dependency,
not a claim that the snapshot has passed Lean. All input bytes and SHA-256 values
are recorded in the adjacent `exact-checks.json`, with copies in `input-snapshots/`.

## 1. Actual definitions and the precise identity to transport

Write

\[
 M_m(X)=\prod_{k=0}^{m}(X+k),\quad
 D_{m,j}(X)=\prod_{\substack{0\le k\le m\\k\ne j}}(X-j+k).
\]

Data's actual series and local coefficient are

\[
 S_{m,j}(A)=A(X-j)/D_{m,j}(X)^9\in\mathbf Q[[X]],\qquad
 a_{m,j,s}(A)=[X^{9-s}]S_{m,j}(A).
\]

Here division is the actual formal-series inverse. Its denominator has nonzero
constant term, including m=0. These are exactly
`numeratorClearedSeries` and `numeratorLocalCoefficient`; they are not independent
coefficient variables. `numerator_local_coefficient_weighted_agreement` identifies
them with `weightedLocalCoefficient` for the genuine `weightedNumerator`.

For n>=1 and r:Fin 5, set P=`connectionP n r`, q=`connectionQ n r`,
A=`weightedNumerator n P`, and C=`shiftedRemainderNumerator n q`.
The desired input from Numerators is its exact actual polynomial theorem
`actual_chosen_cleared_numerator_transport`:

\[
 \operatorname{weightedNumerator}_{n+2}(X^r)
 =X^9(X+n+2)^9A(X+1)+(X+n+2)^9C(X)-X^9C(X+1). \tag{1}
\]

The minus sign is forced by Q(x+1)-Q(x+2), and C describes Q(x+1),
so c_j is indexed by x+j, equivalently t-1+j. No additional shift of C is
permitted in the positive remainder term.

## 2. Two numerator-independent local jet lemmas

These lemmas hold for **every** m>=0 and every actual A:Q[X], even if A is
improper. Their scope is j<=m+1 and 1<=s<=9. No parity or degree hypothesis
is needed.

**Upper insertion**:

\[
 a_{m+1,j,s}((X+m+1)^9A)=
 \begin{cases}a_{m,j,s}(A)&j\le m,\\0&j=m+1.\end{cases} \tag{2}
\]

For j<=m, the exact cleared-denominator identity is

\[
 D_{m+1,j}=D_{m,j}(X-j+m+1).
\]

Multiplying `S_{m,j}(A)` by the new denominator to the ninth power gives
the shifted numerator of the lifted A. Apply the already proved
`numeratorClearedSeries_unique` to obtain equality of the **whole actual series**,
then take coefficient 9-s. For j=m+1, the lifted numerator after shifting contains
X^9; its series therefore has all coefficients of degree <9 equal to zero.

**Lower insertion with shift**:

\[
 a_{m+1,j,s}(X^9A(X+1))=
 \begin{cases}0&j=0,\\a_{m,j-1,s}(A)&1\le j\le m+1.\end{cases} \tag{3}
\]

For 1<=j<=m+1, reindex the remaining factors by k=l+1:

\[
 D_{m+1,j}=(X-j)D_{m,j-1},\qquad
 A((X-j)+1)=A(X-(j-1)).
\]

The second displayed expression records the shift composition. It needs
`Nat.cast_sub` under the explicit 1<=j guard; unguarded Nat predecessor at j=0
would select c_0 instead of the required zero. The same series-uniqueness
argument applies. At j=0, X^9 annihilates the first nine coefficients.

The generic zero-at-inserted-pole helper is proposed as
`local_zero_of_shift_X_nine_candidate`: if
`X^9 ∣ A.comp (shiftedVariable j)`, then the actual coefficient is zero for
1<=s<=9. Its written proof uses `PowerSeries.X_pow_dvd_iff` and the explicit
inverse in the definition. It does not use properness or PF.

Combining (2) after (3) gives

\[
 a_{n+2,j,s}(X^9(X+n+2)^9A(X+1))
 =\begin{cases}a_{n,j-1,s}(A)&1\le j\le n+1,\\0&j=0,n+2.\end{cases} \tag{4}
\]

This is shorter than introducing an abstract partial-fraction array and proving
array uniqueness. The existing generic-PF injectivity theorem compares the
actual jets of two numerators; it does not already prove arbitrary array
uniqueness. Equations (2)-(4) avoid that missing bridge entirely.

## 3. Full actual coefficient transport, including both endpoints

Let b_j,s be the actual old weighted jets, c_j,s the actual jets of C for
0<=j<=n+1, and a_j,s the actual new weighted jets. Applying linearity,
(2)-(4), and actual weighted agreement to (1) proves

\[
 a_{j,s}=b_{j-1,s}+c_{j,s}-c_{j-1,s},\qquad 0\le j\le n+2,\ 1\le s\le9, \tag{5}
\]

where b is zero outside 0..n, c is zero outside 0..n+1, and c_-1=0.
The exact theorem statement is `ActualChosenLocalTransportStatement` in the
companion, using Data's `extendedOldCoefficient`,
`extendedRemainderCoefficient` and `previousRemainderCoefficient` without
redefining their indexing.

The two endpoint corollaries are

\[
 a_{0,s}=c_{0,s},\qquad a_{n+2,s}=-c_{n+1,s}. \tag{6}
\]

The right endpoint is present even when the shifted Q itself has only n+2
partial-fraction blocks. It is produced by Q(x+2), and it must remain in the
new n+3-block array. No coefficient parity is used in this proof.

## 4. All nine rho totals and the signed B correction

Summing (5) over j=0..n+2 cancels every c_j exactly once. Reindexing the old
block gives, for every s=1..9,

\[
 \rho_{n+2,s}(X^r)=\rho_{n,s}(P). \tag{7}
\]

This is a finite rational identity. It includes the simple-pole total and all
even-order totals; no zeta linear independence is involved.

Let H_s(j)=sum_{k=1}^j k^-s and B=-sum_j,s a_j,s H_s(j), exactly the existing
`constantTerm`. The old shifted contribution is

\[
 -\sum_{k,s}b_{k,s}H_s(k+1)=B_{\rm old}-\sum_{k,s}\frac{b_{k,s}}{(k+1)^s}.
\]

The remainder contribution, **with its last negative coefficient retained**, is

\[
 -\sum_{j,s}c_{j,s}H_s(j)+\sum_{j,s}c_{j,s}H_s(j+1)
 =\sum_{j,s}\frac{c_{j,s}}{(j+1)^s}.
\]

Thus the precise finite algebra endpoint is

\[
 B_{\rm new}=B_{\rm old}-\sum_{k=0}^n\sum_{s=1}^9\frac{b_{k,s}}{(k+1)^s}
                  +\sum_{j=0}^{n+1}\sum_{s=1}^9\frac{c_{j,s}}{(j+1)^s}. \tag{8}
\]

Use `harmonicPower_succ` before any PF evaluation. The exact finite contract
is `ActualChosenConstantCorrectionStatement`. Arbitrary finite arrays satisfy
this algebra, but the final universal endpoints always substitute actual jets
obtained from (1), not a coefficient-array hypothesis.

## 5. B closes with actual PF at two regular points

P.natDegree<=4 is provided by `connectionP_natDegree_le`, so
`quartic_is_proper` supplies the old PF degree condition. Evaluate the existing
`actual_global_partial_fractions` at t=1. All 1+k are nonzero, and the genuine
base numerator contains the i=0 factor t-1 for n>=1. Therefore the first sum
in (8) is `weightedR n P 1=0`.

For the second sum apply **the actual generic theorem**
`actual_numerator_global_partial_fractions` with

```
m = n + 1
A = shiftedRemainderNumerator n q
t = 1
hproper = shiftedRemainderNumerator_strict_proper n hn q hq
hregular k hk = 1 + (k : Q) != 0
```

Bounds supplies `shiftedRemainderNumerator_eval_one n hn q=0`; equivalently
this is Q(2)=0. It follows from the explicit numerator factor t-2 for all
n>=1. In particular at n=1 it is the extra t-n-1 factor, so one must not
replace this reasoning by the false assertion R_1(2)=0. The companion includes
a complete written (uncompiled) proof candidate for this actual PF-at-one bridge.
There is no assumed PF, no abstract c array and no even-n restriction.
Both corrections vanish, hence

\[
 B_{n+2}(X^r)=B_n(P). \tag{9}
\]

## 6. Five coordinates and Gamma's orientation

The actual `aggregate` is (B,rho_3,rho_5,rho_7,rho_9), so (7),(9) give

\[
 \operatorname{aggregate}_{n+2}(X^r)=\operatorname{aggregate}_n(P_r).
\]

Bounds' `connectionGamma_restores_P` and aggregate linearity give

\[
 F_{n+2}(r,s)=\sum_{l=0}^4\Gamma_n(r,l)F_n(l,s),\qquad
 \boxed{F_{n+2}=\Gamma_nF_n}. \tag{10}
\]

Rows of the existing `actualFMatrix` are multiplier monomials and its columns
are the five outputs. Gamma therefore acts on the **left**. The exact standard
column-action relation is `F_(n+2)^T=F_n^T Gamma_n^T`; it is not F_(n+2)=F_n Gamma_n.
For row coordinates v, `(v * F_(n+2))=(v * Gamma_n) * F_n` follows by associativity.
The companion records both precise universal matrix and row-action contracts.

Every rational transport endpoint (1),(5),(7),(9),(10) holds for all n>=1.
Even n>=2 is needed when using the existing actual odd-zeta five-output
interpretation and bijective/inverse F theorems. For odd n, reflection makes
the four odd-rho columns zero; (10) still holds but cannot establish F
invertibility. Strict properness alone also does not imply summability.

## 7. Import plan and actual remaining compilation work

The proposed new formal module should import exactly:

```
missions.zeta9.formalization.CoefficientMapFormalTransportNumerators
missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions
missions.zeta9.formalization.CoefficientMapMatrix
```

The first import provides Data/Bounds/chosen connection equation and (1).
The second provides denominator uniqueness, weighted agreement, actual PF and
actual numerator subtraction. The third provides `actualFMatrix`, aggregate
linearity and the existing row-action result. No real-number/zeta-independence
module or new PF-existence premise is required.

The main genuine proof tasks are:

1. The two erased finite-product reindexings in section 2. Lower insertion needs
   k=l+1 with the omitted j matching omitted j-1; casts of Nat subtraction must
   be rewritten only under the positive-j guard.
2. Establish whole-series equalities by `numeratorClearedSeries_unique`, rewriting
   polynomial composition/coercions and `mul_pow`. Keep the denominator's ninth
   power attached to its exact series, and use existing nonzero-constant evidence.
3. Branch the two boundary jets, then compose insertions and apply linearity to
   (1). Normalize n+1+1 and rational/natural casts without changing Data's extenders.
4. Finite double-sum reindexing plus `harmonicPower_succ`, preserving j=n+2.
5. Actual old PF@1 and actual generic remainder PF@1, then `Fin 5` aggregate
   extensionality and `Matrix.mul_apply`/`quarticAggregate_eq_row_vector`.

Only these proof obligations remain for a Lean implementation of this design;
the new file supplies propositions and written proof attempts, not a PASS audit.
Existing frozen NumeratorPF source and its author evidence remain unchanged.

## 8. Exact offline evidence and counterexamples

`check_local_transport.py` ran successfully with exit 0 and **530 finite exact
checks**, all with Python `Fraction`, with **0 Lean invocations**:

- 49 generic (m,A) cases, m=0..6 and seven actual numerator choices per m,
  including zero, constants, small polynomials and polynomials at/above the PF
  degree boundary; all nine upper/lower/double jets were compared.
- All whole cleared-denominator reindexings for these m and legal j.
- n=1..5, all five chosen connection systems solved directly from their original
  15-by-15 rational polynomial equations; all coefficients, local jets, both
  endpoints, rho totals, finite B correction, true PF@1, Q polynomial reconstruction,
  strict degree bound, five outputs and all 25 Gamma entries checked.
- Arbitrary finite-array harmonic corrections for n=0..5, retaining both ends.
- Negative controls: n=1,q=1 has c_0,9=c_2,9=-3/512; omitting the last negative
  block changes the rho total and unguarded Nat predecessor changes the left pole.
  At m=0,A=1, inserted-pole s=0 coefficients are -1 (upper) and +1 (lower), so the
  stated 1<=s bound is material. For upper insertion m=0,A=1, outside j=2 the
  order-nine value is -1/512, contradicting the zero branch if the j bound is omitted.
  At n=0, R_0(1)=1 and Q_0,q=1(2)=1/512; degree-nine q reaches the exact PF boundary.

The rational helpers were copied **source-only from this reviewer's prior pure
checker**. The old checker and report writer were not imported or executed, and
no author test code, author finite answers or native object cache was used.
These checks support the design and expose boundary mistakes; they are not a
universal Lean theorem or platform proof.
