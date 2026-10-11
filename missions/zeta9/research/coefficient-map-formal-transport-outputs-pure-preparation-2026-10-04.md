# Actual B, Gamma and five-output transport: pure preparation

This is an implementation candidate and finite mathematical precheck record.
The new Outputs source has not been compiled. No Lean/Lake call was made in this
preparation. Earlier actual Jets author PASS belongs to the exact ccef export,
not to the shared b081 initial candidate, whose bytes remain unchanged.

The new source is `formalization/CoefficientMapFormalTransportOutputs.lean`.
Its exact 16 header contracts are in
`verification/formalization-coefficient-map-formal-transport-outputs-preparation-2026-10-04/endpoint-contracts.json`.
The three primary endpoints are the actual chosen B transport, the full actual
aggregate vector transport, and
`actualFMatrix (n+2) = connectionGamma n * actualFMatrix n` for every `n>=1`.

## Finite constant term and its signs

Write `P=connectionP n r`, `q=connectionQ n r`. These are the actual unique
Connection witnesses, with P degree at most 4 and q degree at most 9, by the
existing Data/Bounds theorems. The verified Jets theorem gives every order 1..9
and index 0..n+2 of the genuine new weighted numerator:

`a(j,s)=old(j,s)+currentQ(j,s)-previousQ(j,s)`.

Here old is b(j-1,s) on 1<=j<=n+1 and zero elsewhere, currentQ is c(j,s) on
0<=j<=n+1 and zero afterwards, and previousQ is zero at j=0 and c(j-1,s)
afterwards. The rightmost coefficient is therefore `-c(n+1,s)`. It must remain
in the harmonic sum even though its contribution disappears from each rho
after finite cancellation.

Three new finite reindexing lemmas multiply these genuine padded coefficients
by `H_s(j)`. They reuse the already proved zero-extension lemmas, with explicit
functions to avoid the higher-order inference failure seen in the first Jets
candidate. The existing harmonic successor identity then gives, at each order,

`sum_j a(j,s) H_s(j) = sum_k b(k,s) H_s(k) + sum_k b(k,s)/(k+1)^s - sum_k c(k,s)/(k+1)^s`.

The definition B is the negative of the sum of these nine harmonic sums.
Consequently its exact intermediate contract is

`B(n+2,X^r) = B(n,P) - oldPF(1) + shiftedQPF(1)`.

The signs were checked directly against the genuine numerator shift relation.
The correction is minus the old weighted rational function at 1, plus Q(2)
in the original t coordinate. The proof uses finite sum commutation and ring
algebra. It does not derive coefficient equality from a zeta-value identity.

## Both correction terms vanish from actual numerators

For the old weighted function, `ProperMultiplier n P` follows from
`2n+2deg(P)<=2n+8<9(n+1)`. The existing actual weighted global PF theorem is
applied at rational t=1. Every factor `1+k` is nonzero. For n>=1 the actual
positive product contains `1-(0+1)=0`, so `weightedR n P 1=0`.

For Q use `shiftedRemainderNumerator n q` at pole parameter n+1. The existing
Bounds theorem derives degree at most `2n+18`, strictly less than `9(n+2)`
for n>=1 and degree(q)<=9. The existing generic numerator PF theorem applies
at the regular shifted point x=1, with all denominator factors `1+k` nonzero.
The actual shifted numerator is zero at x=1 by the Bounds proof of Q(2)=0.
This proof retains the real extra factor needed at n=1; R_1(2) is nonzero.

Thus the source candidate proves B transport from actual PF theorems and actual
degree/root theorems. Neither PF existence nor transport is a supplied premise.
No absolute or infinite sum is required for these finite formal coordinates.

The n>=1 guard cannot be dropped using this argument: R_0(1)=1. Also n=0 and
q=X^9 produces a remainder numerator of degree 18, equal to its denominator
degree 18, so the generic strict-proper PF theorem cannot be used there.

## Aggregate and matrix orientation

The existing aggregate coordinates are exactly B,rho3,rho5,rho7,rho9. Combine
the new B transport with the existing all-nine-rho transport by five actual
Fin cases. This gives the whole function equality

`aggregate (n+2) (X^r.val) = aggregate n (connectionP n r)`.

Gamma's r-th row is `[X^l]P_r`. Bounds already restores its coordinate polynomial
to the actual P_r. The existing Matrix theorem
`quarticAggregate_eq_row_vector` is valid for every n and every coordinate row.
It supplies

`aggregate n P_r = connectionGamma n r vecMul actualFMatrix n`.

Taking the actual r,i entry yields left multiplication by Gamma. F's rows are
monomial indices and its columns are the five formal outputs, so the endpoint
is `F(n+2)=Gamma(n)*F(n)`. There is no transpose and no inverse or determinant
premise. The candidate supports all n>=1, including odd n; no Even assumption
is needed for this finite algebraic result.

## Exact finite prechecks and their scope

The new `exact_precheck.py` reuses only the explicitly identified Fraction
polynomial helper SOURCE from the earlier independent review. It takes that
source's function prefix before its executable main, never imports its earlier
instances/results and never executes its old report writer. This reuse is
explicitly recorded; these checks are not an independent audit.

Fresh exact reconstruction of the original 15 by 15 Connection system for all
five targets at n=1,2,3,6 passed 588 checks. They include every harmonic order,
the three harmonic padding identities, the signed B correction, the two zero
PF values, five actual output coordinates, 100 actual left-Gamma matrix
entries, and negative controls for wrong right multiplication and missing
domain guards. All four wrong right products differ from their true next F.

These are finite prechecks, not a proof for every n and not Kernel PASS.
The output is `exact-precheck.json`, SHA256
`ecfbad81806d37e1f59838d7ebe10ffdd950ffdbee6f2b0391541eae491a9641`.

## Fresh source-only project and next actual validation

`.rt/oa1` was explicitly checked absent before creation. The actual import
scheduling closure comprises 21 source modules: the earlier 19-module Jets
closure, native Matrix, and Outputs. It is a text import schedule, not an
actual Lean declaration graph. All modules are copied from exact source bytes;
the Jets module alone is overridden with the actual verified ccef export.
The original shared b081 source and its frozen records remain untouched.

Two lossless Expr DAG audit/validation SOURCE programs are copied as source,
with their supplied hashes checked. No ja1/ni1/nu1/ft1/pfi/Root proof objects
are copied. The new build cache and packages junction remain absent. The
longest future olean path plus the required 64-character private suffix is 214,
within the Windows 259 limit.

The future granted serial runner schedules 21 native compiles, two serializer
source controls, the complete 16 source/expected type/kernel/axiom/DAG audit,
nine closed boundary controls and 25 own-cache object resolutions. Its 27
planned calls are not actual invocation counts. Actual source/expected
kernel `isDefEq` comparisons remain distinct from lossless Expr reconstruction.

Likely elaboration points to resolve only after a lane grant are the generic
PF-at-one cast normalization, harmonic finite-sum rewrite matching, and the
definitional row-vector/matrix-entry conversion. Every proof script is complete;
no sorry/admit/axiom declaration appears. These scripts are not claimed to
compile until the actual future source/control calls finish successfully.

All previous frozen5/38/439 and ja1 bytes are left unchanged. No Root, scope,
API, credentials, installation, publication or acceptance action is performed.
