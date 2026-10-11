# Analytic audit of the first ζ(9) linear-form construction

Status (2026-09-24): the contour identity and the **upper** exponential rate below are proved for the stated short-zero family. The six numerical upper bounds are certified by interval arithmetic. No saddle asymptotic, eventual nonvanishing, or irrationality theorem follows. The exact primitive evaluations from the separate arithmetic workstream are all larger than one on the first-round grid.

## 1. The precise linear form and pole cancellation

Use the rising Pochhammer convention `(x)_r=x(x+1)⋯(x+r−1)`. Let `n` be a positive even integer, `0<m<=3n/14`, and

```
R_(n,m)(t) = (n!)³/(m!)¹⁴ · [(t−m)_m(t+n+1)_m]^7/(t)_(n+1)^3,
L_(n,m) = Σ_(k>=1) R_(n,m)^(6)(k)/6!.
```

The rational function has order at most three at `0,−1,…,−n`, seventh-order zeros at `1,…,m` and `−n−m,…,−n−1`, and

```
R(t)=O(t^(14m−3(n+1)))=O(t^(−3))  (t→∞).
```

Consequently the series for `L` converges absolutely. Write the exact partial fractions as `R(t)=Σ_(j=0)^n Σ_(r=1)^3 a_(j,r)/(t+j)^r`. Six derivatives give

```
L = (Σ_j a_(j,1)) ζ(7) + 7(Σ_j a_(j,2)) ζ(8)
    + 28(Σ_j a_(j,3)) ζ(9) + B,       B∈Q.
```

The coefficient of `t^(−1)` at infinity is zero, hence `Σ_j a_(j,1)=0`. Reflection gives `R(−n−t)=−R(t)` for even `n`, so `a_(n−j,2)=−a_(j,2)` and `Σ_j a_(j,2)=0`. Therefore `L=Aζ(9)+B` with rational `A,B`. This construction uses ordinary integer poles in `t`; it is **independent** of the positive functional `μ_9` on poles at negative integer squares. No claim about triple poles in that functional is needed.

The vanishing of the ζ(7) and ζ(8) coefficients is an identity of rational partial fractions. It does not show that `L≠0`, even when `A≠0`, because a hypothetical rational relation could make `Aζ(9)+B=0`. The signed exact evaluations in the separate finite workstream certify nonzero only at their tested parameters.

## 2. Exact cotangent contour and its six elementary oscillations

Let

```
K_7(z)=Σ_(k∈Z)(z−k)^(−7)
     = [d^6/dz^6 (π cot πz)]/6!
     = π^7 [302 cos(πz)+57 cos(3πz)+cos(5πz)]/[360 sin^7(πz)].
```

The three cosines are six exponential oscillations with frequencies `±1,±3,±5` before division by `sin^7`. The numerator coefficients sum to `360`, giving the correct principal part `(z−k)^(−7)` at each integer. The residue of `R(z)K_7(z)` at a positive integer `k` is exactly `R^(6)(k)/6!`; the first `m` such residues vanish because of the seventh-order zeros.

For any `c∈(m,m+1)`, in particular `c=m+1/2`, a right-closing rectangle is clockwise. Its distant right edge vanishes because `R(z)=O(z^(−3))` and its horizontal edges vanish because `K_7` decays exponentially off the real axis. Thus the **orientation sign** is

```
L = −(1/(2πi)) ∫_(c−i∞)^(c+i∞) R(z)K_7(z) dz.       (C1)
```

This is a convergent exact contour identity, not a saddle approximation. For `Im z>0`, write `q=e^(2πiz)`. Then

```
K_7(z) = i(2π)^7/720 · Σ_(ℓ>=1) ℓ^6 q^ℓ
       = i(2π)^7/720 · q(1+57q+302q²+302q³+57q⁴+q⁵)/(1−q)^7. (C2)
```

The lower-half-plane formula is its complex conjugate. Along `z=m+1/2+iny`, `y>=0`, one has `q=−e^(−2πny)`; the first Fourier term has phase `−i` times a positive constant and exponential `e^(−2πny)`. In particular `|K_7(z)|<=(2π)^7 e^(−2πny)` there. The conjugate lower segment and the leading sign in (C1) must both be retained when analyzing possible cancellation.

## 3. A rigorous global **upper** exponent without a saddle assumption

Fix `α=m/n∈(0,3/14]`, take `z=nw`, and set all logarithms on the principal branch in the upper half-plane. Stirling summation of the two numerator products and one denominator product gives the analytic phase

```
Φ_α(w) = −14α log α
         +10w log w +7(w+1+α)log(w+1+α)
         −7(w−α)log(w−α)−10(w+1)log(w+1).             (C3)
```

The coefficient of `n log n` is zero exactly: the factorial prefactor contributes `3−14α`, while the products contribute `14α−3`. On the upper half-plane, the first Fourier oscillation adds `2πiw` to the phase. Thus a candidate complex saddle would satisfy

```
Φ'_α(w)+2πi=0,
Φ'_α(w)=10log w+7log(w+1+α)−7log(w−α)−10log(w+1).   (C4)
```

Exponentiating (C4) gives a polynomial equation, but loses the logarithm branch. Merely locating a root of that polynomial does not identify a contributing saddle, prove its dominance, or prove the conjugate contributions do not cancel. None of those claims is made here.

An upper bound needs no deformation. On the exact half-integer contour, put

```
H_α(y)=Re Φ_α(α+iy)−2πy,    y>=0.
```

For each fixed `α` in the six-point grid, the logarithm of the absolute value of `R(m+1/2+iny)` is at most `n Re Φ_α(α+iy)+O_α(log n)`, **uniformly** in `y>=0`. To see the endpoint carefully, put `δ=1/(2n)`, `x=α+δ`, and first compare the discrete products to integrals along the **shifted** line `Re w=x`. The function `u↦log|x−u+iy|` decreases on `[0,α]`; its right-endpoint sum is at most `n` times its integral. The function `u↦log|x+1+u+iy|` increases; its right-endpoint sum exceeds the integral by at most its total variation, bounded independently of `y,n`. The denominator function `u↦log|x+u+iy|` increases, so the negative of its right-endpoint sum is at most the negative integral; its extra `u=0` term is bounded above by `−log α`. Stirling contributes `O_α(log n)`. This gives `log|R|<=n Re Φ_α(x+iy)+O_α(log n)` uniformly. In particular, at `y=0` the numerator factors are midpoints relative to the *unshifted* interval, but they are left endpoints after reversing the shifted interval `[δ,α+δ]`; the shift cannot be discarded without the next estimate.

Finally, `n[Re Φ_α(x+iy)−Re Φ_α(α+iy)]` is the integral of `n Re Φ'_α(u+iy)` over `u∈[α,α+δ]`. For `y<=1`, its only singular term is `−7log|u−α+iy|`, bounded above in the integral by `7|log(u−α)|+O_α(1)`; its integral is `O_α(δ log n)`. For `y>=1`, the four logarithms in `Φ'` have zero total coefficient and their combination is uniformly bounded, including as `y→∞`. Thus replacing the shifted line costs `O_α(log n)` uniformly in `y`.

Combining this estimate with (C1)–(C2) and changing the vertical variable from `Im z` to `ny` gives a bound by `n^{O_α(1)}∫_0^∞exp(nH_α(y))dy`. As `y→∞`, `H_α(y)=(14α−3)log y−2πy+O_α(1)`, and `14α−3<=0`. Hence for all sufficiently large fixed `Y`, uniformly for `n>=1`, the tail `y>=Y` is bounded by `∫_Y^∞e^(−πny)dy`; on `[0,Y]` the ordinary compact Laplace upper bound applies. Therefore

```
limsup_(n→∞, m=αn) (1/n)log|L_(n,m)| <= sup_(y>=0) H_α(y).       (C5)
```

This is an absolute-value upper bound. It does not show `L` is eventually nonzero or that the limsup equals the right side.

The derivative has a particularly simple exact form:

```
H'_α(y)=3π/2−10 arctan(y/α)−7 arctan(y/(1+2α))
              +10 arctan(y/(1+α)).                       (C6)
```

It starts at `3π/2` and tends to `−2π`. Multiplying `H''_α(y)` by the positive product `(α²+y²)((1+2α)²+y²)((1+α)²+y²)` gives a quadratic polynomial in `x=y²`. For each of the six rational grid values, its constant coefficient is negative, its linear coefficient positive, and its leading coefficient `3−14α` nonnegative. Hence `H''` changes sign exactly once from negative to positive (even at the endpoint, where the quadratic coefficient is zero), `H'` has exactly one positive zero, and that zero is the global maximizer of `H`.

The companion script `scripts/linear_saddle.py --certify` brackets each zero between exact dyadic rationals, evaluates `H` on the whole bracket with 256-bit Arb balls, and writes `verification/analytic-vertical-bound.json`. Its certified strict upper bounds are:

| `α` | `sup H_α` is strictly below |
|---:|---:|
| `1/28` | `0.671769718688` |
| `1/14` | `1.167676972547` |
| `3/28` | `1.609438937754` |
| `1/7` | `2.021873399673` |
| `5/28` | `2.416195251742` |
| `3/14` | `2.798637880122` |

These are bounds for the unnormalized `L`. The positive exponential rates do not produce small integer linear forms after denominator clearing. The separate exact first-round grid (`n=56,112,224`, six positive ratios, plus controls) found `|P_(n,m)(ζ(9))|>1` in every tested main case. The measured `log|P|/n` values, copied from the exact workstream's verified JSONL, are:

| `α=m/n` | `n=56` | `n=112` | `n=224` |
|---:|---:|---:|---:|
| `1/28` | `7.9191` | `8.5278` | `8.2735` |
| `1/14` | `8.4387` | `9.1105` | `8.6570` |
| `3/28` | `8.9999` | `9.1080` | `9.1011` |
| `1/7` | `9.1179` | `9.3245` | `9.3380` |
| `5/28` | `9.0470` | `9.9092` | `9.5075` |
| `3/14` (properness endpoint) | `9.2903` | `9.9597` | `9.7902` |

Along each fixed ratio the three primitive values did not show strict decrease. Finite evidence does not rule out every future sequence, but it does not justify extending this grid to larger `n` as though a negative trend had appeared.

## 4. The independent μ₉ Gram comparison

The positive odd-`s` functional specializes to

```
w_9(y)=2(2π)^8 y^9/8! · Σ_(ℓ>=1)ℓ^8e^(−2πℓy),
μ_9(t^e)=(-1)^e B_(2e+2)(2e+9)!/[8!(2e+2)!],
μ_X((t+j²)^−1)=j^8(X−H_j^(9))−1/8+1/(2j).
```

For `P(t)=D_N(t)^8`, `h=K−N`, and `G_ij(X)=μ_X(P(t)t^(i+j)/D_K(t))`, the value at `X=ζ(9)` is positive definite. The `X`-coefficient matrix is `V diag(j^8P(−j²)/D'_K(−j²))Vᵀ`, with `j=N+1,…,K`; the square Vandermonde and nonzero diagonal show `deg_X det G=h`. The residue-at-infinity form is `B_ij=+[t^(−1)]_∞t^(i+j+4)P(t)/D_K(t)`, so its first possible nonzero anti-diagonal is `i+j=K−deg P−5`, one earlier than for `s=7`.

For primes `p>=11`, the polynomial moments are `p`-integral at every `e<4p−5`. At `e=4p−5`, the Bernoulli index is `8(p−1)` and the seven numerator factors are `8p−7,…,8p−1`, containing no `p`; von Staudt–Clausen gives valuation exactly `−1`. For the unshifted `D_N^8` matrix, this places the first possible polynomial correction at `i+j=K−8N+4p−5` and bounds its rank by `min(h,[K+6N−4p+4]_+)`. This is a moment-integrality/rank lemma, **not** a determinant valuation theorem.

For fixed odd `s`, changing `s=7` to `s=9` changes only polynomial prefactors in `w_s(K√t)`. With the same `q,α,h/K`, the leading `K²` external field and logarithmic-energy comparison are unchanged; only `O_s(K log K)` real terms change. The prime-by-prime integerization cost is not transferable: both Bernoulli-moment thresholds and harmonic pole valuations change.
