# Two-form graph bridge: pure SOURCE design

Status: **uncompiled SOURCE**. This design has made 0 Lean calls, 0 API calls and 0 credential reads. The exact accepted original open parent is preserved.

For the original family, F_k is the genuine constant/rho3/rho5/rho7/rho9 map on quartics. Its selection rows S are B and rho9. For integers (b,a), set

    E_k(b,a) = (b,a) S F_k^-1,
    H_k(b,a) = sum_{r=0}^4 |E_k(b,a)_r| k^(2r).

The new Open child requires fixed delta>0 and, for every lower cutoff N, an even k>=max(N,2) with two integer pairs of nonzero determinant and each H_k<=exp((2641/250-delta)k). It asks for geometric coefficient size rather than assuming small linear-form values. It does not assert the selected rational quartic has integer coefficients. Its proof is precisely the missing lattice/height/J task.

The accepted Matrix coordinate theorem identifies E_k with the true selected quartic coefficients. The accepted Matrix HasSum theorem gives the true sum b+a Re zeta(9). The locally complete A theorem gives, uniformly in all quartics, exp((-2641/250+epsilon(k))k) times coefficient size, with epsilon tending to 0. Choose a threshold after which epsilon(k)<delta/2. At each target n choose an available even k>=max(n,threshold). The value is then strictly below exp(-delta k/2)<=exp(-delta n/2). Both pairs share k and delta, and the original integer determinant is retained.

This proves the existing two-form obligation from a genuinely separate geometric Open child and three actual analytic/algebraic endpoints. No bound on form values, no injectivity assumption and no arbitrary coefficient map are introduced. The finite clearing product does not itself provide the required asymptotic short-vector margin.

The three imported endpoint modules are all used explicitly in the proof body. Catalogue `sorry` declarations remain type references, not independently verified source proofs. Root must compile against the actual complete dependencies and independently audit before claiming a complete bridge or uploading the sketch.
