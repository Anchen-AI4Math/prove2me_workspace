The proof chooses a fixed threshold after which $n\ge3$ and $n^a\ge17$. Thus $D=\lfloor n^a\rfloor\ge16$ and $n^a/2\le D\le n^a$. The ceiling choice satisfies $D^{s/2}\le g\le2D^{s/2}\le\sqrt D$, since $s\le1/2$.

The two proved full-D cost lemmas bound all oracle calls and the scan, prime-selection and construction terms. Because $D\le n$ and $\log n\ge1$, $(\log D+1)^2\le4\log^2n$. Adding the terms gives $(256C+36C')\kappa n^3D^{-s/2}\log^2n$. Finally the floor lower bound implies $D^{-s/2}\le2n^{-as/2}$, yielding one actual Exact Triangle solver with exponent $3-as/2$, uniformly in $\kappa$ and the weight bound.

The ceiling identity is needed only when $D\ge1$, allowing the finite parameter routines' behavior at size zero. The theorem does not identify a restricted-domain cost function with a global solver; the actual full-D host and globally correct Lop solver are explicit premises supplied by separate program proofs.
