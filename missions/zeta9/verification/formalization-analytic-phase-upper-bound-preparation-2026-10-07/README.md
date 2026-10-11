# Actual phase upper-bound source preparation

This is **UNCOMPILED**. Neither the unchanged 15-lemma
`formalization/AnalyticPhase.lean` preparation nor the new complete-source
`formalization/AnalyticPhaseUpperBound.lean` candidate was compiled in this run.
There is no kernel, axiom, platform or Z9.A completion claim.

The new candidate keeps the exact original phase and supplies complete
tactic bodies, with no proof holes, for the intended statement

\[
\forall x\in\mathbb R,\quad x>1\Longrightarrow f(x)\le-2641/250.
\]

The mathematical chain actually yields the stricter rational cap
\(f(x)<-10564011/1000000\), leaving the positive margin \(11/1000000\).
For \(1\le x\le101/100\), the smooth function

\[
G(x)=10x\log x+(x+2)\log(x+2)-10(x+1)\log(x+1)
      -f(1)-(x-1)(1+\log A)
\]

satisfies \(G(1)=0\) and
\(G'(x)=\log((x+2)(x/(x+1))^{10})-\log A\le0\).
Here \(A=(301/100)(101/201)^{10}\) is the actual original constant.
Thus \(G(1+u)\le0\), while \(\log z\le z-1\) gives
\(u(1+\log(A/u))\le A\) for every \(u>0\). No continuity or derivative of
\(u\log u\) at zero is used. The original actual right-side antitonicity
handles all \(x\ge101/100\).

Mathlib already proves the finite atanh-series lower and upper bounds used
here. Six terms at \(1/3\) certify
\(\log2>693147/1000000\); eleven terms at \(1/2\), with Mathlib's actual
geometric remainder \(1/6291456\), certify
\(\log3<1098613/1000000\). Exact rational normalization gives
\(A<309/100000\). `exact_certificate.py` reproduces these integer/fraction
calculations and checks the unchanged base hash and source contract. It uses
no floating-point certificate, subprocess, Lean or API.

Only the phase component is prepared. Genuine moment asymptotics, infinite
tails and a coefficient-uniform \(o(1)\) remain separate Z9.A obligations.
Fresh source compilation and explicit complete-type/standard-axiom checks
require a new Root Lean lane grant.
