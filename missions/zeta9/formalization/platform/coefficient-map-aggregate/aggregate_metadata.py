"""Academic descriptions for the exact three selected Aggregate endpoints."""


def build_metadata(source_hash):
    origin = "Zeta(9) genuine five rational coefficient outputs and quartic coordinates: missions/zeta9/research/coefficient-map-aggregate-2026-10-04.md. Frozen missions/zeta9/formalization/CoefficientMapAggregate.lean SHA256 " + source_hash + ". The coefficients are extracted from the actual weighted local formal series; B is the actual finite negative harmonic constant."
    definition = r"""For a natural number $n$ and a rational polynomial $W$, let $c^W_{n,j,s}$ be the actual weighted local coefficient, extracted at degree $9-s$ from the genuine cleared formal series. Use the existing exact rational definitions

$$\rho_{n,s}(W)=\sum_{j=0}^n c^W_{n,j,s},\qquad B_n(W)=-\sum_{j=0}^n\sum_{s=1}^9 c^W_{n,j,s}H_j^{(s)}.$$

Define the actual five-coordinate map, indexed by $\operatorname{Fin}(5)$ in the order displayed,

$$F_n(W)=(B_n(W),\rho_{n,3}(W),\rho_{n,5}(W),\rho_{n,7}(W),\rho_{n,9}(W)).$$

For $a\in\mathbb Q^5$, define $C(a)=\sum_{i=0}^4 a_iX^i$ and $\pi(W)_i=[X^i]W$. The other three definitions package $F_n$, $C$, and $F_n\circ C$ as rational linear maps, with their actual addition and scalar identities proved.

This is the genuine five-output aggregate, not the complete $(n+1)$-by-9 local coefficient array. Its definition assumes no properness, reflection, kernel triviality, rank or inverse. In particular $F_0(X^4)=0$ while $X^4\ne0$ and $\rho_{0,1}(X^4)=1$."""
    titles = ["Additivity of the actual five rational coefficient outputs", "Exact recovery of every rational quartic from its five coefficients", "All nine coefficient totals vanish under actual even strong-proper aggregate zero"]
    natural = [r"""Let $n$ be any natural number and let $W,V\in\mathbb Q[X]$. For the actual aggregate

$$F_n(W)=(B_n(W),\rho_{n,3}(W),\rho_{n,5}(W),\rho_{n,7}(W),\rho_{n,9}(W)),$$

where every coefficient is extracted from the genuine weighted formal local series and $B_n$ is the finite negative harmonic constant, one has

$$F_n(W+V)=F_n(W)+F_n(V).$$

The equality is of all five rational coordinates, with pointwise addition. It holds for arbitrary rational polynomials and includes $n=0$ and zero polynomials, without an evenness, degree, properness or cancellation hypothesis.""", r"""Let $W\in\mathbb Q[X]$ have natural degree at most four. Write $\pi(W)_i=[X^i]W$ for $0\le i\le4$, and define $C(a)=\sum_{i=0}^4 a_iX^i$ for a rational five-coordinate vector $a$. Then

$$C(\pi(W))=W.$$

This recovers the actual polynomial from its five coefficients, including the zero polynomial, constants and nonmonic quartics. The degree bound is essential. It is a statement about quartic coordinates and does not assert that the aggregate $F_n$ has an inverse.""", r"""Let $n$ be an even natural number, and let $W\in\mathbb Q[X]$ satisfy the actual stronger degree bound

$$2n+2\operatorname{natdeg}(W)+2\le9(n+1).$$

Assume the genuine five-output aggregate vanishes, $F_n(W)=0$, with coordinates $B_n(W),\rho_{n,3}(W),\rho_{n,5}(W),\rho_{n,7}(W),\rho_{n,9}(W)$. Then, for every natural order $s$ with $1\le s\le9$,

$$\rho_{n,s}(W)=\sum_{j=0}^n c^W_{n,j,s}=0.$$

These are the actual totals of the weighted local coefficients. Evenness and the stronger degree bound are retained. The conclusion concerns nine totals, not the individual local coefficient array, and it does not infer $W=0$. Strict properness alone would not suffice: $n=0,W=X^4$ has $F_0(X^4)=0$ but $\rho_{0,1}=1$; it is proper and fails the stronger bound.""" ]
    return origin, definition, titles, natural
