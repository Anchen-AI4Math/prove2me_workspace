# ParameterShift candidate: independent offline precheck

The inspected candidate has SHA256 dc629940878fd365e1cb995fe3e4ca6b75b38aee6938eeca37a9fa493e7156b0.
This is a source and exact rational algebra precheck, with zero Lean/Lake
invocations. It is not a compiled proof review or PASS verdict.

The source's positive product uses roots 1,...,n and the negative product
uses n+1,...,2n. At n+2,t-1 the added three numerator pairs, after retaining
the two cancelled endpoints explicitly, are
(t-n-a)(t+2n+a) = u-(n+a)(2n+a), a=1,2,3. Thus connectionZ is the correct
three-factor polynomial. The factorial ratio is exactly
((n+1)(n+2))^7. The new pole product is
(t-1)*poleProduct(n,t)*(t+n+1), so the denominator factor is
D=(t-1)^10*(t+n+1)^10. No extra sign or scale appears.

For regular_new(k): t-1+k != 0 for 0<=k<=n+2, the index substitutions
k+1 and k+2 respectively give old regularity at t and t+1. The endpoints
k=0,1,n+2 give t-1, t, t+n+1 nonzero. This is sufficient for all divisions
and cancellation of D. The candidate never needs R_n(t) nonzero; 21 tested
regular points have R_n(t)=0 and satisfy the identities.

When n>=1, Nat(n-1) casts to n-1 and V_n(t+1)=(t+1)(t+n). The actual R shift
then gives Q(t+1)=R_n(t)*(t+2n+1)/(t+n+1)^10*q((t+1)(t+n)). Consequently
D*(Q(t)-Q(t+1))=R_n(t)*H(q). This sign agrees with the original full
D*P(u)+H(q)=c*Z(u)*(u-n-1)^r, and division by the proven nonzero D yields
exactly the candidate's finite rational point transport.

The n>=1 assumption is necessary for this Q bridge with the actual clipped
V definition. At n=0,t=2,q=X, regular_new holds but V_0(t+1)=9 while the
second H argument is (t+1)t=6. The actual Q difference is 8747/1119744,
whereas R_0(t)*H(q)(t)/D(t)=13121/1679616. They differ. The separate product
and R parameter-shift identities do not use V and remain valid at n=0.

The exact Python replay exited 0. It checked 40 whole polynomial product
index identities and 24 D/Z/factorial identities for n=0,...,7, 45 regular
implications and R ratio points, and 420 Q monomial difference points.
For each n=1,2,3 it independently solved the exact 15-by-15 system for all
five original targets r=0,...,4. All 15 complete polynomial residuals were
zero, P degree<=4 and q degree<=9; 60 corresponding true R point transports
held. These are exact finite instances, not a universal Lean certificate.

The source's final unique-existence endpoint keeps the full original
polynomial equation and adds point transport; uniqueness comes from the
same polynomial equation. The reviewed algebraic shape has no identified
mathematical mismatch. Source elaboration, actual closed types, proof-field
closure and kernel/axiom checks remain for the first real compilation.
Five formal F-coordinate transport, infinite summation and irrationality
are outside this candidate's claims. Kernel/Connection/Matrix materials were
not edited; all new records are confined to this precheck directory.
