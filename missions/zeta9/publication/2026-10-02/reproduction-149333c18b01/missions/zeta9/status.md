# Zeta(9) first research round

Latest continuation (2026-10-02, Lean deferred):
[new linear forms, arithmetic reductions and scalar classification](research/progress-2026-10-02.md).
The main J exit remains unproved. A new unconditional primitive-row theorem
gives Gram gcd | exterior content * saturated Gram discriminant and a
computable divisor of the actual center denominator. An exact minimum-
denominator same-side interval projection gives six strictly nonzero
primitive values below one, through n=192. Its infinite decay, and growth
of both Farey parent denominators, are equivalent to irrationality; finite
success is not a noncircular proof of J.

A different growing-dimension positive Gram family, h by h with 2h+3
consecutive square poles, stays linear in zeta(9). Its positive raw error
has proved exponential bounds f_c-log(16) <= lower rate <= upper rate <= f_c<0.
For c=0 these endpoints are -8.8797162298 and -6.1071275076. The required
full reduced denominator upper bound remains open. All 39 finite examples
have costly primitive values; 38 large-prime maximal-minor gcds are one,
while (h,M)=(10,10) gives 24077, so a universal gcd-one shortcut is false.

For h=1,S=1, arbitrary dispersed integer square poles are now completely
classified: m<=5 primitive values grow uniformly, with rate at least 9/50
per largest pole for m=5; m>=6 give primitive constant one. Actual zero
tail sums are handled by finite-color prime budgets, not ignored.

An isolated seventh-derivative Apery-type sum has the written asymptotic
L_n ~ (16/15)n^-4(log n)^5>0, exact full-normalizer decay criterion and
a large-prime valuation theorem. Its exceptional-prime mass bound is open.
An explicit eightfold-zero variant eliminates all first n leakage terms
while preserving isolation. Six certified cases have changing signs and
primitive magnitudes above one; eventual nonvanishing, analytic rate and
content asymptotics remain open for that repair.

Five exact verification scripts passed root reruns and independent written
reviews. Proofs and finite certificates are distinct; no actual Lean build
or external submission occurred. Earlier dated entries retain their states.

Latest frontier advance (2026-10-01, Lean deferred):
[remaining obstacle and exact arithmetic frontiers](research/progress-2026-10-01-frontier.md).
The main written route has one essential unresolved exit: exclude eventual
fixation of the shortest primitive integer direction. Under the proved V
and transport results this is equivalent to J and to zeta(9) irrationality;
S is a stronger sufficient condition, not a separate necessary hurdle.
An explicit moving rational projection now has eventual nonvanishing and
a precise Gram-gcd/area decay criterion, whose required growth is unproved.

New square-pole theorems cover arbitrary fixed h>=m and fixed positive
numerators, including moving bounded-degree nonnegative integer numerators
of subexponential height, with primitive lower log-rate 4.5 per largest
active pole. A stronger cluster theorem covers all fixed h,m, bounded
numerator degree and subexponential height whenever relative pole width
tends to zero: log primitive value / b - 9 * actual degree -> 0.
Degree zero gives primitive constant 1; all nonconstant covered sequences
grow. Consecutive S=1 poles have exact degree max(0,min(m,h,2h+4-m)),
including every low-rank boundary; fixed positive numerators and fixed
offsets have an eventual degree and the corresponding exact rate.

Mellin strict increments and all-parameter large-prime cancellation are
now controlled by rectangular maximal minors: P>=F/J^2. The required
asymptotics for F and J remain open. A shifted p=19 example shows complete
19^2 cancellation, ruling out a naive full-rank converse.
Six exact verification groups and independent mathematical reviews passed.
No new Lean build or external submission occurred; J/S and irrationality
remain open. Earlier dated entries below preserve their original states.

Latest arithmetic advance (2026-10-01, Lean deferred):
[two all-parameter growth obstructions](research/progress-2026-10-01-arithmetic.md).
For sufficiently right-shifted Mellin blocks, both the reduced denominator
and the positive primitive integer-coefficient form have exact log-rate 18
per unit M. A sharper bound also excludes M/(D^2 log D) -> c > 17/18,
with positive lower rate 18-17/c; sparse shifted windows have a separate
dimension/width criterion. These are sufficient exclusion ranges, not sharp
boundaries or impossibility results for the entire Mellin construction.

For every integer square-pole pair 1 <= a < b, with dimension two and
constant numerator one, the primitive polynomial value has uniform lower
log-rate at least 4.5 per unit b. Thus translating or separating that
specific complete two-pole family cannot extend its finite (1,2) small
value into a decay sequence. A general harmonic-denominator stability
lemma and exact arithmetic certificates support the new proofs.
Independent mathematical review and root reruns passed. S/J and zeta(9)
irrationality remain open; no Lean build or external submission occurred.

Latest structural advance (2026-09-30, Lean deferred):
[sharp positive-moment errors, arithmetic comparison and filter barriers](research/progress-2026-09-30-structure.md).
For consecutive Mellin exponent blocks {M,...,M+D}, the actual rational
approximation error is now proved uniformly asymptotic to
5040/[D^8(D+2M)^8]. The primitive integer form tends to zero exactly when
its denominator is o(D^8(D+2M)^8); that arithmetic condition is not proved.
For the same rational positive weight and dimension, with dimension and
numerator degree O(K), the s=9 and s=5 real Hankel log-determinants differ
by only O(K log K). Any K^2-scale gap in primitive values therefore comes
from the full-coefficient integer normalization.

A modified two-pole example yields the exact primitive polynomial
-6163+22568X-16384X^2, whose value at zeta(9) is rigorously between 0 and 1
(about 0.44830598763). This is one finite example, not an irrationality
argument; its powers do not overcome an unknown rational denominator.
The old direction route now has exact irreducibility certificates and an
all-fixed-rational-filter barrier: adjacent finite differences retain the
positive second-mode exponent. All adjacent coordinate minors have explicit
nonzero asymptotics, but joint integrality still gives no contradiction.
New proofs received cross-review and exact scripts passed. S/J, the required
normalization decay, and zeta(9) irrationality remain open; no Lean run.

Latest public-source and alternate-route audit (2026-09-30, Lean deferred):
[public progress, exact counterchecks and positive-form alternatives](research/public-progress-and-routes-2026-09-30.md).
The public zeta(5) repository has an explicit complete irrationality endpoint
with one project PNT axiom; we audited its fixed source and certification
record but did not locally replay its Lean build. A separate Zenodo zeta(7)
v1 manuscript has an exact arithmetic inconsistency: its defining formula
gives 7/20 at y=3/2 while Table 5 gives -299/20. Correcting the outer integral
invalidates its stated decay bound; this does not prove actual growth.

Two positive Gram mechanisms were adapted to zeta(9), independently of the
old lattice direction problem. The square-pole route has 24 main and 110
grid exact primitive-polynomial cases, plus 60 single-pole linear-form cases;
the tested zeta(9) parameters do not yield a decay family. The Mellin monomial
route gives a rigorously nonzero primitive P*zeta(9)-Q for every exponent set
E, together with the all-parameter lower bound P/(8! K_D), D=max E and
K_D=(D+8)^2*binom(D+7,7)^2/8. All 20 tested sets with at least three elements
already fail the necessary small-denominator test by exact integer comparison.
Finite cases are not asymptotic impossibility results. The old S/J conditions
and zeta(9) irrationality remain open. New written arguments and certificates
are separate from the existing Lean mirrors; no external submission occurred.

Latest all-model advance (2026-09-29, Lean deferred):
[all fixed models and the remaining direction problem](research/progress-2026-09-29-all-models.md).
Every positive even and odd local model is now proved nonsingular, with
explicit alternating determinant signs. The even proof uses a narrower
actual exterior cone; the odd proof constructs a new exact rational
connection and its own all-parameter cone, with genuine initial matrices.
The complete arithmetic envelope now gives signed rate < -0.05865038,
limsup log(N/g)/n < 9.44134962, and limsup B_n < **10.22921877**,
with margin > **0.33478123** below tau=10.564.
For each fixed integer output (b,a), a nonzero, log(h_n/q_n)=o(n).
Under a rationality assumption this implies B_n+sigma_n -> alpha,
approximately 10.56415384, and liminf sigma_n > 0.33493507;
these are compatible conditional consequences, not a contradiction.
Exact ellipse/minima, actual second-mode direction, and endpoint-height
results are also recorded in the report. S, J and irrationality remain
open. Proofs and exact certificates received independent cross-review;
no Lean build or external submission was performed. The eight earlier
Lean mirrors still contain sorry. Earlier entries retain their dated states.

The final fixed-axis theorem additionally bounds log(q_B)/n by <0.106618
and proves h_n/q_n(b,a) divides q_B a for arbitrary moving integer outputs.
It gives only limsup(B_n+sigma_n)<=alpha+S, still above the critical alpha.
The adjugate scale rho_n is a positive integer with lower exponent
>7.9291597879. These results were independently reviewed and rerun and
do not close the remaining direction condition.

Latest post-V advance (2026-09-29, Lean deferred):
[exact area growth and direction changes](research/progress-2026-09-29-post-v.md).
The actual exterior recurrence now has an exact rational invariant-cone
certificate for every real n>=20, plus uniform projective contraction and
an independently reconstructed F20 initial wedge. This proves the formerly
open sharp area rate log(Xi_n)/(2n) -> (1/4)log(A B), approximately
5.5085439542. The uniform first-output height exponent improves from
<9.31161 to <5.05562, and the combined volume upper bound to <10.394861.
A separate polynomial-index transport theorem proves that, under the
already proved V, J is equivalent to liminf sigma_n=0 and to infinitely
many changes of the primitive first-output direction. None of these open
conditions is asserted. Exact finite diagnostics cover 100 actual lattices
and 99 adjacent inclusions/direction changes; these do not imply infinitely
many changes. New proofs were independently reviewed; the cone certificate
was independently rerun. S, J and irrationality remain open; no Lean build
or external submission was performed.

Latest advance (2026-09-29, Lean deferred):
[written proof of VC and V](research/vc-closure-2026-09-29.md)
closes the original nonnegative arithmetic budget VC at the written-proof
level: limsup E_mid/n <= 538676482493/1243484457600 < **0.433200**,
strictly below the certified threshold 0.610714369473055...
Merged-pole trace identities, a CRT treatment of ordinary harmonic terms,
and the twenty certified fixed models give sharp local bounds. A universal
excess bound of 7 controls the remaining blocks by fixed-cutoff limits.
The genuine discount has liminf U/n >= 0.160566059492300..., yielding
limsup (E_mid-U)/n <= 0.272633148749255... and limsup B_n < 10.394960.
Consequently VA and V are proved in the research notes, with more than
0.169 margin below tau=10.564. Exact arithmetic and source certificates
passed, and the new proofs received independent cross-review.
The independent shape condition S, the combined condition J and zeta(9)
irrationality remain open. This is not a Lean-checked result; no Lean build
or external submission was performed. The eight registered mirrors still
contain sorry. Earlier dated entries below retain their historical states.

Latest continuation (2026-09-29, Lean deferred):
[twenty prime blocks and the 2.116 bound](research/progress-2026-09-29-continuation.md)
reduces the uniform middle-prime excess upper bound from <10.486 to **<2.116**.
Exact fixed-model certificates cover odd blocks m=1,3,...,19 and even blocks
m=2,4,...,20, each with an all-prime statement outside a fixed finite exception
set. A separate reverse bound proves a2<=10 throughout every odd block under
explicit size conditions, without a model nondegeneracy assumption. The joint
envelope integral lies between approximately 2.115033951154927 and
2.115160935281912. Proofs were cross-reviewed; exact algebra, rational
integration, source hashes and 2,533 additional real-matrix cases passed.
Current envelope contributions from the first two blocks already total
547/720 > 0.759, so extending only the nonnegative tail estimates cannot
close the required 0.61071437 threshold. This is a limitation of the present
upper envelopes, not a lower bound on the true arithmetic budget.
VC, the separate lattice-shape condition S, J and irrationality remain open.
No Lean build or external submission was performed.

Latest mathematical advance (2026-09-29, Lean deferred):
[three local arithmetic improvements and the joint budget](research/progress-2026-09-29.md)
lowers the uniform middle-prime excess upper bound from <14.337 to **<10.486**.
The new endpoint-cluster theorem gives v_p(N_n) <= 7 + floor(3n/(2p))
+ floor(7n/(2p)) + 1_(p=257) for max(7,n/2) < p < n.
Its exact 3x3 low-zeta matrix has determinant -2^14*3*257, explaining
the existing n=258, p=257 exception. A separate odd-block cancellation
theorem and reverse propagation inside integral connection blocks supply
the remaining improvement. The combined envelope integral is certified
between 10.485368532870627 and 10.485495516997612; this is not a lower
bound for the actual budget. Written proofs received independent cross-review;
exact algebra, rational integration and finite implementation checks passed.
The 0.61071437 target, VC, the independent shape condition S, J and
irrationality remain open. No Lean build or external submission was performed.
The older entries below retain their dated proof states.

Local arithmetic advance (2026-09-28, Lean deferred):
[local connection and prime budget](research/local-connection-budget.md) proves
v_p(N_n) <= 13 + floor(3n/(2p)) + floor(7n/(2p)) <= 21 for every prime
max(7,n/2) < p <= n. The proof uses a new exact polynomial/cofactor certificate
for C(n), and the local Smith profile (0,1,1,1,1) of F_(p-1).
Replacing the old envelope on this entire prime interval lowers its integral
by exactly 8: the uniform middle-prime excess budget is now < 14.337,
versus the earlier < 22.337. The required 0.61071437 threshold is still open,
as is the independent lattice-shape condition S. No irrationality is claimed.
Reproducible symbolic identities and independent finite checks passed;
see verification/local-connection-2026-09-28/symbolic.json.

Further research (2026-09-28, Lean deferred at the user's request):
[fixed-window asymptotic](research/fixed-window-asymptotic.md) proves
L_(n,m) ~ 81/(80(m!)^4) n^(4m-3) (log n)^6 for each fixed m, hence eventual
strict positivity, with an explicit sufficient threshold. Standard d_n^9/G
integerization has exponential growth rate 9. Positivity and this growth
also hold for m(n) <= c log n/log log n, any fixed 0 < c < 3/28.
This is a written proof, not Lean checked; it does not exclude extra primitive
content cancellation or the positive-ratio / two-dimensional lattice routes.
See [difficulty and outlook](research/proof-outlook-2026-09-28.md). The global
irrationality goal and the uniform lattice/arithmetic bottleneck remain open.

Latest update (2026-09-28): see [the progress survey and continuation](research/progress-2026-09-28.md).
The first-round coefficient gap C3 is now closed at the written-proof level:
for every even n >= 2 and m >= 0, sign(A_(n,m)) = (-1)^(m+n/2), with an
explicit factorial/binomial lower bound. This is not a Lean-checked result,
and neither nonvanishing of the linear form nor irrationality follows.
Combined with the existing contour upper bound, it gives eventual rational
approximation errors below exp(-c_alpha n) on all six fixed slopes, with
certified c_alpha between 2.813123 and 4.957923. No denominator-times-error
decay or nonzero-error assertion is established. The registered build passes
after the import repair described below; all eight registered mirrors still contain sorry.
The dated entries below preserve the earlier proof states.

Build fix (2026-09-28): all eight theorem mirrors now import only the Mathlib
modules needed by their statements, instead of the full Mathlib umbrella.
A single normal build recompiled all eight successfully (3150 jobs vs 8713),
without serial prewarming or cache replacement. The previous explanation
"missing .olean.private files" was not established: files existed and serial
imports worked. See verification/build-fix-2026-09-28/README.md and build.log.

Completed 2026-09-24. Status: first research round complete; no irrationality
proof is claimed. See [the report](report.md) for results and proof boundaries.

Primary route: third-order integer poles, seventh-order endpoint zeros, and
sixth-derivative summation yielding a rational linear form in 1 and zeta(9).
Secondary route: positive simple-square-pole Gram determinants using the
general odd-zeta functional already implemented under missions/zeta7.

The 21 linear-form and 21 zeta9 Gram samples all have primitive absolute value
strictly above one. Two zeta5/zeta7 regression controls also passed. There were
no unresolved computation timeouts. No n448 candidate met the promotion gate.

Proved local results include the all-prime d_n^9/G integerization, the exact
large-prime gcd valuation and its asymptotic integral, and a global analytic
upper bound. The upper bound does not close to a negative exponent. Proofs
were cross-reviewed; no eventual nonvanishing or irrationality is established.

Exact coefficients, primitive normalization, hashes and Arb ball evidence are
stored under verification/. No Lean or external submission was performed.

## Proof-state audit (2026-09-25)

[An audit of the whole effort](research/zeta9-proof-state-audit.tex) ([Chinese
summary](research/zeta9-proof-state-audit-zh.md)) reconstructs the proof state
item by item, classifies every definition / lemma / numerical claim, draws the
dependency DAGs toward the irrationality of zeta(9), and lists every logical
gap. It repairs nothing. Part I covers the first research round; Part II covers
rounds 2-9, the local roadmap DAG (13 open nodes, 27 note-proved, none Lean
checked) and the private platform mission (open root, two SKETCH_ACCEPTED
decompositions, eight abstract theorem-level proofs).

Verdict: in Part I the analytic side supplies only *upper* bounds for the linear
form while the arithmetic side controls only denominators, so the route has no
mechanism for the decay a proof would need; in Part II every closing statement
is a for-all (over primitive directions, or over infinitely many n) while the
corpus holds five-scale finite certificates only, and the newest geometric lemma
(FQ) is vacuous below n ~ 1686 -- far beyond every parameter ever used. The
proved uniform arithmetic estimate stands at 22.337 against a requirement of
0.61071437.

The audit also re-verified, independently: the contour-identity orientation
sign; the H'/H'' phase data; the Gamma enclosures; the sup-H bounds; the
improved integerization t# = d_n^9/G on five parameters (including n=224); the
large-prime gcd formula on new data (216 parameters, 1951 prime terms, no
failures); the round5-7 saddle constants x_*, f(x_*), a (to full displayed
precision); the FQ sample-point activation threshold; and the true-kernel
five-point cubature weights. Scripts and transcripts:
verification/audit-2026-09-25/.

No irrationality statement is claimed at any point.

---

## 2026-09-25: platform DAG wiring

The private mission `8195d8fe-059f-4515-92b4-57b585e2bac6` now has the goal theorem
attached to real children. Before this session
`ZetaNine.irrational_zeta_nine` was a bare `Open` leaf with **zero** decompositions.
Now:

- five new private theorem items — three `Proved` general lemmas (the formalisable
  cores of nodes TP and FQ) and two `Open` obligations (R1, R2);
- two `SKETCH_ACCEPTED` decompositions of the goal, one per main line (one-form and
  two-form);
- five new milestone links (TP1, TP2, FQ1, R1, R2), 35 → 40 milestones;
- blind independent read-back for all five statements, all faithful;
- mission description and discussion updated (comment `7463b390`).

The goal remains **Open**. Neither open obligation is proved, and the concrete
construction still has no Lean definitions, so the arithmetic arrows
(`V ← VA,Q,X` etc.) are deliberately not posted yet. Full record:
`roadmap/platform/wiring/README.md`.

### Same day, notes-layer batch

Four more note-proved nodes were published, proved and milestone-linked
(`publish_notes_layer.py`, receipt `wiring/notes-layer-receipt.json`):

| node | milestone | child edge |
|---|---|---|
| `ZetaNine.five_sample_sign_forces_nonzero` | TP3 | ← `quadrature_exact_of_moments` |
| `ZetaNine.min_lt_weighted_average_lt_max` | FI1 | — |
| `ZetaNine.mediant_strictly_between_min_and_max` | FI2 | ← `min_lt_weighted_average_lt_max` |
| `ZetaNine.positive_matrix_maps_nonneg_to_pos` | TA1 | — |

Milestones 40 → 44, linked-to-theorem 11 → 15. Two new platform decomposition edges were
registered.

### Same day: public abstract-layer mission, 8/8 Proved

The public proposal *Formalize the abstract layer of "Research Notes on ζ(9)" (v0.1)*
(`00d787d8-91c8-45bf-87f0-6a5e9e8bc472`, namespace `Zeta9Note.*`) now carries all eight of its
theorems as `Proved`: eight local `Sol_Zeta9Note_*.lean` compile with `lake env lean` (exit 0,
no `sorry`), the combined `formalization/Zeta9Note.lean` in the public repository compiles, and
all eight submissions came back `ACCEPTED` (receipt
`roadmap/platform/public-proposal/submissions-receipt.json`). Two of the eight are reductions
(`five_sample_sign_forces_nonzero ← quadrature_exact_of_moments`,
`mediant_strictly_between_min_and_max ← min_lt_weighted_average_lt_max`).

None of the eight mentions ζ(9); they are the abstract criteria and positivity/quadrature
lemmas of the note. The proposal is still `In review` with an empty `mission_id`, but the
platform accepted submissions at that stage and flipped every theorem to `Proved` — the
earlier assumption that it would refuse was wrong, and `submit_solutions.py` now exposes
`--allow-pre-approval` for it. The private root remains `Open`. The mediant first came back `CE` because of a local trap — in this
environment `rw` does not rewrite inside a `∑` binder, and `set … with hx` already
folds the target so `rw [← hx]` then fails; switching to `simp only [..., ← lemma]`
fixed it (recorded in `memory/LEAN-PITFALLS.md`). Blind read-back passed on all four.
Goal still **Open**.
