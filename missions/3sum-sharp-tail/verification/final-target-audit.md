# Static audit of the final 3SUM target

Audit date: 2026-10-14. This is a source/type audit only; it does not compile or
validate a proof.

## Target and parameter match

`Theorems/Thm_ThreeSumSharpTail_threeSum_1999017.lean` states exactly
`EndStatement.ThreeSum.SolvedInTime 1.999017`. The published target's formal
type is unchanged in `Solutions/Sol_ThreeSumSharpTail_cost_regime_solve_3sum.lean`:
it assumes `G`, rational `a,s,r`, `0<a<1`, `0<s<1/2`, a uniform
`CostsWithinP` certificate on `1 ≤ D ≤ N^a`, and the two strict exponent
inequalities, and concludes `SolvedInTime r` whenever `r > 2-as/4`. The
preprocessing and query expressions in `hcost` are the exact stated bounds,
including `(log D+1)` factors. `CostsWithinP` constrains the actual retained-tail
preprocessing cost and query cost; the subsequent Lop-detection time bound
adds its `nD+w+1` overhead. The target does not replace the retained-tail cost
by the older relaxed `cost8` interface.

The numeric certificate records exact rational parameters
`c=21`, `θ=0.11202`, `a=0.05665`, and `s=0.06945`. It certifies the encoding,
preprocessing, query, prime-selection, and construction inequalities required
by the parameterized statement. Its exact exponent calculation is
`2-as/4 = 1.999016414375`, so the selected `r=1.999017` has strict margin
`0.000000585625`. Thus the final decimal is not rounded down from the claimed
bound. The cost-regime target's stricter-looking `s<1/2` is satisfied by the
certificate's `s=0.06945`; the analytic admissibility theorem itself states
`s<1`, with its query condition supplying the sharper requirement.

The exact published type of `admissible_parameters_solve_3sum` has the five
analytic inequalities and `r > 2-as/4` as hypotheses and concludes the same
`SolvedInTime r` predicate. The exact type of `threeSum_1999017` specializes
that predicate to `1.999017`. Neither type adds an oracle for the algorithm,
assumes correctness, or weakens the uniform word-width/correctness conclusion.

## Meaning of the conclusion

The necessary source definition is
`Definitions/Def_TrulySubcubicAPSP_SourceSpecification.lean`:

- `EndStatement.ThreeSum` has instances `Fin n → Int`; acceptance means that
  three pairwise distinct positions have integer sum zero.
- `Problem.SolvedBy` runs one finite `List Instr` from position zero on the
  specified initial memory and requires the correct verdict within `T n` steps.
- `Problem.SolvedInTime` quantifies over every natural `κ`, chooses a program,
  word-width constant `b`, and natural-valued time function `T`, and requires
  correctness for every input with entries bounded by `n^κ` and every word
  width `W ≥ b*(Nat.log2 n+1)`.
- `BigO` encodes the exact rational exponent by integer powers. At
  `1.999017 = 1999017/1000000`, the asymptotic requirement is
  `T(n)^1000000 ≤ K*n^1999017` for all `n≥2`.

The machine is an integer-addressed, fixed-width word RAM with constant-write,
add, subtract, multiply, indirect load/store, signed conditional jump,
accept, and reject instructions; each instruction consumes one step, and
arithmetic is on `BitVec W`. The formal target includes all natural input
sizes, including `0,1,2`, and all sufficiently large widths with no upper
bound. The already-ACCEPTED `uniform_three_sum_transfer` theorem concludes
this exact `EndStatement.ThreeSum.SolvedInTime` predicate from uniform Exact
Triangle; its conclusion therefore covers `κ=0` and the small sizes as well.
These quantifiers are retained in the final composition, rather than added
as a separate assumption.

## Final closure readback

The subsequent platform readback marks `cost_regime_solve_3sum`
(`421030db-0ca7-4fd3-af76-166d00b6be18`), the original
`admissible_parameters_solve_3sum`, and `threeSum_1999017`
(`1674355a-fcd8-4885-8ec3-cc3e1ff29624`) all Proved. The completed native Lop
proof was ACCEPTED as `49135b57-ab3c-4e69-bd0b-28456716f7fb`; the exact
cost-regime composition was ACCEPTED as
`5a8578d3-cb3d-486b-9224-93424d75083f`.

The proof-bearing Solution files contain the actual program, resource,
correctness, runtime, and inherited-reduction compositions. The theorem
reference files retain `by sorry` as the platform's specification interface;
these reference templates are distinguished from complete proof sources.
The final graph audit verifies 43 actual child/submission/parent paths and
25 accepted supporting proofs, with no remaining frontier. The registered
29-root-module build completed with exit 0 (8850 jobs), and its solution
source hashes were unchanged during the build.

The exact numerical and source/type audit above remains a static audit.
Completion evidence is supplied separately by the saved ACCEPTED verdicts,
Proved theorem snapshots, dependency graph, and local build records.
