# Public mission: formalize the abstract layer of "Research Notes on ζ(9)" (v0.1)

The public counterpart of the private ζ(9) mission. It carries the **abstract layer only** —
nothing here mentions ζ(9) — under the namespace `Zeta9Note.*` (the private mission uses
`ZetaNine.*`, so the two never collide).

Platform state (read back 2026-09-25):

| field | value |
|---|---|
| proposal id | `00d787d8-91c8-45bf-87f0-6a5e9e8bc472` |
| mission id | *empty* — the proposal is `In review`, awaiting moderator approval |
| visibility | `public` |
| goal | `Zeta9Note.irrational_of_small_nonzero_integer_forms` |
| items | 8 (1 goal + 1 stronger variant + 6 supporting), 7 milestones |
| theorems | 8/8 `Proved`, 8/8 submissions `ACCEPTED` |

## The eight items

| local id | theorem | kind | submission |
|---|---|---|---|
| `Z9N.ONE` | `irrational_of_small_nonzero_integer_forms` | goal — one-form criterion | `778c9c7e…` |
| `Z9N.TWO` | `irrational_of_two_small_integer_forms` | stronger — two independent forms | `4ebdf8ab…` |
| `Z9N.QUAD` | `quadrature_exact_of_moments` | moment matching ⇒ exact on degree ≤ 4 | `b8939099…` |
| `Z9N.AVG` | `min_lt_weighted_average_lt_max` | weighted average is interior | `590b79ef…` |
| `Z9N.MED` | `mediant_strictly_between_min_and_max` | mediant is interior (reduces to AVG) | `e6a13c32…` |
| `Z9N.CONE` | `positive_matrix_maps_nonneg_to_pos` | positive matrix on nonzero nonneg vectors | `e475cc2e…` |
| `Z9N.TSUM` | `taylor_sign_implies_kernel_sum_pos` | nonnegative Taylor coefficients ⇒ positive sum | `6ab693ce…` |
| `Z9N.SIGN` | `five_sample_sign_forces_nonzero` | five-sample nonvanishing (reduces to QUAD) | `7061a724…` |

Full ids, theorem ids and solution hashes: [submissions-receipt.json](submissions-receipt.json).

## Reproduce / audit

```bash
py=.../python.exe
"$py" missions/zeta9/roadmap/platform/public-proposal/build_public_proposal.py --status
"$py" missions/zeta9/roadmap/platform/public-proposal/submit_solutions.py --check
"$py" missions/zeta9/roadmap/platform/public-proposal/submit_solutions.py --poll
```

`--submit` refuses unless the mission is live; pass `--allow-pre-approval` to post onto the
compiled theorems while the proposal is still in review (that is what this run did).

Local compile of all eight proofs, plus the combined file in the public repository:

```bash
lake build Theorems.Thm_Zeta9Note_quadrature_exact_of_moments \
            Theorems.Thm_Zeta9Note_min_lt_weighted_average_lt_max
for f in missions/zeta9/roadmap/platform/public-proposal/solutions/Sol_Zeta9Note_*.lean; do
  lake env lean "$f" || echo "FAILED $f"
done
lake env lean "D:/users/self_projects/zeta9-research-notes/formalization/Zeta9Note.lean"
```

All nine runs exit 0 with no `sorry`.

## What this does *not* say

The eight theorems are general statements about real numbers, integer linear forms, real
polynomials and finite sums. Proving them is **not** a step toward the irrationality of ζ(9);
the concrete construction ($F_n$, the saturation kernel, the Smith data, the weighted areas,
the congruence-lattice minima) still has no Lean definitions, and the private mission's root
`ZetaNine.irrational_zeta_nine` remains `Open`.
