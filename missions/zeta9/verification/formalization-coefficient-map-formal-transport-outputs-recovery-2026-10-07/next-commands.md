# Outputs author recovery, 2026-10-07

The original pure preparation is intact. The new recorder rehashed all 129
binding occurrences (102 unique paths) and all 54 original SHA256SUMS entries.
Every comparison passed. The first recorder metadata failure was corrected
only in this new recovery script and is retained in pure-recorder-attempt-01.json.
The recovery is an author check, not an independent review or a Lean PASS.

The original SOURCE-only project is `.rt/oa1`. No `.rt/ga1` project was prepared
for this batch. Build directory `b`, package link `.lake`, compile receipt,
actual runs and Root lane grant are all absent. The maximum future object path
plus the required 64 characters is 214. No author, independent, Root or tj1
proof object exists in this project.

The shared Outputs source has 12600 bytes and SHA256
`f16dc8be54bd58c09f240ed3404ba3810297e1a8e9d9ab9806893d410862f09d`.
All 16 original complete text headers agree with endpoint-contracts.json and
preparation-state.json. These are text comparisons, not actual Lean types.
All 21 actual source origins, initial private copies and immutable snapshots
match. Their full hashes and origins are in actual-source-hashes.json.

The Jets origin, private compiler input and immutable snapshot all use
`ccef5eaf7bad1b86ce8da45401b2ed3d5bb28e55aafc2626a92d4fc2a4cf4c02`.
The original shared failed b081 candidate is preserved and excluded from
the planned compiler inputs. Serializer/validator and recorder reuse is
SOURCE reuse with provenance retained, not proof-object reuse.

The three exact primary statements remain:

```lean
theorem actual_chosen_constantTerm_transport (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    constantTerm (n + 2) (X ^ r.val) = constantTerm n (connectionP n r)

theorem actual_chosen_five_output_transport (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    aggregate (n + 2) (X ^ r.val) = aggregate n (connectionP n r)

theorem actual_five_output_matrix_transport (n : ℕ) (hn : 1 ≤ n) :
    actualFMatrix (n + 2) = connectionGamma n * actualFMatrix n
```

The finite B proof keeps the signed correction
`-oldPF(1)+shiftedQPF(1)`. The old value vanishes by the true positive-root
factor, and the shifted remainder value vanishes by its true numerator factor
at t=2. It does not infer R_1(2)=0. Degree4 for actual P and degree9 for actual q
give the needed strict properness for the existing PF theorems. The final
matrix proof uses left Gamma multiplication. No Even, PF-existence, transport,
invertibility, zeta-independence or infinite-summation premise occurs in these
three headers. All nine rho transports are consumed from the verified Jets
source. The original 588 rational prechecks at n=1,2,3,6 remain finite checks.

No Lean/Lake/API was run during this recovery. A serial author lane must first
be granted by Root. Root must then add the new grant file
`verification/formalization-coefficient-map-formal-transport-outputs-preparation-2026-10-04/Root-lane-grant.json`,
binding the lane, original preparation and exact source. Do not execute
the following command before that grant.

From `D:\users\self_projects\prove2me_workspace\missions\zeta9`:

```powershell
& 'C:\Python314\python.exe' verification/formalization-coefficient-map-formal-transport-outputs-preparation-2026-10-04/execute.py --lane-granted
```

The current interpreter was read-only verified as Python 3.14.7. The managed
restricted shell cannot resolve it correctly; use the already authorized
runtime prefix with an exec sandbox escalation when running this command.
That runtime check and the mandated task file inventory both exited 0.

The original runner links only the fixed root `.lake/packages`, compiles all
21 native SOURCE files freshly in its own cache, compiles four source controls,
and checks 25 own-object resolutions. Its 27 planned calls comprise runtime,
21 native source compiles, four controls and one resolver. They are planned
counts, not actual invocations. The four controls contain the two serializer
programs, all 16 exact source/expected kernel/type/axiom/DAG comparisons, and
nine closed boundaries. Retain every real attempt's inputs, selected paths,
logs, exit and partial objects. Any repair starts only after a retained real
failure and preserves original complete headers and frozen source snapshots.
Fresh successful execution still requires a full author audit/freeze and an
independent native review before any publication claim.
