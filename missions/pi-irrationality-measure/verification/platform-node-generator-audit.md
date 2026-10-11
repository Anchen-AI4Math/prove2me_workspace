# Node staging generator audit

Date: 2026-10-08. Added scripts/generate_platform_nodes.py; no Lean, platform request, oracle edit, source edit, inventory edit or official bundle output edit was performed.

The generator consumes the authoritative artifact/unit plans through the existing Definitions generator's freshness and name gates. Final mode inherits the complete-875, reviewed-plan and validated-override requirements. Preview remains provisional and never marks an artifact validated or submission-ready.

Source components are ordered by their actual unit dependencies. Original parser byte ranges select retained inline commands and subtract only whole declaration/import commands; every source component retains its namespace/section/context skeleton inside an isolating section. Supported narrow := rfl elaboration helpers use the existing sanctioned helper logic. Ordinary non-rfl missing syntax dependencies, private inline identities, component/helper name conflicts and unhandled context commands are rejected.

The target is now hoisted after every source component scope closes. The statement is theorem <full-platform-name> and the proof is a literal top-level theorem solution, complying with root SKILL.md line 104. The earlier _root_.solution-inside-namespace variant was corrected; a globally qualified name did not satisfy the required source shape. Active open/variable/universe/include/omit commands are replayed from their AST ranges at root in original order. Namespace and section openings are not replayed around the target. Wrapper include/omit/open commands are hoisted consistently for statement and solution.

The proof's authoritative := boundary is translated through the header-edit ledger, then a local open <namespace-prefixes> in term is inserted there. This restores the original namespace and its parent-prefix lookup in the proof body without wrapping theorem solution in a namespace. Original section frames, local notation/attributes/options and other complex active contexts are rejected pending a reviewed top-level transformation. Authoritative project constant references in the target declaration header and simple active context now receive their full original or mapped public names; fvars are not edited. A single original-coordinate edit pass composes these reference changes with the binding/docstring/wrapper/keyword changes, so header offsets are never reused against already edited text.

Moved Definitions local instances are emitted as attribute [local instance] <stable-public-name> at the original command's byte range within the preserved source skeleton. Instances active at the target are also replayed in the original order and source scope, using their source offsets among the reopened namespace/section/context commands. They are not promoted to global instances. All required Definitions imports, including their transitive package closure, must have current kernel/standard-axiom and strict 300-second certificates, or the stage is rejected. The already validated canonical Statement bundle is routed to its existing module.

Every node manifest records source/AST/graph hashes, original source hashes and commit, plan/inventory hashes, generator hash, runtime/core hashes, exact statement/solution bytes and two pinned kernel-type snapshot inputs. A recorded source-to-platform constant-name correspondence does not itself establish type equality. All four Lean files, exported types and axioms remain pending independent validation.

Pure-Python preview generation succeeded for:

| Node | Components | Inline units | Thm bytes | Sol bytes |
| --- | ---: | ---: | ---: | ---: |
| OAI.PiExponent.DeterminantAnalyticBound.log_norm_sum_le | 1 | 0 | 1606 | 2531 |
| OAI.PiExponent.Collision.sum_weight_ge_of_low_count_le | 1 | 1 | 2217 | 2930 |

Both stages are under verification/nodes-preview. Python checks confirmed exact preamble/formal-statement and preamble/solution reconstruction, file and snapshot hashes, source hashes, literal theorem solution, no namespace or section in the replayed active context, and validated=false/submission_ready=false. Both active contexts contain only open scoped BigOperators. Their proof terms respectively use open OAI OAI.PiExponent OAI.PiExponent.DeterminantAnalyticBound in and open OAI OAI.PiExponent OAI.PiExponent.Collision in. This is source/byte verification, not Lean compilation or kernel-type validation. The term-local open syntax was inspected in the pinned local Mathlib sources, not tested through Lean here.

Negative-path observations:

- uniform_margin_of_affine_curve_data rejected because AdmissibleBlowupGeometry has no final validated Definitions manifest.
- Final invocation rejected at the incomplete-875 extraction gate before staging.
- pi_eventual_lower_bound was absent from the partial artifact plan and was rejected as an absent node selection; it was not invented from text.

Current conservative limits are explicit: private inline declarations need a validated name correspondence; child Theorems exporting a same-named inline helper are rejected. Definitions-consuming nodes and restoration of local instances have not been exercised through Lean. Original snapshots import the earlier built source olean, whose complete-build provenance remains an input; this script does not rebuild or individually hash the complete imported olean closure. Full-tree generation and platform submission readiness are not established by these two previews.

## Fixed source route and ordinary public theorem renames

Both generators now load platform/upload-route.json and platform/source-theorem-name-overrides.json, pin their input hashes and require the fixed declaration-graph hash. Plans must target only OAI.PiExponent.pi_eventual_lower_bound. The three public overrides are restricted to ordinary public non-instance theorems, preserve their original namespaces, have distinct ASCII names that do not collide with the source graph, and cannot rename the root. Definitions/Parameters names and canonical six-definition Statement reuse are preserved. Any direct generated import, or a consumed Definitions certificate's import list, containing the three excluded community adapter modules is rejected.

The ordinary source theorem binding and same-file references use the existing rename_bound_constant helper; bindings receive the new leaf, references receive the full mapped name. Imported full graph identities are rewritten to that same mapped name. Node names and child module filenames use the shared map. Same-file abbreviated private IDs remain resolved by their own binding ranges, with no cross-file join by spelling.

Pure-Python checks confirmed the following original binding/same-file edit counts with source unchanged:

- exists_admissible_parameters → exists_admissible_parameters_source017: 1 edit.
- DeterminantContradiction.actual_minor_arithmetic_lower_bound → corresponding _source017 leaf: 2 edits.
- DeterminantContradiction.tendsto_collisionRate → corresponding _source017 leaf: 2 edits.

Real external reference samples were rewritten by authoritative ranges: exists_admissible_parameters in AdmissibleDeterminantSequences and DeterminantContradiction (1 reference each), and the other two theorems in DeterminantSequences (1 reference each). These checks did not mutate source files or establish Lean/type correctness. A combined header/binding edit on the original exists_admissible_parameters theorem qualified its AdmissibleParameters header reference while preserving literal theorem solution. The root mapping remained unchanged, and all three excluded adapter import names were rejected.

The two independent node previews still generate under the revised route. exists_admissible_parameters remains rejected at the unverified-Definitions gate; this test did not weaken that gate to expose a renamed stage. The public override flags remain unvalidated until re-elaboration and kernel-type checks pass. No Lean or platform request was run.
