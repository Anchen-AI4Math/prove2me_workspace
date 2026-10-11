# Provider node generator: offline increment

`scripts/generate_platform_provider_nodes.py` consumes the independently rebuilt
all-shared-public provider variant through `ProviderGenerator`. It writes only
`verification/provider-nodes-preview`; accepted nodes, original generators,
publishers, original sources, oracle, and global plans were not edited. No Lean
process or HTTP request was started. All generated nodes remain provisional,
unvalidated, and not submission-ready.

## Concrete output and Python checks

Four samples have exact Thm/Sol/SnapshotOriginal/SnapshotGenerated source files:

- `DeterminantAnalyticBound.log_norm_sum_le`: standalone, no helper.
- `Collision.sum_weight_ge_of_low_count_le`: standalone, one original public
  inline theorem retained. The existing accepted copy is unchanged.
- `FormalLogTruncation.logTail_mem_rationalWeightedIdeal`: three planned Def
  dependencies and one child dependency, all explicitly unvalidated witnesses.
- `LocalIntersection.regular_ring_onecut_length`: one source-private ordinary
  theorem gets a per-node binding-specific alias; four planned Defs and one child.

`provider-nodes-preview/pure-python-shape-qa.json` records exact Thm/Sol byte
reconstruction, all four file hashes, all current input and implementation pins,
literal top-level `theorem solution`, restored scope closure, and public-binding
collision checks for each sample. These checks do not validate Lean syntax or
kernel types. No actual private kernel names have been invented or recovered.

## Binding and scope invariants

The source is edited at original parser ranges: only whole declaration commands
and imports are subtracted; retained namespaces, sections and context remain.
The target is removed from its original position and hoisted after component
scopes. `restore_node_context.restore_context` restores active variable, open,
include/omit, notation, attribute and section commands in source order. Moved
local instances become local attributes at their original source position and
are replayed only when their original scope is active for the target.

Source-private ordinary theorem helpers use unique node + source module + graph
name + binding-range aliases. Same-file abbreviated private references resolve
through authoritative binding ranges; foreign references require full graph
identity. Dotted declaration bindings retain their namespace-relative prefix;
quoted/root-qualified ambiguous binding spellings are rejected. The collector
requires a unique actual `privateToUserName?` match belonging to OwnModule via
`getModuleIdxFor?`, then checks its closed CI and Std3. Actual maps remain null
until the generated files compile and their collector output is certified.

Public inline units, including complete `@[reassoc]` command companions, retain
their original names. The entire import closure inventory includes every
retained public graph name and every extra elaboration-only rfl helper in both
node and Definition skeletons. Any duplicate provider is rejected. Public CI
snapshot requests enumerate all ordinary and generated companion graph names;
actual environment ownership, theorem kind, closed type and Std3 must pass.
Snapshots use `TypeOnlyTheoremSnapshotCore.inc`: theorem proof values are null.

Dependencies carry pinned original/port/AST source witnesses and planned module
identities. Their presence in the plan grants no certificate or actual OLean.
Actual imports, four bounded preflights, types, axioms, name maps and publication
review all remain required.

## Main remains strictly blocked

Main's public unshared mixed inline command
`GlobalBlowupAffineSquare:798`, lines 24–34, owns
`totalChart_projection` and `totalChart_projection_assoc`. It is preserved as one
full source command; no guessed reassoc name or private transformation is used.

After permitting that complete public unit, Main reaches the concrete refusal
in child `FormalLogTruncation:17060`: syntax needs public rfl
`FormalLogTruncation.shiftEquiv_apply`, whose kernel closure includes
`FormalLogTruncation.shiftMap.eq_1`. The equation graph row has zero source lines,
no command owner, and is not in `preserved_generated_commands`. The existing
`shiftMap` Definition command is retained, but its name prefix alone cannot
certify the equation relationship. Main has no staged files and is not ready.

The separate Cech sample rejects private `def schemeFreeOpen`, unit
`CechOneConverse:2490`. This increment supports private ordinary theorem aliases;
private noncomputable/abbrev/def value correspondence is explicitly pending.
Mixed target theorem commands remain rejected; the planned whole-command
provider overlay is a separate planner change.

Full source ranges, DAG-plan and graph pins for these boundaries are in
`provider-nodes-preview/boundary-evidence.json`. Exact run outcomes and pins are
in `provider-nodes-preview/generation-report.json`.

## Equation provenance probe, staged only

`scripts/generate_equation_provenance_probe.py` stages paired original/provider
probes in `verification/equation-provenance-probe`, with their byte hashes,
primary source command, AST/graph/runtime/core/API-source pins and certification
policy in `probe-plan.json`. Neither probe was compiled.

Pinned Lean 4.33.1 `Lean/Meta/Eqns.lean` lines 255–258 implements
`getEqnsFor?` with the definition's recorded equation-affecting options; lines
211–212 exposes `isEqnThm?` as the exact inverse primary relation. Lines 312–330
implements `getUnfoldEqnFor?`, with its nonrecursive default recorded separately.
The original and provider probes query the same primary `shiftMap` source
binding, enumerate actual returned equation Names and inverse primary links,
export each closed equation CI type and Std3, and export the primary complete
Def value and type for exact comparison. The primary imported module is checked.
Equation ownership is recorded exactly, including OwnModule lazy realization;
it is never inferred from a suffix or module prefix.

Before compiling, hold extraction and recheck captured pins; the generated
provider's exact source/OLean/certificate and full import closure still need
binding. Both probes must separately finish within 300 seconds. Only actual API
membership, source/provider CI type equality, complete primary Def value
equality and Std3 can establish the generated equation's availability. No
equation availability was added to the planner or node generator by this plan.
