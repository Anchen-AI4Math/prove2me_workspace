# Private definition support and command-emission evidence plan

The isolated provider-node implementation now supports one named source-private
ordinary `def` or `abbrev`, as well as the earlier ordinary theorem case. It
preserves the exact original private/noncomputable/other modifier bytes. It
selects the def/abbrev keyword and declaration binding from their parser AST,
verifies full namespace and source Graph identity, and rewrites only the
binding and authoritative same-file/cross-component references.

`scripts/private_node_binding.py` collects actual unique OwnModule private CI
names via `privateToUserName?` and `getModuleIdxFor?`; it checks closed types,
closed definition values/proofs, exact CI kind and Std3. Source private CIs are
selected by actual imported environment names. TypeOnly snapshots export null
theorem proof values and complete nonnull definition values.

`compare_private_ci_snapshots` requires a certified, artifact-specific actual
environment map. It maps original Graph private constant Names to actual
generated kernel Names only in structural kernel constant/projection positions,
and normalizes bound universe parameter names. It compares complete definition
values, rejects missing/null def values and unvalidated maps, and ignores
prettyType strings. Its caller must certify the exact preflight/runtime/input
pins; synthetic fixture maps are not actual compilation evidence.

The real `CechOneConverse.schemeFreeOpen` source command is `private abbrev`.
Its AST binding and two reference edits passed offline checks; eight negative
fixtures rejected opaque/instance/missing-private/ambiguous-binding/namespace
errors and uncertified/null/changed kernel-value evidence. See
`private-definition-binding-ast-qa.json`.

## Cech's next actual boundary

With the new runtime captured after the controlled stage-root registration,
regeneration passes `schemeFreeOpen` and rejects the retained context reference
to `higherCochainAddCommGroup`. This is an ordinary private def, not an instance
command: raw AST unit `CechH1Transfer:797`, lines 25–29, carries
`@[instance_reducible] private def`. Its original source command is absent from
the kernel-reachable plan; the retained `attribute [local instance] ...` at
lines 31–32 needs it. Its value references compiler-generated private def/proof
CIs with no AST command owner. No prefix-based ownership or guessed private
number is accepted. The Cech four-file stage remains ungenerated.

Opaque, instance/structure commands and exported target/public-inline interface
types requiring private helpers remain explicit refusals. Source-private helper
types/values also need complete actual dependency-name maps when they refer to
unowned private auxiliary CIs; a main binding map alone cannot prove equality.

## Prepared exact-command provenance probe

`scripts/prepare_command_emission_probe.py` stages two files under
`verification/command-emission-probe`, without changing the original
SketchOracle, extraction state, global inventories/plans, or accepted files:

- `CommandEmission.lean`: copies the complete original legal source prefix and
  exact AST command bytes; captures the actual environment Name set immediately
  before the command and exports every new actual OwnModule declaration after
  it. The delta uses a HashSet of Lean.Name values, not printed names or suffixes.
  The unique primary private user-name is checked. Every emitted def/theorem CI
  has closed type/value or proof and Std3; theorem proof values remain null.
- `SourceOriginalSnapshot.lean`: imports the original module and exports 19
  actual private CIs selected through authoritative Graph type/value edges from
  the primary source definition. Exact imported owners are checked. Def values
  are complete; theorem proof values are null.

`probe-plan.json` binds the exact source command range/hash, copied prefix hash,
original/port/AST/graph/core/runtime/script hashes and pinned Lean API source
hashes. `pure-python-qa.json` verifies exact command bytes, scope closure and all
pins. Both files are uncompiled, and no auxiliary availability was granted.

Pinned `BuiltinEvalCommand.lean` evaluates `run_meta` only after restoring its
temporary elaboration environment (`withoutModifyingEnv`, lines 230–247), so the
Name-set delta is not based on evaluator temporary declaration prefixes. Runtime
evidence must still confirm the emitted Name set. Both probe files require
strict separate preflights within 300 seconds and preserved logSHAs. Missing
original project dependency OLeans cause rejection. A generated provider/node
alias command must repeat the command delta probe and pass actual CI type/full
Def-value correspondence before auxiliary source/generated Name maps or
availability can be certified.

The offline context audit covers the current 224-node complete provider plan. It finds
one node needing one additional private def command: Cech's
`SectionComparison.cohomology_one_zero` active local-instance attribute needs
`higherCochainAddCommGroup`. Exact reference/context/definition ranges and its
unowned direct project dependencies are recorded in
`command-emission-probe/source-node-context-closure-cases.json`. The audit is
limited to named ordinary private defs in retained nondeclaration context; it
does not claim coverage of macro-emitted or anonymous/private instance cases.

No Lean compiler or HTTP request was started. Provider-node source is frozen at
this increment; all previews remain unvalidated and not submission-ready.

## Actual probe failures and isolated repair

Root's first `CommandEmission` attempt failed after 40.6847453 seconds with
exit code 3221226505: Lean cannot evaluate the same-module initialized
`savedNames` declaration. Root's first `SourceOriginalSnapshot` attempt failed
after 52.4929 seconds because the unused private-user-name filter had an
ambiguous pipeline/equality precedence. Exact old sources, builders, plans and
logs are archived under `command-emission-probe/failed-attempt-20261008-113319`
and `failed-attempt-20261008-113902`, each with a SHA witness manifest.

The repaired probe has no initializer or global state. One `run_cmd` captures an
ordinary local actual-Name HashSet, calls `Lean.Parser.runParserCategory` on the
exact source command string, checks its parser kind against the original AST,
elaborates it via `Lean.Elab.Command.elabCommand` in the copied active source
context, then exports the actual Name delta. Runtime parsing avoids quotation
hygiene altering the source binding. The original command string has an exact
UTF-8/CRLF round-trip byte check against the authoritative source range.
The optional private user-name predicate is explicitly parenthesized.

Both repaired source files and `probe-plan.json` were regenerated; the 19
original SourcePrivateCI requests are unchanged. `pure-python-qa.json` verifies
all hashes, one atomic command action, absence of initializers, scope closure
and exact command literal bytes. Neither repaired file was compiled by this
agent. No availability or validation claim follows from the repair.

## Final isolated probe and existing-evidence certifier

The third failed command probe (36.6762 seconds) is preserved in
`command-emission-probe/failed-attempt-20261008-114924`. Its reserved `syntax`
binder is replaced by `parsedCommand`; namespace closers now come from the
reversed authoritative scope stack, with anonymous sections closed separately.
The successful original snapshot (exit 0, 54.6130264 seconds) is archived in
`successful-original-20261008-115313`; its exact source SHA remains
`85f1cdec7d26cc6b24dda9019023cbded3b942800696d840a8fcc3dba220848b`.

The new probe has three files. `CommandEmission.lean` records the exact atomic
command's actual Name-set delta. Separately, it exports twenty actual prior
OwnModule private CIs selected by unique `privateToUserName?` identities for
the copied `schemeFreeOpen`, `schemeUnit`, and `freeOpenHomAddCommGroup` prefix
closure. `SourcePrefixSnapshot.lean` requests the corresponding original
imported CIs. The existing `SourceOriginalSnapshot.lean` still requests the
nineteen CIs in the target command's original private closure. Prefix CIs are
never attributed to the target command's emission delta.

`scripts/certify_command_emission_probe.py --certify-existing` requires exact
current source/input/API/OLean/runtime pins and all three successful preflight
records, each within 300 seconds, with preserved record/log hashes. It checks
closed structural CI types, complete definition values, null theorem values,
Std3 axioms, exact request domains, actual owning modules, and unique actual
private-user-name mappings. Source-to-probe kernel Names are mapped only from
those actual environment identities, then types and definition values are
compared after that Name mapping and universe-binder normalization. Changed
definition values, free/loose variables and undeclared universe parameters
are rejected by pure Python fixtures.

The final offline check passed with 19 original and 20 prefix requests. The
final command/source-prefix hashes are recorded in `probe-plan.json` and
`pure-python-qa.json`; the successful original bytes/output remain unchanged.
Actual command emission and prefix snapshots remain pending root's serial
compiler. A source provenance certificate alone does not prove generated
provider availability: the generated alias command must repeat the same
actual-delta and type/full-value validation. All submission flags remain false.
