# Isolated standalone-node variant — 2026-10-08

New files only: `scripts/private_inline_binding.py` and
`scripts/generate_platform_nodes_isolated.py`. The accepted generator,
publisher, manifests, source, oracle and global inventories/plans were not
modified. The original accepted Collision statement/proof bytes still match
their saved hashes.

`inline-provider-collision-audit.json` and `.md` preserve the complete 799-module
plan audit, including 84 collision nodes, 22 consumers missed by the direct
guard, 24 private-inline refusals, all 326 shared public declaration names, and
three statement-required helper names. They include original declaration
ranges/scopes, provider DAGs, graph rows and selected authoritative reference
facts. The JSON is intentionally complete; use targeted JSON queries instead
of loading its approximately 41 MB into chat context.

The narrow variant supports one same-file standalone public target and atomic
ordinary proof-only inline theorem helpers. Each helper gets a stable alias
derived from the node name, source module, graph declaration and binding
range. A new private modifier is inserted at the authoritative theorem token
after any attributes/wrapper; an existing private modifier is preserved.
Binding and use edits select one oracle binding identity within that source
file. Original private prefixes are never joined across files by spelling.

Mixed/reassoc commands, public interface/Definitions-required helpers,
unavailable graph/syntax dependencies, child nodes, Definitions, cross-file
components and target/global renames are explicit pending refusals. The
interface guard includes exported node type-dependency roots and Definitions'
full dependency closure; the three known statement-helper exceptions are
guarded. No global classification is changed.

Generated Thm, Sol and Generated Snapshot include an inline `run_meta`
collector. It scans actual Environment constants, matches the generated alias
using `privateToUserName?`, restricts candidates with
`getModuleIdxFor?.isNone` (OwnModule), requires one theorem with closed
type/value, and checks its actual axiom Names against Std3. It emits actual
kernel names, ownership, type/value constant references and axioms as one
`PI_ISOLATED_PRIVATE_MAP` JSON stdout message per artifact. There are no public
collector definitions, fabricated private prefixes or local output-path
writes in the upload text. Local snapshots additionally export original and
generated helper types/values to separate JSON files.

`recover_private_maps(manifest, four_preflights, ROOT)` is a read-only postcompile
helper. It requires complete exact-file preflights/log hashes plus current
input/implementation/core/runtime/original/port/AST pins, checks the three
unique OwnModule map messages and all original binding identities, and returns
the per-artifact actual-name maps. Name recovery alone does not certify types
or publication: its returned validated/submission/full-tree flags remain false.

The future context hook accepts explicit commands, namespace body opens,
optional closing text and AST evidence. Thm/Sol close restored sections after
their declaration; Generated Snapshot closes after both declarations and
before inserting the snapshot core. A synthetic section hook passed in-memory
exact-concatenation/closing placement checks. `restore_node_context.py` has not
been integrated yet, as requested.

Pure Python preview results:

- Collision `sum_weight_ge_of_low_count_le`: one private helper alias,
  `_p2m_inline_c51cd00f11b0c794269f`, in the original Collision namespace.
- `log_norm_sum_le`: zero helpers.
- FormalLogTruncation `logTail_mem_rationalWeightedIdeal`: whole-node generation
  refused because it requires Definitions/child nodes.
- FormalLogJet `coeff_liftSeries` fragment: two consumers receive distinct
  aliases; `@[simp]` stays intact and private is inserted at byte 518, not 510.
- Original private `ExceptionalRecoveryMap.intersection_one`: unique binding
  identity verified, renamed without removing or duplicating its private token.
- Reassoc command and the three statement-helper guards are exercised.

The two real samples are under `verification/nodes-isolated-preview/`. Their
exact output hashes, manifest statement concatenation and implementation pins
were checked. They are still provisional/unvalidated, with private kernel names
pending actual compilation. No Lean, GET or POST was run by this agent, and no
full-root readiness is claimed.
