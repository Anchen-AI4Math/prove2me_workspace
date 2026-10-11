# Independent-node and Definitions-generator audit

Date: 2026-10-08. This audit ran Python and file inspection only; it did not run Lean or make platform requests.

## Independent-node fixes

The three independent-node scripts now pin the two snapshot inputs, the kernel serializer, declaration graph, source AST facts, original source bytes, port source bytes and captured Lean runtime. Validation reconstructs and compares the complete statement, solution and both snapshot inputs. The reconstructed statement/preamble is the same text sent to submit-problem. Lean files are written as UTF-8 bytes, avoiding Windows newline translation of original CRLF fragments.

Four preflight certificates must identify their exact staged file, current SHA and captured runtime. Both timeout and measured seconds must be positive and at most 300. The validation document binds both exported type JSON files, exact upload hashes and log hashes. Publication rechecks these certificates. Exact-name lookup pages through all results; recorded publish/verify intentions still prevent automatic retry after an uncertain POST.

Python syntax checks and an in-memory reconstruction case containing CRLF passed. Changing the generated snapshot or the manifest statement was rejected. The captured runtime executable/configuration hashes were checked against the actual files.

The existing independent generator flattens surrounding namespaces into a root-level statement and solution. This can change unqualified resolution; its standalone compilation and exact kernel-type comparison remain mandatory. The inspected log_norm_sum_le theorem has explicit binders and an open-scoped BigOperators context, with no project declaration in its complete kernel dependency closure. No namespace-dependent project binding was identified in that theorem's statement or proof.

The Original snapshot imports the source module's compiled olean. Runtime pins and source SHA checks do not independently pin every imported olean. Thus the source-build and source-cache provenance supplied by the earlier complete build remains part of the comparison's trusted input. This audit did not reproduce that build.

## Definitions bundle generator

Added scripts/generate_platform_bundles.py. It recomputes the unit and artifact plans from their current graph/inventories and rejects stale plans. Final mode requires complete extraction of all 875 modules, reviewed non-provisional ready plans, unambiguous public names, verified explicit overrides and currently validated canonical-definition reuse. Every manifest records hashes of its input plans/inventories, source AST facts, original source and port source.

Generation uses declaration_edits, import_edits and rename_bound_constant on the same original byte coordinates, followed by one apply_edits call. Definitions retain their complete proof bodies. All surrounding namespace/section/end, variable/open/include/omit, local-instance and supported notation/attribute commands are retained at their original positions. Unsupported context command kinds are rejected. Private names are connected by their binding ranges within their own source file; an unresolved or ambiguous identity is rejected. Retained syntax referring to a removed or unplanned project declaration is rejected. Statement is skipped in favor of Definitions.Def_OAI_PiExponent_ApproximationDefinitions, and planned consumers route their import to that canonical module.

Five preview bundles passed the generator's independent forward/reverse byte reconstruction and subsequent Python hash checks:

| Source module suffix | Retained units | Output bytes | Local instances |
| --- | ---: | ---: | ---: |
| Analysis.Collision | 1 | 1218 | 0 |
| Analysis.AnalyticCollision | 3 | 1474 | 0 |
| Approximation.TensorPure | 19 | 20290 | 1 |
| Cohomology.CechOneConverse | 2 | 11990 | 1 |
| Cohomology.FiniteCoverCohomology | 100 plus 1 elaboration helper | 72111 | 5 |

Outputs are in verification/bundles-preview/Definitions. They preserve source hashes and contain no placeholder insertion edits. Every manifest explicitly has validated=false and submission_ready=false; these are structural previews, not compiled deliverables.

The following real cases were rejected rather than weakened:

- ExceptionalAffineChartRestriction and ExceptionalRepresentedOpaque: transitive project import facts were still pending, so their two proposed schemeFreeOpen renames were not generated.
- FiniteCoverCohomology initially rejected a source syntax reference to the removed mapFrom_apply. Further inspection corrected the initial context classification: its two references are inside the retained mapFrom_mk₀ and mapFrom_comp theorem proofs (lines 926 and 932), not an attribute command. Its exact original lemma (lines 921–922, bytes 43891–44036) has AST value bytes 44030–44036 equal to := rfl, and its only project kernel dependency is the already retained mapFrom definition. This narrow case is now preserved as a complete source command, with no change to the planner's classification.
- ReesProductSchemeChart:1847 initially rejected an anonymous private instance without nameRange/verified_name. The generator now integrates rename_anonymous_instance.py for the recognized atomic private local instance form: its graph userName supplies the stable public name, the recovered source namespace must agree, and the same-file oracle binding range must cover the original instance keyword. Unsupported anonymous forms remain rejected. The complete ReesProductSchemeChart bundle still rejects generation while its transitive project import facts are pending.
- Final invocation with partial extraction: rejected at the 875-module gate before output generation.

Other unresolved cases are returned in preview's rejected list. Generated Definitions still need compilation within 300 seconds, standard-axiom auditing and definition/consumer kernel-type comparison. Neither this script nor this audit marks a bundle publishable.

## Narrow source-elaboration helper rule

The generator now permits a same-module deleted theorem to be retained solely when authoritative reference ranges inside retained declarations require its name, its command owns exactly one public ordinary theorem, its source binding is unique, its scope and wrapper ranges agree, it has no scoped wrapper/private/local-instance complication, and its complete AST value suffix normalizes only by whitespace to exactly := rfl. Every project constant in its full kernel type/value/constructor dependency closure must already belong to the accessible Definitions closure. No missing theorem is promoted into the planner and no theorem placeholder is imported. All other missing syntactic references remain rejected.

The manifest's elaboration_only_helpers field records the complete original command/value ranges, both consumer reference ranges and the exact project dependency list. For FiniteCoverCohomology it records one helper and retains five original local instances. Python rejection tests changed the six-byte AST value suffix from := rfl to := foo and added an escaping project kernel dependency; both were rejected. No attribute-cropping rule was introduced because the actual case does not contain the purported attribute command.

## Anonymous-instance integration

The recognized ReesProductSchemeChart instance now resolves to OAI.PiExponent.ReesProductPowerSections.instIsOpenImmersionFChartCover. The integration's Python test confirmed the name is no longer a pending-name error, the same-file binding identity is _private.0.OAI.PiExponent.ReesProductPowerSections.instIsOpenImmersionFChartCover, exactly two AST edits are returned, the original local token remains present after offset adjustment, and the source file is unchanged. The insertion is at byte 1869 after the instance keyword; only the private token is removed. The per-rename manifest includes the helper's complete binding/edit record. Implicit typeclass uses have no lexical reference range to rewrite and still require re-elaboration plus source/generated kernel-type comparison. No Lean or type validation is claimed.

Both bundle and node generators subsequently integrated the fixed upload route and three ordinary public _source017 theorem overrides. Details and real same-file/external reference checks are recorded in platform-node-generator-audit.md. The original root and all source Definition/Parameters names remain unchanged, and the three community adapter Definition imports are excluded. Source override re-elaboration/type flags remain false.
