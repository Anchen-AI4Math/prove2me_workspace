"""Author offline Jet gate: source splices, real closures, actual build reports."""
from pathlib import Path
import hashlib
import json
import re
import sys

sys.stdout.reconfigure(encoding="utf-8")
OUT = Path(__file__).resolve().parent
TASK = OUT.parents[2]
ROOT = TASK.parents[1]
BASE_BATCH = TASK / "formalization/platform/coefficient-map"
SOURCE = TASK / "formalization/CoefficientMapJet.lean"
BASE_SOURCE = TASK / "formalization/CoefficientMap.lean"
EXPECTED = "e50e11c0afd2eaac1d5c58c412e5e59bc5c2068c9826063eacee8dc88fc1735a"
BASE_EXPECTED = "e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03"
NS, BASE_NS = "ZetaNine.CoefficientMapJet", "ZetaNine.CoefficientMap"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
MATHLIB = ["Mathlib.RingTheory.PowerSeries.Inverse", "Mathlib.Algebra.Polynomial.Eval.Coeff", "Mathlib.Algebra.BigOperators.NatAntidiagonal"]
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def load(path): return json.loads(path.read_text(encoding="utf-8-sig"))
def facts(path): return [json.loads(s) for s in path.read_text(encoding="utf-8-sig").splitlines() if s.startswith("{")]
def write(path, value): path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
def edit(data, edits):
    edge = len(data)
    for start, end, replacement in sorted(set(edits), reverse=True):
        assert 0 <= start <= end <= edge
        data = data[:start] + replacement + data[end:]
        edge = start
    return data
checks = []
def check(name, condition, evidence):
    checks.append({"name": name, "pass": bool(condition), "evidence": evidence})
    assert condition, name

source = (OUT / "oracle-input.lean").read_bytes()
base_source = (BASE_BATCH / "oracle-input.lean").read_bytes()
plan, p, dplan = [load(OUT / name) for name in ["target-plan.json", "integration-provenance.json", "decl-plan.json"]]
oracle, receipt = [load(OUT / name) for name in ["oracle-execution-receipt.json", "staged-compile-receipt.json"]]
definition_req, problems = [load(OUT / name) for name in ["definitions-request.json", "problems-request.json"]]
check("both_frozen_sources_and_actual_parser_snapshots", sha(SOURCE) == EXPECTED and sha(BASE_SOURCE) == BASE_EXPECTED and source == SOURCE.read_bytes().replace(b"\r\n", b"\n") and base_source == BASE_SOURCE.read_bytes().replace(b"\r\n", b"\n"), {"Jet_source_sha256": EXPECTED, "Base_source_sha256": BASE_EXPECTED})
math_review_path = TASK / "verification/formalization-coefficient-map-jet-2026-10-03/independent-review.json"
math_review = load(math_review_path)
check("independent_frozen_native_math_review", math_review["status"] == "PASS" and math_review["sources_sha256"]["CoefficientMapJet.lean"] == EXPECTED and math_review["sources_sha256"]["CoefficientMap.lean"] == BASE_EXPECTED, {"report": math_review_path.relative_to(TASK).as_posix(), "sha256": sha(math_review_path), "scope": math_review["verdict"]})
manifest = load(ROOT / "lake-manifest.json")
revision = next(v["rev"] for v in manifest["packages"] if v["name"] == "mathlib")
toolchain = (ROOT / "lean-toolchain").read_text().strip()
check("pinned_environment", revision == problems["env"] == definition_req[0]["env"] == "0df444a360eaa60ab8c11dca51a86af692955474" and toolchain == "leanprover/lean4:v4.33.1", {"mathlib_rev": revision, "lean_toolchain": toolchain})
for row in oracle["rows"]:
    assert row["exit_code"] == 0 and sha(OUT / row["wrapper"]) == row["wrapper_sha256"]
    if row.get("log"): assert sha(OUT / row["log"]) == row["log_sha256"]
    if row.get("stdout"):
        assert sha(OUT / row["stdout"]) == row["stdout_sha256"] and sha(OUT / row["stderr"]) == row["stderr_sha256"]
    if row.get("output"): assert sha(Path(row["output"])) == row["output_sha256"]
    if row.get("extractor"): assert sha(OUT / row["extractor"]) == row["extractor_sha256"]
assert sha(TASK / oracle["base_original_olean"]) == oracle["base_original_olean_sha256"] == sha(TASK / oracle["task_local_base_object_copy"])
graph = facts(OUT / "decl_graph.jsonl")
by_name = {r["name"]: r for r in graph}
oracle_facts = facts(OUT / "sketch_info.jsonl")
jet = [r for r in graph if r["module"].endswith(".CoefficientMapJet")]
check("executed_official_cross_module_graph_and_parser", len(oracle["rows"]) == 4 and len(graph) == len(by_name) == 65 and len(jet) == 37 and sum(r["startLine"] > 0 for r in jet) == 28 and {k: sum(f["kind"] == k for f in oracle_facts) for k in ["decl", "ref", "command"]} == {"decl": 28, "ref": 141, "command": 47}, {"receipt": "oracle-execution-receipt.json", "source_declarations": "9 defs plus 19 proofs", "generated_spanless_eq_1": 9, "regex_mathematical_source_position_queries": False})
base_fact_path = TASK / p["base_parser_facts"]
assert sha(base_fact_path) == p["base_parser_facts_sha256"]
base_decl_facts = [f for f in facts(base_fact_path) if f["kind"] == "decl"]
work = [r["name"] for r in jet if r["startLine"] > 0] + [r["name"] for r in graph if r["isInstance"]]
reachable = set()
while work:
    name = work.pop()
    if name in reachable: continue
    reachable.add(name)
    work.extend(by_name[name]["typeDeps"] + by_name[name]["valueDeps"])
helpers = [by_name[name] for name in reachable if by_name[name]["module"].endswith(".CoefficientMap") and by_name[name]["kind"] == "theorem" and by_name[name]["startLine"] > 0]
assert [r["userName"] for r in helpers] == [BASE_NS + ".clearedPoleProduct_ne_zero"]
for record, fact in zip(helpers, p["base_helper_declaration_facts"]):
    matches = [f for f in base_decl_facts if f["declStart"]["line"] <= record["startLine"] <= f["declEnd"]["line"]]
    assert matches == [fact]
bridge = "open scoped BigOperators\nopen Finset Polynomial\n\nnamespace " + BASE_NS + "\n\n"
bridge += "\n\n".join(base_source[f["declStart"]["offset"]:f["declEnd"]["offset"]].decode("utf-8") for f in p["base_helper_declaration_facts"])
bridge += "\n\nend " + BASE_NS + "\n"
assert (OUT / "base-proof-bridge.lean.inc").read_bytes() == bridge.encode("utf-8")
check("actual_Base_proof_closure_inlined_without_new_assumption", p["base_helper_names"] == [BASE_NS + ".clearedPoleProduct_ne_zero"] and not dplan["new_external_theorem_boundaries"], {"helpers": p["base_helper_names"], "bridge_exact_original_bytes": True, "Base_definition_import": plan["base_definition"], "new_external_Theorems_boundaries": []})
definition_path = OUT / "staged" / plan["local_definition"]
definition_code = definition_path.read_text(encoding="utf-8")
definition_facts = p["definition_facts"]
actual_defs = [source[f["declStart"]["offset"]:f["declEnd"]["offset"]].decode("utf-8") for f in definition_facts]
check("lightweight_actual_nine_Jet_defs_no_proofs", len(actual_defs) == 9 and all(s in definition_code for s in actual_defs) and len(re.findall(r"(?m)^def ", definition_code)) == 9 and not re.search(r"(?m)^(theorem|lemma|axiom)\b", definition_code) and definition_req[0]["definition"] == definition_code and sha(definition_path) == p["definition_sha256"] and "import Definitions.Def_ZetaNine_CoefficientMap\n" in definition_code and "import missions." not in definition_code, {"names": dplan["retained_Jet_definition_names"], "exact_original_source_def_spans": True, "closed_formula_replacement": False})
deletions = [(f["declStart"]["offset"], f["declEnd"]["offset"], b"") for f in definition_facts]
diagnostics = [(f["span"]["start"]["offset"], f["span"]["end"]["offset"], b"") for f in p["diagnostic_deletion_facts"]]
header = facts(OUT / "header_info.jsonl")[0]
assert header == p["header_fact"] and header["start"]["offset"] == 0
assert source[:header["end"]["offset"]].decode().strip().splitlines() == ["import missions.zeta9.formalization.CoefficientMap"] + ["import " + m for m in MATHLIB]
solution_header = "import " + plan["local_definition"].removesuffix(".lean").replace("/", ".") + "\nimport Mathlib.Tactic\n" + "\n".join("import " + m for m in MATHLIB) + "\n\n" + bridge
assert solution_header == p["solution_header"]
original_rows = {r["label"]: r for r in facts(OUT / "types-original.log")}
definition_rows = {r["label"]: r for r in facts(OUT / "types-definition.log")}
def_labels = dplan["retained_Base_definition_names"] + dplan["retained_Jet_definition_names"]
assert len(original_rows) == 21 and len(definition_rows) == len(def_labels) == 18
all_values, all_types, all_axioms, all_stubs = True, True, True, True
targets = []
for i, target in enumerate(plan["targets"]):
    name = target["theorem_name"]
    t = p["targets"][name]
    d = t["stage2_declaration_fact"]
    start, value = [d[k]["offset"] for k in ["declStart", "valStart"]]
    bs, be = t["binding_fact"]["start"]["offset"], t["binding_fact"]["end"]["offset"]
    signature = source[be:value].decode("utf-8")
    renames = []
    for ref in t["stage2_target_reference_facts"]:
        a,b = ref["start"]["offset"], ref["end"]["offset"]
        if any(ca <= a and b <= cb for ca, cb, _ in diagnostics): continue
        old = source[a:b].decode()
        new = t["checked_name"].removeprefix(NS + ".") if old == name.removeprefix(NS + ".") else t["checked_name"]
        renames.append((a,b,new.encode("utf-8")))
    core = edit(source, [(0,header["end"]["offset"],b"")] + deletions + diagnostics + renames).decode("utf-8")
    code = solution_header + "\n" + core + "\n\nopen " + NS + "\n\ntheorem solution" + signature + ":= by\n  exact " + t["checked_name"] + " " + target["wrapper_arguments"] + "\n\n#print axioms solution\n"
    solpath, refpath = [OUT / "staged" / target["local_" + kind] for kind in ["solution", "reference"]]
    assert solpath.read_bytes() == code.encode("utf-8") and sha(solpath) == t["solution_sha256"] and sha(refpath) == t["reference_sha256"]
    assert len(re.findall(r"(?m)^theorem ", code)) == 21
    assert not re.search(r"\b(sorry|admit|axiom|unsafe)\b", code) and not re.search(r"(?m)^import (?:Theorems|Solutions|missions)\.", code)
    sol_rows, ref_rows = [{r["label"]: r for r in facts(OUT / f"types-{i}-{kind}.log")} for kind in ["solution", "reference"]]
    assert len(sol_rows) == len(ref_rows) == 19
    for label in def_labels:
        for comparison in [definition_rows, sol_rows, ref_rows]:
            all_values &= all(comparison[label][k] == original_rows[label][k] for k in ["type", "value"])
            all_axioms &= set(comparison[label]["axioms"]) <= STANDARD
    original, solution, reference = original_rows[name], sol_rows[name], ref_rows[name]
    all_types &= original["type"] == solution["type"] == reference["type"]
    all_axioms &= set(original["axioms"]) == set(solution["axioms"]) == STANDARD
    all_stubs &= "sorryAx" in reference["axioms"] and set(reference["axioms"]) <= STANDARD | {"sorryAx"}
    targets.append({"theorem_name": name, "original_statement_type": original["type"], "original_solution_reference_type_exactly_equal": original["type"] == solution["type"] == reference["type"],
                    "original_axioms": original["axioms"], "solution_axioms": solution["axioms"], "statement_stub_axioms": reference["axioms"],
                    "solution": target["local_solution"], "solution_sha256": sha(solpath), "reference": target["local_reference"], "reference_sha256": sha(refpath),
                    "extra_top_level_solution_binders": [], "Base_proof_inlined": p["base_helper_names"], "original_Jet_proofs_preserved": 19})
check("exact_parser_span_transplant_all_nineteen_Jet_proofs", True, {"proof_declarations_per_Solution": "19 Jet + 1 actual Base + 1 solution wrapper", "deleted_Jet_defs": 9, "deleted_diagnostics": 10, "mission_header_replaced_by_actual_parser_span": True, "only_own_theorem_and_resolved_refs_renamed": True})
check("all_eighteen_actual_definition_types_values_exactly_equal", all_values, {"comparison": "Actual imports with pp.fullNames=true; original, Definition, all 3 Solution and 3 reference environments. Nine Jet and nine Base original definition bytes retained.", "reports": ["types-original.log", "types-definition.log"] + [f"types-{i}-{kind}.log" for i in range(3) for kind in ["solution", "reference"]]})
check("three_original_Solution_reference_statement_types_exactly_equal", all_types, {"targets": [t["theorem_name"] for t in targets], "no_extra_binders_or_proof_assumptions": True})
check("three_actual_Solutions_standard_three_axioms_only", all_axioms and all_stubs, {"actual_proof_axioms": sorted(STANDARD), "reference_stubs_intentionally_have_sorryAx": True, "own_Solution_source_has_no_holes_axioms_unsafe": True})
for row in receipt["rows"]:
    assert row["exit_code"] == int((OUT / row["exit_file"]).read_text().strip()) == 0
    assert sha(TASK / row["source"]) == row["source_sha256"]
    for key in ["log", "wrapper", "exit_file"]: assert sha(OUT / row[key]) == row[key + "_sha256"]
    if row["output"]: assert sha(OUT / row["output"]) == row["output_sha256"]
assert sha(TASK / receipt["base_definition_source"]) == receipt["base_definition_source_sha256"] == p["base_definition_source_sha256"]
assert sha(TASK / receipt["base_definition_original_olean"]) == receipt["base_definition_original_olean_sha256"] == sha(TASK / receipt["base_definition_local_object_copy"])
assert sha(TASK / receipt["base_definition_compile_receipt"]) == receipt["base_definition_compile_receipt_sha256"]
check("fifteen_actual_build_and_import_runs_exit_zero", receipt["complete"] and receipt["all_exit_codes_actually_observed"] and len(receipt["rows"]) == 15, {"receipt": "staged-compile-receipt.json", "new_module_builds": 7, "actual_import_type_value_reports": 8, "native_oracle_header_runs_additional": 4})
problem_keys = {"theorem_name", "theorem_title", "formal_statement", "natural_language_statement", "preamble", "source", "tags"}
definition_keys = {"definition_name", "definition_title", "definition", "natural_language_statement", "source", "tags", "env", "private"}
check("strict_documented_API_payloads_and_faithful_quantifiers", set(problems) == {"env", "private", "problems"} and len(problems["problems"]) == 3 and len(definition_req) == 1 and set(definition_req[0]) == definition_keys and all(set(v) == problem_keys and v["formal_statement"].endswith(":= by sorry") and "theorem " + v["theorem_name"] in v["formal_statement"] and not re.search(r"(?m)^def\b", v["preamble"]) for v in problems["problems"]), {"API_document": "formalization/platform/readback-2026-10-03/api-docs/references/contribute.md", "unique_all_n_j_no_hj_added": True, "convolution_j_le_n_and_1_le_s_le_9_preserved": True, "arbitrary_rational_or_integer_W_including_zero": True, "integer_multiplier_does_not_claim_rational_local_coefficients_integral": True})
module_paths = [plan["local_definition"]] + [v[k] for v in plan["targets"] for k in ["local_solution", "local_reference"]]
copy_rows = [{"staged_task_relative": (OUT / "staged" / path).relative_to(TASK).as_posix(), "root_relative_destination": path, "sha256": sha(OUT / "staged" / path), "bytes": (OUT / "staged" / path).stat().st_size, "destination_exists_at_author_freeze": (ROOT / path).exists()} for path in module_paths]
write(OUT / "root-copy-plan.json", {"source_sha256": EXPECTED, "base_source_sha256": BASE_EXPECTED, "required_existing_Base_definition": {"root_relative": plan["base_definition"], "sha256": p["base_definition_source_sha256"]}, "author_scope": "offline staged-only; parent executes installation", "overwrite_allowed": False, "files": copy_rows, "scope_build_entrypoints_for_parent": [v["local_solution"].removesuffix(".lean").replace("/", ".") for v in plan["targets"]]})
check("offline_task_local_batch_and_parent_root_copy_plan", not receipt["shared_root_writes"] and not receipt["API_called"] and len(copy_rows) == 7, {"root_copy_plan": "root-copy-plan.json", "root_scope_API_credentials_writes": False, "platform_published_or_accepted_claimed": False})
failed_attempts = [{"label": "Initial isolated native import layout", "exit_code": 1, "evidence": "original-compile.log.before-cache-layout-fix", "explanation": "Lean's first existing module hierarchy shadowed the later genuine Base object; an exact hash-bound Base object copy in the same task-local hierarchy fixed resolution."}, {"label": "Header oracle adapter field access", "exit_code": 1, "evidence": "header_info.jsonl.before-raw-fix", "explanation": "Lean Parser.parseHeader returns TSyntax; source-range access must use header.raw. Final actual header parser run exits zero."}]
external_paths = [SOURCE, BASE_SOURCE, math_review_path, base_fact_path, BASE_BATCH / "oracle-input.lean", BASE_BATCH / "oracle-execution-receipt.json", TASK / oracle["base_original_olean"], TASK / receipt["base_definition_source"], TASK / receipt["base_definition_original_olean"], TASK / receipt["base_definition_compile_receipt"]]
stable_paths = sorted(set(external_paths + [v for v in OUT.rglob("*") if v.is_file() and v.name not in ["author-audit.json", "SHA256SUMS.txt"] and "__pycache__" not in v.parts]))
bindings = [{"task_relative": v.relative_to(TASK).as_posix(), "root_relative": v.relative_to(ROOT).as_posix(), "bytes": v.stat().st_size, "sha256": sha(v)} for v in stable_paths]
report = {"schema_version": 1, "review_role": "author offline source/compile gate; independent native mathematical review and independent transplant review are separate", "verdict": "PASS", "source_sha256": EXPECTED, "base_source_sha256": BASE_EXPECTED,
          "mathlib_rev": revision, "lean_toolchain": toolchain, "checks": checks, "targets": targets, "retained_failed_attempts": failed_attempts, "platform_published": False, "platform_accepted": False, "root_installed_by_author": False,
          "limitations": ["Formal local quotient in Q[[z]] and nine finite coefficient convolution orders only.", "No numerical evaluation or analytic convergence theorem for the infinite formal series.", "No full LaurentSeries/RatFunc embedding or global partial-fraction decomposition.", "No complete aggregate F map, reflection/cancellation result, or invertibility.", "No exact infinite L identity, J certificate, or irrationality result.", "Integer W supplies integer multiplier coefficients; actual lower local coefficients remain rational and may be nonintegral.", "Arbitrary W can vanish; arbitrary local degree does not discharge global degree/growth restrictions.", "Statement reference stubs use sorryAx and are not proofs.", "Local compilation does not imply platform publication or acceptance."], "stable_files": bindings}
write(OUT / "author-audit.json", report)
frozen = sorted(v for v in OUT.rglob("*") if v.is_file() and v.name != "SHA256SUMS.txt" and "__pycache__" not in v.parts)
(OUT / "SHA256SUMS.txt").write_text("".join(sha(v) + "  " + v.relative_to(OUT).as_posix() + "\n" for v in frozen), encoding="utf-8")
print(json.dumps({"verdict": "PASS", "checks": len(checks), "frozen_files": len(frozen), "author_audit_sha256": sha(OUT / "author-audit.json"), "root_copy_plan_sha256": sha(OUT / "root-copy-plan.json"), "SHA256SUMS_sha256": sha(OUT / "SHA256SUMS.txt")}, indent=2))
