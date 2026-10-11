"""Author's offline gate: verify actual reports, exact parser-splices, then freeze."""
from pathlib import Path
import hashlib
import json
import re
import sys

sys.stdout.reconfigure(encoding="utf-8")
OUT = Path(__file__).resolve().parent
TASK = OUT.parents[2]
ROOT = TASK.parents[1]
SOURCE = TASK / "formalization/CoefficientMap.lean"
EXPECTED = "e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03"
NS = "ZetaNine.CoefficientMap"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def load(path):
    return json.loads(path.read_text(encoding="utf-8-sig"))

def write(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

def facts(path):
    return [json.loads(s) for s in path.read_text(encoding="utf-8-sig").splitlines() if s.startswith("{")]

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
plan = load(OUT / "target-plan.json")
provenance = load(OUT / "integration-provenance.json")
decl_plan = load(OUT / "decl-plan.json")
oracle = load(OUT / "oracle-execution-receipt.json")
receipt = load(OUT / "staged-compile-receipt.json")
definition_req = load(OUT / "definitions-request.json")
problems = load(OUT / "problems-request.json")
check("frozen_original_source_and_actual_snapshot", sha(SOURCE) == EXPECTED and source == SOURCE.read_bytes().replace(b"\r\n", b"\n") and provenance["source_sha256"] == EXPECTED,
      {"source": SOURCE.relative_to(ROOT).as_posix(), "sha256": EXPECTED, "bytes": len(source)})
manifest = load(ROOT / "lake-manifest.json")
revision = next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib")
toolchain = (ROOT / "lean-toolchain").read_text().strip()
check("pinned_environment", revision == problems["env"] == definition_req[0]["env"] == "0df444a360eaa60ab8c11dca51a86af692955474" and toolchain == "leanprover/lean4:v4.33.1", {"mathlib_rev": revision, "lean_toolchain": toolchain})
for row in oracle["rows"]:
    assert row["exit_code"] == 0
    assert sha(OUT / row["wrapper"]) == row["wrapper_sha256"]
    if row.get("log"):
        assert sha(OUT / row["log"]) == row["log_sha256"]
    if row.get("stdout"):
        assert sha(OUT / row["stdout"]) == row["stdout_sha256"]
        assert sha(OUT / row["stderr"]) == row["stderr_sha256"]
    if row.get("output"):
        assert sha(Path(row["output"])) == row["output_sha256"]
oracle_facts = facts(OUT / "sketch_info.jsonl")
check("official_oracles_actually_executed", len(oracle["rows"]) == 3 and {k: sum(f["kind"] == k for f in oracle_facts) for k in ["decl", "ref", "command"]} == {"decl": 27, "ref": 92, "command": 45}, {"receipt": "oracle-execution-receipt.json", "declaration_facts": "decl_graph.jsonl", "parser_reference_facts": "sketch_info.jsonl", "regex_mathematical_source_position_queries": False})

definition_path = OUT / "staged" / plan["local_definition"]
definition_code = definition_path.read_text(encoding="utf-8")
definition_facts = provenance["definition_facts"]
actual_defs = [source[f["declStart"]["offset"]:f["declEnd"]["offset"]].decode("utf-8") for f in definition_facts]
assert all(s in definition_code for s in actual_defs)
check("nine_actual_definitions_only", len(actual_defs) == 9 and len(re.findall(r"(?m)^def ", definition_code)) == 9 and not re.search(r"(?m)^(theorem|lemma|axiom)\b", definition_code) and definition_req[0]["definition"] == definition_code and sha(definition_path) == provenance["definition_sha256"],
      {"declarations": decl_plan["retained_definition_names"], "all_original_definition_spans_exact": True, "no_closed_formula_substitution": True, "weightedR_retention_reason": decl_plan["retention_reason"]})
deletions = [(f["declStart"]["offset"], f["declEnd"]["offset"], b"") for f in definition_facts]
diagnostics = [(f["span"]["start"]["offset"], f["span"]["end"]["offset"], b"") for f in provenance["diagnostic_deletion_facts"]]
target_evidence = []
original_rows = {r["label"]: r for r in facts(OUT / "types-original.log")}
definition_rows = {r["label"]: r for r in facts(OUT / "types-definition.log")}
assert len(original_rows) == 12 and len(definition_rows) == 9
def_labels = decl_plan["retained_definition_names"]
all_def_equal = True
no_bad_axioms = True
all_types_equal = True
all_std3 = True
refs_sorry = True
for i, target in enumerate(plan["targets"]):
    name = target["theorem_name"]
    p = provenance["targets"][name]
    declaration = p["stage2_declaration_fact"]
    start, value = [declaration[k]["offset"] for k in ["declStart", "valStart"]]
    bs, be = p["binding_fact"]["start"]["offset"], p["binding_fact"]["end"]["offset"]
    signature = source[be:value].decode("utf-8")
    renames = []
    for ref in p["stage2_target_reference_facts"]:
        a, b = ref["start"]["offset"], ref["end"]["offset"]
        if any(ca <= a and b <= cb for ca, cb, _ in diagnostics):
            continue
        old = source[a:b].decode("utf-8")
        checked_short = p["checked_name"].removeprefix(NS + ".")
        new = checked_short if old == name.removeprefix(NS + ".") else p["checked_name"]
        renames.append((a, b, new.encode("utf-8")))
    core = edit(source, deletions + diagnostics + renames).decode("utf-8")
    code = "import " + plan["local_definition"].removesuffix(".lean").replace("/", ".") + "\n" + core + "\n\nopen " + NS + "\n\ntheorem solution" + signature + ":= by\n  exact " + p["checked_name"] + " " + target["wrapper_arguments"] + "\n\n#print axioms solution\n"
    solpath = OUT / "staged" / target["local_solution"]
    refpath = OUT / "staged" / target["local_reference"]
    assert solpath.read_bytes() == code.encode("utf-8")
    assert sha(solpath) == p["solution_sha256"] and sha(refpath) == p["reference_sha256"]
    assert not re.search(r"\b(sorry|admit|axiom|unsafe)\b", code)
    assert not re.search(r"(?m)^import (?:Theorems|Solutions)\.", code)
    assert len(re.findall(r"(?m)^theorem ", code)) == 19
    sol_rows = {r["label"]: r for r in facts(OUT / f"types-{i}-solution.log")}
    ref_rows = {r["label"]: r for r in facts(OUT / f"types-{i}-reference.log")}
    assert len(sol_rows) == len(ref_rows) == 10
    for label in def_labels:
        baseline = original_rows[label]
        for comparison in [definition_rows, sol_rows, ref_rows]:
            all_def_equal &= all(comparison[label][key] == baseline[key] for key in ["type", "value"])
            no_bad_axioms &= set(comparison[label]["axioms"]) <= STANDARD
    original = original_rows[name]
    solution, reference = sol_rows[name], ref_rows[name]
    all_types_equal &= original["type"] == solution["type"] == reference["type"]
    all_std3 &= set(original["axioms"]) == set(solution["axioms"]) == STANDARD
    refs_sorry &= "sorryAx" in reference["axioms"] and set(reference["axioms"]) <= STANDARD | {"sorryAx"}
    target_evidence.append({"theorem_name": name, "original_statement_type": original["type"],
                            "original_solution_reference_type_exactly_equal": original["type"] == solution["type"] == reference["type"],
                            "original_axioms": original["axioms"], "solution_axioms": solution["axioms"],
                            "statement_stub_axioms": reference["axioms"],
                            "solution": target["local_solution"], "solution_sha256": sha(solpath),
                            "reference": target["local_reference"], "reference_sha256": sha(refpath),
                            "only_source_edits": ["Nine actual def declaration deletions", "Eight parser-certified diagnostic command deletions", "Selected theorem binding and resolved references renamed", "Exact-signature solution wrapper appended"],
                            "extra_top_level_solution_binders": []})
check("complete_source_mathematical_helper_transplant", True, {"inline_theorem_count_per_solution": 18, "original_27_decl_core": "9 moved defs plus 18 retained proof declarations", "target_source_splices_verified_byte_for_byte": True, "new_external_theorem_boundaries": []})
check("all_nine_definition_types_and_values_exactly_equal", all_def_equal and no_bad_axioms, {"comparison": "Actual Lean imports, pp.fullNames=true, original vs definition vs all three Solution and reference environments; exact source declaration bytes retained.", "reports": ["types-original.log", "types-definition.log"] + [f"types-{i}-{kind}.log" for i in range(3) for kind in ["solution", "reference"]]})
check("all_three_original_solution_reference_types_exactly_equal", all_types_equal, {"targets": [r["theorem_name"] for r in target_evidence], "no_extra_binders_or_assumed_original_results": True})
check("all_three_actual_proofs_have_only_standard_axioms", all_std3 and refs_sorry, {"solution_axioms": sorted(STANDARD), "reference_stubs_contain_sorryAx_and_are_not_proofs": True, "all_Solution_source_has_no_sorry_admit_axiom_unsafe": True})
for row in receipt["rows"]:
    assert row["exit_code"] == 0
    assert int((OUT / row["exit_file"]).read_text().strip()) == 0
    assert sha(TASK / row["source"]) == row["source_sha256"]
    for key in ["log", "wrapper", "exit_file"]:
        assert sha(OUT / row[key]) == row[key + "_sha256"]
    if row["output"]:
        assert sha(OUT / row["output"]) == row["output_sha256"]
check("all_fifteen_actual_compile_import_runs_exit_zero", receipt["complete"] and receipt["all_exit_codes_actually_observed"] and len(receipt["rows"]) == 15, {"receipt": "staged-compile-receipt.json", "builds": 7, "actual_import_type_value_reports": 8, "original_oracle_executions_additional": 3})
problem_keys = {"theorem_name", "theorem_title", "formal_statement", "natural_language_statement", "preamble", "source", "tags"}
definition_keys = {"definition_name", "definition_title", "definition", "natural_language_statement", "source", "tags", "env", "private"}
check("documented_API_payload_schema_and_faithful_public_statements", set(problems) == {"env", "private", "problems"} and len(problems["problems"]) == 3 and set(definition_req[0]) == definition_keys and all(set(p) == problem_keys and p["formal_statement"].endswith(":= by sorry") and "theorem " + p["theorem_name"] in p["formal_statement"] and not re.search(r"(?m)^def\b", p["preamble"]) for p in problems["problems"]), {"API_document": "formalization/platform/readback-2026-10-03/api-docs/references/contribute.md", "no_local_def_in_problem_preamble": True, "regular_point_condition_preserved": True, "unweighted_formula_all_n_j_le_n": True, "weighted_formula_even_n_arbitrary_W_may_vanish": True})

module_paths = [plan["local_definition"]] + [p[k] for p in plan["targets"] for k in ["local_solution", "local_reference"]]
copy_rows = [{"staged_task_relative": (OUT / "staged" / path).relative_to(TASK).as_posix(),
              "root_relative_destination": path, "sha256": sha(OUT / "staged" / path),
              "bytes": (OUT / "staged" / path).stat().st_size,
              "destination_exists_at_author_freeze": (ROOT / path).exists()} for path in module_paths]
write(OUT / "root-copy-plan.json", {"source_sha256": EXPECTED, "author_scope": "offline staged-only; parent executes installation", "overwrite_allowed": False, "files": copy_rows,
                                    "scope_build_entrypoints_for_parent": [p["local_solution"].removesuffix(".lean").replace("/", ".") for p in plan["targets"]]})
check("offline_task_local_boundary_and_root_copy_plan", not receipt["shared_root_writes"] and not receipt["API_called"] and len(copy_rows) == 7, {"root_copy_plan": "root-copy-plan.json", "no_root_scope_API_credentials_changes": True, "platform_published_or_accepted_claimed": False})

stable_paths = sorted(p for p in OUT.rglob("*") if p.is_file() and p.name not in ["SHA256SUMS.txt", "author-audit.json"] and "__pycache__" not in p.parts)
bindings = [{"task_relative": p.relative_to(TASK).as_posix(), "root_relative": p.relative_to(ROOT).as_posix(), "bytes": p.stat().st_size, "sha256": sha(p)} for p in stable_paths]
bindings.insert(0, {"task_relative": SOURCE.relative_to(TASK).as_posix(), "root_relative": SOURCE.relative_to(ROOT).as_posix(), "bytes": SOURCE.stat().st_size, "sha256": sha(SOURCE)})
report = {"schema_version": 1, "review_role": "author offline source/compile gate; independent review is separate", "verdict": "PASS", "source_sha256": EXPECTED,
          "mathlib_rev": revision, "lean_toolchain": toolchain, "checks": checks, "targets": target_evidence,
          "platform_published": False, "platform_accepted": False, "root_installed_by_author": False,
          "limitations": ["Finite highest-pole clearing and coefficient entry only.", "No complete Laurent expansion or lower partial-fraction coefficient map.", "No full reflection identity or invertibility of the coefficient map.", "No exact infinite L-sum identity, J certificate, or irrationality result.", "Arbitrary polynomial W can annihilate the highest weighted coefficient.", "Statement stubs use sorryAx by design; only Solution modules are proofs.", "Server publication and acceptance are not implied by local compilation."],
          "stable_files": bindings}
write(OUT / "author-audit.json", report)
frozen = sorted(p for p in OUT.rglob("*") if p.is_file() and p.name != "SHA256SUMS.txt" and "__pycache__" not in p.parts)
(OUT / "SHA256SUMS.txt").write_text("".join(sha(p) + "  " + p.relative_to(OUT).as_posix() + "\n" for p in frozen), encoding="utf-8")
print(json.dumps({"verdict": report["verdict"], "checks": len(checks), "stable_files": len(frozen), "author_audit_sha256": sha(OUT / "author-audit.json"), "root_copy_plan_sha256": sha(OUT / "root-copy-plan.json"), "SHA256SUMS_sha256": sha(OUT / "SHA256SUMS.txt")}, indent=2))
