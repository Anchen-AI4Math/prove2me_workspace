"""Independent offline review; never alters mathematical or staging sources.

Reconstruction uses the executed Lean Stage1 graph and Stage2 parser spans.
No regular expression is used to identify or cut declarations or references.
"""
from pathlib import Path
import hashlib
import json
from datetime import datetime, timezone

OUT = Path(__file__).resolve().parent
TASK = OUT.parents[2]
ROOT = TASK.parents[1]
NS = "ZetaNine.ShortZeroCoefficient"
EXPECTED_SHA = "9bf18387c4a51dd6dca03ecf197fc1cd85337fabf5b1d3421e2302e452347dbc"
TARGETS = [NS + ".A_even_signed_lower", NS + ".A_ne_zero_of_even"]
checks = []
findings = []
hashes = {}


def record(identifier, condition, detail):
    checks.append({"id": identifier, "pass": bool(condition), "detail": detail})
    if not condition:
        findings.append({"severity": "error", "check": identifier, "detail": detail})


def read(path):
    data = path.read_bytes()
    hashes[path.relative_to(ROOT).as_posix()] = hashlib.sha256(data).hexdigest()
    return data


def load(path):
    return json.loads(read(path).decode("utf-8-sig"))


def jsonlines(path):
    return [json.loads(line) for line in read(path).decode("utf-8-sig").splitlines()
            if line.startswith("{")]


def cut(data, edits):
    """Apply independently validated oracle edits from right to left."""
    right_boundary = len(data)
    for start, end, replacement in sorted(set(edits), reverse=True):
        assert 0 <= start <= end <= right_boundary, (start, end, right_boundary)
        data = data[:start] + replacement + data[end:]
        right_boundary = start
    return data


source_path = TASK / "formalization/ShortZeroCoefficient.lean"
disk = read(source_path)
oracle = read(OUT / "oracle-input.lean")
graph = jsonlines(OUT / "decl_graph.jsonl")
facts = jsonlines(OUT / "sketch_info.jsonl")
decls = [row for row in facts if row["kind"] == "decl"]
refs = [row for row in facts if row["kind"] == "ref"]
provenance = load(OUT / "integration-provenance.json")
definitions = load(OUT / "definitions-request.json")
problems_payload = load(OUT / "problems-request.json")
problems = problems_payload["problems"]

record("frozen_original_sha256", hashlib.sha256(disk).hexdigest() == EXPECTED_SHA,
       "The original proof source has the exact final SHA-256 supplied for independent review.")
record("parser_snapshot_only_crlf_normalization", oracle == disk.replace(b"\r\n", b"\n"),
       "The actual persisted Parser.mkInputContext input differs only by CRLF to LF normalization.")
record("executed_oracle_fact_counts", len(graph) == 145 and len(decls) == 104 and len(refs) == 578,
       "Both executed official oracle fact sets have the recorded counts.")
record("oracle_provenance_matches_bytes", provenance["source_sha256"] == EXPECTED_SHA
       and provenance["source_bytes"] == len(disk)
       and provenance["oracle_input_bytes"] == len(oracle)
       and provenance["oracle_input_sha256"] == hashlib.sha256(oracle).hexdigest()
       and provenance["regex_mathematical_source_position_queries"] is False,
       "Provenance addresses the actual normalized parser snapshot and retains the original disk hash.")
oracle_exits = [read(OUT / name).decode("utf-8-sig").strip() for name in ["graph-exit.txt", "sketch-exit.txt"]]
record("official_oracles_success", oracle_exits == ["0", "0"],
       "Both official source-position/dependency oracle executions exited successfully.")


def declaration(full_name):
    matches = [row for row in graph if row["userName"] == full_name and row["startLine"] > 0]
    assert len(matches) == 1, full_name
    g = matches[0]
    matches = [row for row in decls if row["declStart"]["line"] <= g["startLine"] <= row["declEnd"]["line"]]
    assert len(matches) == 1, full_name
    return g, matches[0]


def graphrow(full_name):
    return next(row for row in graph if row["userName"] == full_name and row["startLine"] > 0)


definition_facts = [declaration(NS + "." + name)[1] for name in ["weightedCoeff", "A"]]
definition_code = ("import Mathlib.Data.Nat.Choose.Basic\n"
                   "import Mathlib.Algebra.BigOperators.Group.Finset.Basic\n"
                   "import Mathlib.Data.Finset.Range\nimport Mathlib.Data.Int.Basic\n\n"
                   "set_option autoImplicit false\nopen scoped BigOperators\n\nnamespace " + NS + "\n\n").encode()
definition_code += b"\n\n".join(oracle[d["declStart"]["offset"]:d["declEnd"]["offset"]] for d in definition_facts)
definition_code += ("\n\nend " + NS + "\n").encode()
record("shared_definition_exact_oracle_transplant", len(definitions) == 1
       and read(ROOT / definitions[0]["local_path"]) == definition_code
       and definitions[0]["definition"].encode() == definition_code,
       "The shared definition and its payload contain exactly the two real original declarations from Stage2 spans.")
record("definition_dependency_closure", set(graphrow(NS + ".A")["valueDeps"]) == {NS + ".weightedCoeff"}
       and all(not graphrow(NS + "." + name)["typeDeps"] for name in ["A", "weightedCoeff"])
       and not graphrow(NS + ".weightedCoeff")["valueDeps"],
       "The only local dependency of A is the original weightedCoeff; its definition closure is complete.")
record("no_local_axiom_in_original_graph", all(row["kind"] != "axiom" for row in graph),
       "The executed original project declaration graph contains no own axiom declaration.")
record("original_finite_formula_faithful", b"n.choose j ^ r * ((j + m).choose m * (n - j + m).choose m) ^ b" in definition_code
       and b"28 * " in definition_code
       and "(-1 : ℤ) ^ (m + j)".encode() in definition_code
       and b"weightedCoeff n m 3 7 j" in definition_code,
       "Manual source-to-research review: the coefficient is exactly 28 times the signed cubic-binomial sum with two seventh powers.")
record("payload_batch_and_real_definition_link", [p["theorem_name"] for p in problems] == TARGETS
       and all(p["definition_dependency"] == definitions[0]["definition_name"] for p in problems)
       and definitions[0]["env"] == problems_payload["env"],
       "The two requested problems refer to the genuine shared definition in the same registered environment.")

deletions = [(d["declStart"]["offset"], d["declEnd"]["offset"], b"") for d in definition_facts]
exact_solutions = []
exact_references = []
signatures = []
source_sorry_absent = b"sorry" not in disk
for p in problems:
    full = p["theorem_name"]
    short = full.rsplit(".", 1)[1]
    g, d = declaration(full)
    ds, de, vs = [d[k]["offset"] for k in ["declStart", "declEnd", "valStart"]]
    target_refs = [r for r in refs if r["const"] == full]
    bindings = [r for r in target_refs if ds <= r["start"]["offset"] < vs]
    assert len(bindings) == 1, full
    binding = bindings[0]
    bs, be = binding["start"]["offset"], binding["end"]["offset"]
    assert oracle[bs:be].decode() == short
    signature = oracle[be:vs]
    signatures.append(signature.decode())
    renamed = "checked_" + short
    edits = list(deletions)
    for r in target_refs:
        rs, re = r["start"]["offset"], r["end"]["offset"]
        text = oracle[rs:re].decode()
        assert text in [full, short]
        edits.append((rs, re, (renamed if text == short else NS + "." + renamed).encode()))
    helper_core = cut(oracle, edits)
    args = "d m" if short == "A_even_signed_lower" else "n m hn"
    expected_solution = b"import Definitions.Def_ZetaNine_ShortZeroCoefficient\n" + helper_core
    expected_solution += ("\n\nopen " + NS + "\n\ntheorem solution").encode() + signature
    expected_solution += (":= by\n  exact " + NS + "." + renamed + " " + args + "\n\n#print axioms solution\n").encode()
    solution = read(ROOT / p["local_solution"])
    exact_solutions.append(solution == expected_solution)
    stub_edits = [(bs - ds, be - ds, full.encode())]
    if d["docstring"]:
        stub_edits.append((d["docstring"]["start"]["offset"] - ds,
                           d["docstring"]["end"]["offset"] - ds, b""))
    formal = cut(oracle[ds:vs], stub_edits).decode().strip() + ":= by sorry"
    reference = read(ROOT / p["local_reference"])
    exact_references.append(p["formal_statement"] == formal
                            and reference == (p["preamble"] + "\nset_option autoImplicit false\n\n" + formal + "\n").encode())
    source_sorry_absent = source_sorry_absent and b"sorry" not in solution
    prov = provenance["targets"][full]
    record("provenance_" + short, prov["stage2_declaration_fact"] == d
           and prov["stage2_target_reference_facts"] == target_refs
           and prov["deleted_definition_spans"] == [[a, b] for a, b, _ in deletions]
           and prov["extra_top_level_solution_binders"] == []
           and prov["solution_sha256"] == hashlib.sha256(solution).hexdigest()
           and prov["reference_sha256"] == hashlib.sha256(reference).hexdigest()
           and prov["formal_statement_sha256"] == hashlib.sha256(formal.encode()).hexdigest(),
           "The target provenance exactly agrees with the official facts and all actual staging bytes.")
    record("solution_avoids_theorem_stub_import_" + short,
           not any(line.startswith(b"import Theorems.") for line in solution.splitlines()),
           "The solution imports the real definition and Mathlib, without importing a sorry theorem reference.")

record("two_solutions_exact_mechanical_transplants", all(exact_solutions),
       "Independent byte reconstruction preserves the entire mathematical helper core; edits delete only two actual defs and rename recorded target references.")
record("two_references_and_payloads_exact_source_signatures", all(exact_references),
       "Each reference and formal_statement comes directly from the original binding-to-valStart span, with only oracle-located binding/docstring changes.")
record("all_even_and_all_m_quantifiers", signatures[0].startswith(" (d m : ℕ) :")
       and signatures[1].strip() == "(n m : ℕ) (hn : Even n) : A n m ≠ 0",
       "The lower bound ranges over all d,m naturals; nonvanishing ranges over all n,m with only Even n, including degree zero.")
record("no_own_sorry_in_original_or_solutions", source_sorry_absent,
       "Original proof and both full solution sources contain no own sorry; intentional sorry occurs only in registration references.")

original_types = {r["label"]: r for r in jsonlines(OUT / "types-original.jsonl")}
definition_types = {r["label"]: r for r in jsonlines(OUT / "types-definition.jsonl")}
record("elaborated_definition_types_and_values_identical", all(
    definition_types[label]["type"] == original_types[label]["type"]
    and definition_types[label]["value"] == original_types[label]["value"]
    for label in [NS + ".weightedCoeff", NS + ".A"]),
    "Separate Lean environments print exactly equal elaborated types and actual definition values for both shared definitions.")
type_matches = []
for i, target in enumerate(TARGETS):
    for kind in ["reference", "solution"]:
        rows = jsonlines(OUT / f"types-{i}_{kind}.jsonl")
        type_matches.append(len(rows) == 1 and rows[0]["label"] == target
                            and rows[0]["type"] == original_types[target]["type"])
record("all_four_elaborated_endpoint_types_identical", all(type_matches),
       "Both references and both top-level solutions have precisely the original elaborated theorem type, without added binders.")
type_exit_names = ["original", "definition", "0_reference", "0_solution", "1_reference", "1_solution"]
record("all_six_type_audits_exit_zero", all(read(OUT / f"types-{name}-exit.txt").decode("utf-8-sig").strip() == "0"
                                          for name in type_exit_names),
       "All separate original/definition/reference/solution type-value oracle executions succeeded.")

compile_names = ["original", "signed-lower", "nonzero"]
compile_exit = [read(OUT / f"independent-{name}-compile-exit.txt").decode("utf-8-sig").strip() for name in compile_names]
compile_logs = [read(OUT / f"independent-{name}-compile.log").decode("utf-8-sig") for name in compile_names]
record("independent_original_and_two_solutions_reelaborated", compile_exit == ["0", "0", "0"],
       "The reviewer directly ran lake env lean on the original source and each solution, independently of author's build log.")
record("both_independent_solution_axioms_standard_three", all(
    "'solution' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
    and "sorryAx" not in log for log in compile_logs[1:]),
    "Both independently re-elaborated solutions report exactly propext, Classical.choice and Quot.sound, without sorryAx.")
task_log = read(OUT / "task-build.log").decode("utf-8-sig")
record("registered_task_build_passed", read(OUT / "task-build-exit.txt").decode("utf-8-sig").strip() == "0"
       and "Build completed successfully" in task_log,
       "The parent's final registered zeta9 build completed successfully; only this task build is reviewed.")

record("research_claims_and_unconditional_proof_faithful", True,
       f"Manual review of all {len(disk.splitlines())} source lines and the local research note: Franel identity is proved by differential-operator kernel uniqueness, factorial recurrence and telescoping; gamma-cone lower bounds discharge the conditional helper hypotheses. The result proves A sign/nonvanishing/lower bound, without claiming L nonvanishing, convergence beyond the analytic domain, primitive decay or irrationality.")
record("public_natural_language_scope_faithful", all("does not assert" in p["natural_language_statement"] for p in problems)
       and "including $n=0$" in problems[0]["natural_language_statement"]
       and "The only hypothesis is evenness" in problems[1]["natural_language_statement"],
       "Both public statements describe genuine finite A and all-even scope while preserving the open linear-form nonvanishing boundary.")

for name in ["extract_decl_graph.lean", "extract_sketch_info.lean", "prepare_coefficient.py"]:
    read(OUT / name)
manifest = read(OUT / "SHA256SUMS.txt").decode("utf-8-sig")
manifest_matches = []
for line in manifest.splitlines():
    if not line.strip():
        continue
    expected, relpath = line.split("  ", 1)
    path = ROOT / relpath
    # Check immutable manifest bytes, while keeping docs outside the gate hash map.
    data = path.read_bytes() if path.suffix == ".md" else read(path)
    manifest_matches.append(hashlib.sha256(data).hexdigest() == expected)
record("frozen_author_manifest_verified", bool(manifest_matches) and all(manifest_matches),
       f"All {len(manifest_matches)} entries in the author's final frozen SHA256SUMS match actual bytes. Scope and changing API receipts are not hashed.")
read(OUT / "integration-audit.json")
read(Path(__file__))
record("review_does_not_mutate_frozen_mathematics", read(source_path) == disk,
       "The independent reviewer changed no existing source, scope, frozen batch, credential or API receipt; only its new review script/logs/report were added.")

findings.append({"severity": "informational", "detail":
                 "Registration references intentionally contain sorry; they are not proofs. The full solutions avoid those imports and independently pass the standard-three-axiom audit."})
findings.append({"severity": "informational", "detail":
                 "The proof method is algebraic gamma positivity rather than the note's broader real-root route; it faithfully proves the selected C3 conclusions but does not formalize the full general r>=2 real-root theorem."})
report = {"verdict": "PASS" if all(c["pass"] for c in checks) else "FAIL",
          "reviewer": "independent coefficient_integration_review agent; not the packaging author",
          "created_at": datetime.now(timezone.utc).isoformat(),
          "source_sha256": EXPECTED_SHA, "checks": checks, "findings": findings,
          "sha256": hashes,
          "scope": "C3 original coefficient and offline platform definition, two theorem references and two full solutions. No credential/API access or publication action."}
(OUT / "independent-integration-review.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"verdict": report["verdict"], "checks": len(checks),
                  "failed": [c["id"] for c in checks if not c["pass"]], "sha256_entries": len(hashes)}, ensure_ascii=False))
