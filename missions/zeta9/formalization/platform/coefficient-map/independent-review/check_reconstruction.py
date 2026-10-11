"""Independently reconstruct mathematical splices from re-executed Lean facts."""
from pathlib import Path
import hashlib
import json
import sys

sys.stdout.reconfigure(encoding="utf-8")
HERE = Path(__file__).resolve().parent
BATCH = HERE.parent
TASK = BATCH.parents[2]
ROOT = TASK.parents[1]
NS = "ZetaNine.CoefficientMap"
DEFS = ["numerator", "poleProduct", "actualR", "clearedPoleProduct", "clearedR", "leadingPoleCoefficient", "weightedR", "clearedWeightedR", "weightedLeadingPoleCoefficient"]
TARGETS = ["clear_highest_pole", "leadingPoleCoefficient_eq", "weightedLeadingPoleCoefficient_eq_even"]
ARGS = ["n j hj t ht", "n j hj", "n j hn hj W"]
EXPECTED = "e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03"
checks = []
def check(name, okay, detail=None):
    checks.append({"name": name, "pass": bool(okay), "evidence": detail})
    assert okay, name

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
def digest(b):
    return hashlib.sha256(b).hexdigest()
def load(p):
    return json.loads(p.read_text(encoding="utf-8-sig"))
def rows(p):
    return [json.loads(s) for s in p.read_text(encoding="utf-8-sig").splitlines() if s.startswith("{")]
def canonical(rs):
    normalized = []
    for r in rs:
        r = dict(r)
        for k in ["typeDeps", "valueDeps"]:
            if k in r:
                r[k] = sorted(r[k])
        normalized.append(json.dumps(r, sort_keys=True, ensure_ascii=False))
    return sorted(normalized)
def splice(data, edits):
    edge = len(data)
    for a, b, replacement in sorted(set(edits), reverse=True):
        assert 0 <= a <= b <= edge
        data = data[:a] + replacement + data[b:]
        edge = a
    return data

source = (TASK / "formalization/CoefficientMap.lean").read_bytes()
snapshot = (HERE / "oracle-input.lean").read_bytes()
check("original_source_and_reexecuted_parser_snapshot_exact", digest(source) == EXPECTED and source == snapshot and source == (BATCH / "oracle-input.lean").read_bytes())
graph = rows(HERE / "decl_graph.jsonl")
facts = rows(HERE / "sketch_info.jsonl")
check("actual_stage1_graph_reexecuted_matches_author", canonical(graph) == canonical(rows(BATCH / "decl_graph.jsonl")), {"environment_records": len(graph), "source_position_records": sum(g["startLine"] > 0 for g in graph), "generated": [g["name"] for g in graph if g["startLine"] == 0]})
check("actual_stage2_decl_ref_command_spans_reexecuted_match_author", canonical(facts) == canonical(rows(BATCH / "sketch_info.jsonl")), {kind: sum(f["kind"] == kind for f in facts) for kind in ["decl", "ref", "command"]})
byname = {g["userName"]: g for g in graph if g["startLine"] > 0}
decls = [f for f in facts if f["kind"] == "decl"]
refs = [f for f in facts if f["kind"] == "ref"]
commands = [f for f in facts if f["kind"] == "command"]
def declaration(full):
    g = byname[full]
    candidates = [f for f in decls if f["declStart"]["line"] <= g["startLine"] <= f["declEnd"]["line"]]
    assert len(candidates) == 1 and candidates[0]["valStart"] is not None
    return candidates[0]

definition_facts = [declaration(NS + "." + name) for name in DEFS]
check("nine_moved_declarations_are_original_actual_defs", len(definition_facts) == 9 and all(byname[NS + "." + n]["kind"] == "def" for n in DEFS))
check("original_mathematical_core_is_nine_defs_eighteen_theorems", len(byname) == 27 and sum(g["kind"] == "theorem" for g in byname.values()) == 18)
definition_path = "Definitions/Def_ZetaNine_CoefficientMap.lean"
definition_prefix = b"import Mathlib.Algebra.Polynomial.Eval.Defs\nimport Mathlib.Algebra.BigOperators.Ring.Finset\nimport Mathlib.Data.Nat.Choose.Cast\nimport Mathlib.Data.Nat.Factorial.BigOperators\n\nset_option autoImplicit false\nnoncomputable section\nopen scoped BigOperators\nopen Finset Polynomial\n\nnamespace ZetaNine.CoefficientMap\n\n"
definition = definition_prefix + b"\n\n".join(source[f["declStart"]["offset"]:f["declEnd"]["offset"]] for f in definition_facts) + b"\n\nend ZetaNine.CoefficientMap\n"
check("definition_nine_original_parser_spans_reconstructed_exactly", definition == (BATCH / "staged" / definition_path).read_bytes(), {"sha256": digest(definition)})
definitions_request = load(BATCH / "definitions-request.json")
check("definition_request_exact_staged_original_value", len(definitions_request) == 1 and definitions_request[0]["definition"].encode() == definition)
definition_cuts = [(f["declStart"]["offset"], f["declEnd"]["offset"], b"") for f in definition_facts]
diagnostics = [f for f in commands if f["syntaxKind"] == "Lean.Parser.Command.printAxioms"]
diagnostic_cuts = [(f["span"]["start"]["offset"], f["span"]["end"]["offset"], b"") for f in diagnostics]
check("only_eight_parser_certified_diagnostic_commands_removed", len(diagnostics) == 8 and all(source[a:b].startswith(b"#print axioms ") for a,b,_ in diagnostic_cuts))
preamble = "import Definitions.Def_ZetaNine_CoefficientMap\n\nset_option autoImplicit false\nopen Finset Polynomial\nopen ZetaNine.CoefficientMap\n"
problem_request = load(BATCH / "problems-request.json")
check("request_pinned_env_public_and_exact_three_selected_endpoints", problem_request["env"] == "0df444a360eaa60ab8c11dca51a86af692955474" and problem_request["private"] is False and [p["theorem_name"] for p in problem_request["problems"]] == [NS + "." + n for n in TARGETS])
target_details = []
for i, name in enumerate(TARGETS):
    full = NS + "." + name
    d = declaration(full)
    begin, end, val = [d[k]["offset"] for k in ["declStart", "declEnd", "valStart"]]
    target_refs = [r for r in refs if r["const"] == full]
    bindings = [r for r in target_refs if begin <= r["start"]["offset"] < val]
    assert len(bindings) == 1
    binding = bindings[0]
    a,b = binding["start"]["offset"], binding["end"]["offset"]
    assert source[a:b].decode() == name
    signature = source[b:val]
    rename_edits = []
    for r in target_refs:
        x,y = r["start"]["offset"], r["end"]["offset"]
        if any(ca <= x and y <= cb for ca,cb,_ in diagnostic_cuts):
            continue
        old = source[x:y].decode()
        assert old in [name, full]
        new = "checked_" + name if old == name else NS + ".checked_" + name
        rename_edits.append((x,y,new.encode()))
    core = splice(source, definition_cuts + diagnostic_cuts + rename_edits)
    solution = b"import Definitions.Def_ZetaNine_CoefficientMap\n" + core + ("\n\nopen " + NS + "\n\ntheorem solution").encode() + signature + (":= by\n  exact " + NS + ".checked_" + name + " " + ARGS[i] + "\n\n#print axioms solution\n").encode()
    edits = [(a-begin,b-begin,full.encode())]
    if d["docstring"]:
        doc = d["docstring"]
        edits.append((doc["start"]["offset"]-begin,doc["end"]["offset"]-begin,b""))
    formal = splice(source[begin:val],edits).decode().strip() + ":= by sorry"
    reference = (preamble + "\n" + formal + "\n").encode()
    solpath = "Solutions/Sol_ZetaNine_CoefficientMap_" + name + ".lean"
    refpath = "Theorems/Thm_ZetaNine_CoefficientMap_" + name + ".lean"
    check(name + "_solution_recomputed_exact_from_actual_parser_ref_spans", solution == (BATCH / "staged" / solpath).read_bytes(), {"sha256": digest(solution), "rename_spans": [[x,y] for x,y,_ in rename_edits], "helper_proofs_preserved": 18})
    check(name + "_reference_and_request_exact_original_statement_no_extra_binders", reference == (BATCH / "staged" / refpath).read_bytes() and problem_request["problems"][i]["formal_statement"] == formal and problem_request["problems"][i]["preamble"] == preamble, {"original_signature": signature.decode(), "formal_statement_sha256": digest(formal.encode())})
    target_details.append({"theorem": full, "signature": signature.decode(), "solution": solpath, "reference": refpath, "rename_spans": [[x,y] for x,y,_ in rename_edits]})

freeze = []
for line in (BATCH / "SHA256SUMS.txt").read_text(encoding="utf-8-sig").splitlines():
    expected, rel = line.split("  ",1)
    p = (BATCH / rel).resolve()
    assert p.is_relative_to(TASK), rel
    freeze.append({"path": p.relative_to(TASK).as_posix(), "expected": expected, "actual": sha(p)})
check("all_96_frozen_manifest_members_hash_verified", len(freeze) == 96 and all(f["expected"] == f["actual"] for f in freeze))
check("author_freeze_control_hashes_bound", sha(BATCH / "author-audit.json") == "f5d04a3297e7c28f233fec3b7db822c8b63570dab1b00c910b0c3286490fc1e6" and sha(BATCH / "root-copy-plan.json") == "5dadb5ca13fdf18862387315abb9da410fae4a81a5290e875ed972233ef28e8b" and sha(BATCH / "SHA256SUMS.txt") == "1ca21dd468f39c5d064ed63f0207766064f523cadc1ec67220da6f0835e0885b")
result = {"checks":checks,"targets":target_details,"frozen_manifest_members":freeze,"actual_stage1_records":len(graph),"actual_stage2_counts":{kind:sum(f["kind"] == kind for f in facts) for kind in ["decl","ref","command"]}}
(HERE / "reconstruction-report.json").write_text(json.dumps(result,ensure_ascii=False,indent=2) + "\n",encoding="utf-8")
print("Independent parser-span reconstruction PASS: seven staged files, nine definitions, eighteen helper proofs per solution, three original signatures and 96 frozen hashes.")
