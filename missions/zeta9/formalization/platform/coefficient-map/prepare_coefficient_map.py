"""Offline transplant from executed official Lean declaration/ref byte spans."""
from pathlib import Path
import hashlib
import json
import sys

sys.stdout.reconfigure(encoding="utf-8")
OUT = Path(__file__).resolve().parent
TASK = OUT.parents[2]
ROOT = TASK.parents[1]
SOURCE = TASK / "formalization/CoefficientMap.lean"
EXPECTED = "e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03"
REV = "0df444a360eaa60ab8c11dca51a86af692955474"
NS = "ZetaNine.CoefficientMap"
DEFS = ["numerator", "poleProduct", "actualR", "clearedPoleProduct", "clearedR", "leadingPoleCoefficient", "weightedR", "clearedWeightedR", "weightedLeadingPoleCoefficient"]
TARGETS = ["clear_highest_pole", "leadingPoleCoefficient_eq", "weightedLeadingPoleCoefficient_eq_even"]
ARGS = ["n j hj t ht", "n j hj", "n j hn hj W"]

def sha(data):
    return hashlib.sha256(data).hexdigest()

def write(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data if isinstance(data, bytes) else data.encode("utf-8"))

def dump(path, obj):
    write(path, json.dumps(obj, ensure_ascii=False, indent=2) + "\n")

def rows(path):
    return [json.loads(s) for s in path.read_text(encoding="utf-8-sig").splitlines() if s.startswith("{")]

def edit(data, edits):
    edge = len(data)
    for start, end, replacement in sorted(set(edits), reverse=True):
        assert 0 <= start <= end <= edge, (start, end, edge)
        data = data[:start] + replacement + data[end:]
        edge = start
    return data

assert sha(SOURCE.read_bytes()) == EXPECTED
source = (OUT / "oracle-input.lean").read_bytes()
assert source == SOURCE.read_bytes().replace(b"\r\n", b"\n")
graph = rows(OUT / "decl_graph.jsonl")
by_name = {r["name"]: r for r in graph}
assert len(graph) == len(by_name)
assert not [r for r in graph if r["kind"] == "axiom"]
facts = rows(OUT / "sketch_info.jsonl")
decls = [r for r in facts if r["kind"] == "decl"]
refs = [r for r in facts if r["kind"] == "ref"]
commands = [r for r in facts if r["kind"] == "command"]
execution = json.loads((OUT / "oracle-execution-receipt.json").read_text(encoding="utf-8"))
assert all(r["exit_code"] == 0 for r in execution["rows"])
assert (len(decls), len(refs), len(commands)) == (27, 92, 45)

def declaration(full):
    graph_matches = [r for r in graph if r["userName"] == full and r["startLine"] > 0]
    assert len(graph_matches) == 1, full
    row = graph_matches[0]
    matches = [f for f in decls if f["declStart"]["line"] <= row["startLine"] <= f["declEnd"]["line"]]
    assert len(matches) == 1 and matches[0]["valStart"] is not None
    return matches[0]

definition_facts = [declaration(NS + "." + name) for name in DEFS]
assert {r["userName"] for r in graph if r["kind"] == "def" and r["startLine"] > 0} == {NS + "." + name for name in DEFS}
definition_imports = ["Mathlib.Algebra.Polynomial.Eval.Defs", "Mathlib.Algebra.BigOperators.Ring.Finset", "Mathlib.Data.Nat.Choose.Cast", "Mathlib.Data.Nat.Factorial.BigOperators"]
definition_code = "\n".join("import " + m for m in definition_imports) + "\n\nset_option autoImplicit false\nnoncomputable section\nopen scoped BigOperators\nopen Finset Polynomial\n\nnamespace " + NS + "\n\n"
definition_code += "\n\n".join(source[f["declStart"]["offset"]:f["declEnd"]["offset"]].decode("utf-8") for f in definition_facts)
definition_code += "\n\nend " + NS + "\n"
definition_name = "ZetaNine_CoefficientMap"
definition_path = "Definitions/Def_" + definition_name + ".lean"
write(OUT / "staged" / definition_path, definition_code)
source_reference = "Zeta(9) research notes: missions/zeta9/research/coefficient-map-finite-entry-2026-10-03.md (actual product definitions and highest cleared-pole coefficient); underlying missions/zeta9/round5/research/arithmetic.md, equations (1), (5), and (6), specialized to p=9, one layer q=1, m=n. Frozen verified Lean source missions/zeta9/formalization/CoefficientMap.lean, SHA256 " + EXPECTED + "."
definition_nl = r"""Let $n,j$ be natural numbers and let $t$ be rational. The actual numerator and pole product are

$$N_n(t)=n!^7\prod_{i=1}^{n}(t-i)\prod_{i=1}^{n}(t+n+i),\qquad Q_n(t)=\prod_{k=0}^{n}(t+k),\qquad R_n(t)=\frac{N_n(t)}{Q_n(t)^9}.$$

Let $Q_{n,j}(t)$ be the product over $0\le k\le n$ with $k\ne j$, and set $\widetilde R_{n,j}(t)=N_n(t)/Q_{n,j}(t)^9$ and $C_{n,j}=\widetilde R_{n,j}(-j)$. For a rational polynomial $W$, the actual weighted function is $R_n(t)W(t(t+n))$; its cleared expression and highest cleared-pole value are defined by multiplying $\widetilde R_{n,j}$ by the same polynomial evaluation and then evaluating at $t=-j$.

These finite-product constructions provide the interface for clearing a pole and computing the actual highest coefficient. No binomial coefficient closed formula is used as a definition. The unmodified rational division operations are total; a pole coefficient uses the cleared expression, not $R_n(-j)$."""
definition_request = {"definition_name": definition_name, "definition_title": "Actual rational function and cleared highest-pole coefficient", "definition": definition_code, "natural_language_statement": definition_nl, "source": source_reference + " Definition declarations are the exact original Lean parser spans.", "tags": ["number-theory", "rational-functions", "finite-products", "formalization"], "env": REV, "private": False}
dump(OUT / "definitions-request.json", [definition_request])

titles = ["Clearing the actual highest pole at every regular point", "Closed formula for the actual highest cleared-pole coefficient", "Actual weighted highest-pole coefficient at every even order"]
natural = [
r"""Let $n,j$ be natural numbers with $j\le n$. Define $N_n(t)=n!^7\prod_{i=1}^{n}(t-i)\prod_{i=1}^{n}(t+n+i)$, $Q_n(t)=\prod_{k=0}^{n}(t+k)$ and $R_n(t)=N_n(t)/Q_n(t)^9$. Let $Q_{n,j}$ omit the factor $t+j$, and write $\widetilde R_{n,j}=N_n/Q_{n,j}^9$. At every rational point $t$ satisfying $t+k\ne0$ for all $0\le k\le n$,

$$R_n(t)(t+j)^9=\widetilde R_{n,j}(t).$$

This identifies the actual cleared expression on the regular domain. It is a finite clearing identity; evaluation of the uncleared rational function at a pole is not used as a coefficient.""",
r"""For natural numbers $n,j$ with $j\le n$, let $C_{n,j}$ be the value at $t=-j$ of the actual cleared expression $N_n(t)/Q_{n,j}(t)^9$, where $N_n(t)=n!^7\prod_{i=1}^{n}(t-i)\prod_{i=1}^{n}(t+n+i)$ and $Q_{n,j}(t)=\prod_{0\le k\le n,\ k\ne j}(t+k)$. Then

$$C_{n,j}=(-1)^{n+j}\binom{n}{j}^{9}\binom{n+j}{n}\binom{2n-j}{n}.$$

The coefficient is defined by the original products and clearing operation; this identity computes that value. It covers both endpoint poles $j=0,n$ and the case $n=0$, without a parity assumption.""",
r"""Let $n,j$ be natural numbers, with $n$ even and $j\le n$, and let $W\in\mathbb Q[X]$ be any rational polynomial. Starting from the actual rational function $R_n(t)=N_n(t)/Q_n(t)^9$, multiply by $W(t(t+n))$. Define its highest cleared-pole value $C^W_{n,j}$ by evaluating $N_n(t)W(t(t+n))/Q_{n,j}(t)^9$ at $t=-j$. Then

$$C^W_{n,j}=(-1)^j\binom{n}{j}^{9}\binom{n+j}{n}\binom{2n-j}{n}\,W\bigl(-j(n-j)\bigr).$$

This computes the effect of the actual polynomial multiplier on the highest cleared-pole value. The multiplier is arbitrary, including the zero polynomial, and the weighted coefficient can be zero. The statement covers $n=0$ and does not assert a full Laurent expansion, a lower-coefficient map, or an infinite-sum identity."""
]
preamble = "import " + definition_path.removesuffix(".lean").replace("/", ".") + "\n\nset_option autoImplicit false\nopen Finset Polynomial\nopen " + NS + "\n"
deletions = [(f["declStart"]["offset"], f["declEnd"]["offset"], b"") for f in definition_facts]
diagnostics = [f for f in commands if f["syntaxKind"] == "Lean.Parser.Command.printAxioms"]
diagnostic_cuts = [(f["span"]["start"]["offset"], f["span"]["end"]["offset"], b"") for f in diagnostics]
problems, target_plan = [], []
provenance = {"source": SOURCE.relative_to(ROOT).as_posix(), "source_sha256": EXPECTED, "source_bytes": len(SOURCE.read_bytes()), "oracle_input_sha256": sha(source), "oracle_input_bytes": len(source), "source_position_authority": "Actually executed official Lean Stage1 declaration graph and Stage2 parser/ref oracle. The Stage2 command-span extension removes diagnostic print commands only.", "regex_mathematical_source_position_queries": False, "stage1_declarations": len(graph), "stage2_fact_counts": {"decl": len(decls), "ref": len(refs), "command": len(commands)}, "definition_facts": definition_facts, "definition_sha256": sha(definition_code.encode()), "diagnostic_deletion_facts": diagnostics, "all_mathematical_helper_declarations_preserved": True, "targets": {}}
for i, short in enumerate(TARGETS):
    full = NS + "." + short
    fact = declaration(full)
    start, end, value = [fact[k]["offset"] for k in ["declStart", "declEnd", "valStart"]]
    target_refs = [r for r in refs if r["const"] == full]
    binding = [r for r in target_refs if start <= r["start"]["offset"] < value]
    assert len(binding) == 1
    binding = binding[0]
    bs, be = binding["start"]["offset"], binding["end"]["offset"]
    assert source[bs:be].decode() == short
    signature = source[be:value].decode()
    checked = "checked_" + short
    renames = []
    removed_diagnostic_refs = []
    for ref in target_refs:
        a, b = ref["start"]["offset"], ref["end"]["offset"]
        name = source[a:b].decode()
        assert name in [short, full]
        if any(ca <= a and b <= cb for ca, cb, _ in diagnostic_cuts):
            removed_diagnostic_refs.append(ref)
            continue
        renames.append((a, b, (checked if name == short else NS + "." + checked).encode()))
    core = edit(source, deletions + diagnostic_cuts + renames).decode()
    solution = "import " + definition_path.removesuffix(".lean").replace("/", ".") + "\n" + core + "\n\nopen " + NS + "\n\ntheorem solution" + signature + ":= by\n  exact " + NS + "." + checked + " " + ARGS[i] + "\n\n#print axioms solution\n"
    formal_edits = [(bs-start, be-start, full.encode())]
    if fact["docstring"]:
        doc = fact["docstring"]
        formal_edits.append((doc["start"]["offset"]-start, doc["end"]["offset"]-start, b""))
    formal = edit(source[start:value], formal_edits).decode().strip() + ":= by sorry"
    solution_path = "Solutions/Sol_" + full.replace(".", "_") + ".lean"
    reference_path = "Theorems/Thm_" + full.replace(".", "_") + ".lean"
    reference = preamble + "\n" + formal + "\n"
    write(OUT / "staged" / solution_path, solution)
    write(OUT / "staged" / reference_path, reference)
    problems.append({"theorem_name": full, "theorem_title": titles[i], "formal_statement": formal, "natural_language_statement": natural[i], "preamble": preamble, "source": source_reference + f" Original endpoint declaration lines {fact['declStart']['line']}–{fact['declEnd']['line']}.", "tags": ["number-theory", "rational-functions", "pole-coefficients", "formalization"]})
    target_plan.append({"theorem_name": full, "local_solution": solution_path, "local_reference": reference_path, "wrapper_arguments": ARGS[i], "definition_dependencies": [definition_name]})
    provenance["targets"][full] = {"stage2_declaration_fact": fact, "stage2_target_reference_facts": target_refs, "references_removed_with_diagnostic_commands": removed_diagnostic_refs, "actual_rename_spans": [[a,b] for a,b,_ in renames], "binding_fact": binding, "checked_name": NS + "." + checked, "deleted_definition_spans": [[a,b] for a,b,_ in deletions], "diagnostic_deletion_spans": [[a,b] for a,b,_ in diagnostic_cuts], "solution_sha256": sha(solution.encode()), "reference_sha256": sha(reference.encode()), "formal_statement_sha256": sha(formal.encode()), "extra_top_level_solution_binders": [], "wrapper_arguments": ARGS[i]}
dump(OUT / "problems-request.json", {"env": REV, "private": False, "problems": problems})
dump(OUT / "target-plan.json", {"definition_name": definition_name, "local_definition": definition_path, "targets": target_plan, "API_request_bodies_contain_only_documented_fields": True})
dump(OUT / "integration-provenance.json", provenance)

roots = [NS + "." + short for short in TARGETS]
work = roots + [r["name"] for r in graph if r["isInstance"]]
reachable = set()
while work:
    name = work.pop()
    if name in reachable: continue
    reachable.add(name)
    work.extend(by_name[name]["typeDeps"] + by_name[name]["valueDeps"])
dump(OUT / "decl-plan.json", {"selected_public_endpoints": roots, "root_union_reachable_declarations": sorted(reachable), "root_union_definition_names": sorted(name for name in reachable if by_name[name]["kind"] == "def"), "retained_definition_names": [NS + "." + name for name in DEFS], "additional_actual_API_definition": NS + ".weightedR", "retention_reason": "Keep the complete original mathematical helper core unchanged. The actual weightedR API is used by the retained original clear_weighted_highest_pole theorem and describes the actual weighted rational function, although the three selected public roots do not require it directly.", "retained_all_source_mathematical_declarations": 27, "moved_definition_declarations": 9, "proof_helpers_and_theorems_preserved_inline": 18, "no_lemmas_in_Def": True, "no_closed_formula_substitute_Def": True, "only_deleted_nondeclaration_commands": "Eight exact parser-certified #print axioms diagnostic spans.", "new_external_theorem_boundaries": []})

def type_report(module, names):
    code = "import " + module + "\nimport Lean\nopen Lean\nset_option pp.fullNames true\nset_option pp.universes false\nrun_meta do\n  let emit (label : String) (name : Name) : Lean.Meta.MetaM Unit := do\n    let ci ← getConstInfo name\n    let typ ← Lean.Meta.ppExpr ci.type\n    let value ← match ci with\n      | .defnInfo d => pure (some (← Lean.Meta.ppExpr d.value).pretty)\n      | _ => pure none\n    let axioms ← Lean.collectAxioms name\n    IO.println (Json.mkObj [(\"label\", Json.str label), (\"declaration\", Json.str name.toString),\n      (\"type\", Json.str typ.pretty), (\"value\", toJson value), (\"axioms\", toJson (axioms.toList.map Name.toString))]).compress\n"
    return code + "\n".join('  emit "' + label + '" `' + name for label, name in names) + "\n"

def_names = [NS + "." + name for name in DEFS]
write(OUT / "types_original.lean", type_report("missions.zeta9.formalization.CoefficientMap", [(name,name) for name in def_names + roots]))
write(OUT / "types_definition.lean", type_report(definition_path.removesuffix(".lean").replace("/", "."), [(name,name) for name in def_names]))
for i, p in enumerate(target_plan):
    for kind, decl, key in [("solution", "solution", "local_solution"), ("reference", p["theorem_name"], "local_reference")]:
        module = p[key].removesuffix(".lean").replace("/", ".")
        names = [(name,name) for name in def_names] + [(p["theorem_name"], decl)]
        write(OUT / f"types_{i}_{kind}.lean", type_report(module, names))
print(json.dumps({"definition": definition_path, "definitions": len(DEFS), "endpoints": roots, "source_sha256": EXPECTED, "actual_oracle_span_generation": True}, ensure_ascii=False, indent=2))
