"""Transplant actual Jet spans and its genuine cross-module proof closure."""
from pathlib import Path
import hashlib
import json
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
REV = "0df444a360eaa60ab8c11dca51a86af692955474"
NS = "ZetaNine.CoefficientMapJet"
BASE_NS = "ZetaNine.CoefficientMap"
DEFS = ["shiftedVariable", "shiftedNumerator", "shiftedClearedDenominator", "localU", "integerLocalU", "clearedSeries", "weightedClearedSeries", "localCoefficient", "weightedLocalCoefficient"]
BASE_DEFS = ["numerator", "poleProduct", "actualR", "clearedPoleProduct", "clearedR", "leadingPoleCoefficient", "weightedR", "clearedWeightedR", "weightedLeadingPoleCoefficient"]
TARGETS = ["clearedSeries_unique", "coefficient_convolution_explicit", "integer_coefficient_convolution"]
ARGS = ["n j S hS", "n j s hj hs1 hs9 W", "n j s hj hs1 hs9 W"]
MATHLIB = ["Mathlib.RingTheory.PowerSeries.Inverse", "Mathlib.Algebra.Polynomial.Eval.Coeff", "Mathlib.Algebra.BigOperators.NatAntidiagonal"]

def sha(data): return hashlib.sha256(data).hexdigest()
def write(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data if isinstance(data, bytes) else data.encode("utf-8"))
def dump(path, obj): write(path, json.dumps(obj, ensure_ascii=False, indent=2) + "\n")
def rows(path): return [json.loads(s) for s in path.read_text(encoding="utf-8-sig").splitlines() if s.startswith("{")]
def edit(data, edits):
    edge = len(data)
    for start, end, replacement in sorted(set(edits), reverse=True):
        assert 0 <= start <= end <= edge, (start, end, edge)
        data = data[:start] + replacement + data[end:]
        edge = start
    return data

assert sha(SOURCE.read_bytes()) == EXPECTED and sha(BASE_SOURCE.read_bytes()) == BASE_EXPECTED
source = (OUT / "oracle-input.lean").read_bytes()
base_source = (BASE_BATCH / "oracle-input.lean").read_bytes()
assert source == SOURCE.read_bytes().replace(b"\r\n", b"\n") and base_source == BASE_SOURCE.read_bytes().replace(b"\r\n", b"\n")
graph = rows(OUT / "decl_graph.jsonl")
by_name = {r["name"]: r for r in graph}
assert len(graph) == len(by_name) == 65 and not any(r["kind"] == "axiom" for r in graph)
facts = rows(OUT / "sketch_info.jsonl")
decls = [r for r in facts if r["kind"] == "decl"]
refs = [r for r in facts if r["kind"] == "ref"]
commands = [r for r in facts if r["kind"] == "command"]
assert (len(decls), len(refs), len(commands)) == (28, 141, 47)
base_facts = rows(BASE_BATCH / "sketch_info.jsonl")
base_decls = [r for r in base_facts if r["kind"] == "decl"]
execution = json.loads((OUT / "oracle-execution-receipt.json").read_text(encoding="utf-8"))
assert len(execution["rows"]) == 4 and all(r["exit_code"] == 0 for r in execution["rows"])
header_facts = rows(OUT / "header_info.jsonl")
assert len(header_facts) == 1
header = header_facts[0]
assert header["kind"] == "header" and header["start"]["offset"] == 0
header_end = header["end"]["offset"]
assert source[:header_end].decode().strip().splitlines() == ["import missions.zeta9.formalization.CoefficientMap"] + ["import " + m for m in MATHLIB]

def declaration(full):
    matches = [r for r in graph if r["userName"] == full and r["startLine"] > 0]
    assert len(matches) == 1, full
    row = matches[0]
    selected = base_decls if row["module"].endswith(".CoefficientMap") else decls
    matches = [f for f in selected if f["declStart"]["line"] <= row["startLine"] <= f["declEnd"]["line"]]
    assert len(matches) == 1 and matches[0]["valStart"] is not None
    return matches[0]

def closure(seed):
    reached, work = set(), list(seed)
    while work:
        name = work.pop()
        if name in reached: continue
        reached.add(name)
        work.extend(by_name[name]["typeDeps"] + by_name[name]["valueDeps"])
    return reached

jet_source_records = [r for r in graph if r["module"].endswith(".CoefficientMapJet") and r["startLine"] > 0]
assert len(jet_source_records) == 28 and sum(r["kind"] == "def" for r in jet_source_records) == 9
all_core_closure = closure([r["name"] for r in jet_source_records] + [r["name"] for r in graph if r["isInstance"]])
base_helpers = [by_name[name] for name in all_core_closure if by_name[name]["module"].endswith(".CoefficientMap") and by_name[name]["kind"] == "theorem" and by_name[name]["startLine"] > 0]
base_helpers.sort(key=lambda r: r["startLine"])
assert [r["userName"] for r in base_helpers] == [BASE_NS + ".clearedPoleProduct_ne_zero"]
base_helper_facts = [declaration(r["userName"]) for r in base_helpers]
bridge = "open scoped BigOperators\nopen Finset Polynomial\n\nnamespace " + BASE_NS + "\n\n"
bridge += "\n\n".join(base_source[f["declStart"]["offset"]:f["declEnd"]["offset"]].decode("utf-8") for f in base_helper_facts)
bridge += "\n\nend " + BASE_NS + "\n"
write(OUT / "base-proof-bridge.lean.inc", bridge)
definition_facts = [declaration(NS + "." + name) for name in DEFS]
definition_name = "ZetaNine_CoefficientMapJet"
definition_path = "Definitions/Def_" + definition_name + ".lean"
base_definition_path = "Definitions/Def_ZetaNine_CoefficientMap.lean"
definition_code = "import Definitions.Def_ZetaNine_CoefficientMap\n" + "\n".join("import " + m for m in MATHLIB)
definition_code += "\n\nset_option autoImplicit false\nnoncomputable section\nopen scoped BigOperators\nopen Finset Polynomial\n\nnamespace " + NS + "\n\n"
definition_code += "\n\n".join(source[f["declStart"]["offset"]:f["declEnd"]["offset"]].decode("utf-8") for f in definition_facts)
definition_code += "\n\nend " + NS + "\n"
write(OUT / "staged" / definition_path, definition_code)
source_reference = "Zeta(9) research notes: missions/zeta9/research/coefficient-map-jet-2026-10-03.md (actual shifted numerator, cleared denominator, formal local quotient and all nine convolution orders); underlying missions/zeta9/round5/research/arithmetic.md, equation (5), specialized to p=9, one layer q=1, m=n. Frozen verified Lean source missions/zeta9/formalization/CoefficientMapJet.lean, SHA256 " + EXPECTED + "; frozen actual Base source missions/zeta9/formalization/CoefficientMap.lean, SHA256 " + BASE_EXPECTED + "."
definition_nl = r"""Let $n,j$ be natural numbers and let $z$ be a formal variable. Set $T_j(z)=z-j$ and define the actual shifted numerator and cleared denominator by

$$N_{n,j}(z)=n!^7\prod_{i=1}^{n}(T_j(z)-i)\prod_{i=1}^{n}(T_j(z)+n+i),\qquad D_{n,j}(z)=\prod_{0\le k\le n,\ k\ne j}(T_j(z)+k).$$

Set $U_{n,j}(z)=T_j(z)(T_j(z)+n)$. In $\mathbb Q[[z]]$, define $S_{n,j}=N_{n,j}(D_{n,j}^{9})^{-1}$ and, for any $W\in\mathbb Q[X]$, $S^W_{n,j}=S_{n,j}W(U_{n,j})$. For natural $s$, define $c_{n,j,s}=[z^{9-s}]S_{n,j}$ and $c^W_{n,j,s}=[z^{9-s}]S^W_{n,j}$ using natural-number subtraction; the pole-order interpretation is restricted to $1\le s\le9$ and $j\le n$. Also define the integer polynomial $U^{\mathbb Z}_{n,j}=-j(n-j)+(n-2j)X+X^2$, where $n-j$ is natural subtraction.

These nine constructions use genuine shifted finite products and formal power-series coefficients. They provide the interface for uniqueness and polynomial-multiplier convolution. Formal inversion here is a ring construction, with its nonzero-constant justification proved in the Solution modules. It does not assert numerical evaluation or convergence of an infinite series."""
dump(OUT / "definitions-request.json", [{"definition_name": definition_name, "definition_title": "Actual shifted products and formal local coefficient series", "definition": definition_code, "natural_language_statement": definition_nl, "source": source_reference + " The nine definition declarations retain their exact original Lean parser spans.", "tags": ["number-theory", "formal-power-series", "rational-functions", "formalization"], "env": REV, "private": False}])
titles = ["Uniqueness of the actual cleared formal local series", "All nine actual local coefficient convolutions", "Actual local convolution with integer polynomial multipliers"]
natural = [
r"""For any natural numbers $n,j$, let $T_j(z)=z-j$, $N_{n,j}(z)=n!^7\prod_{i=1}^{n}(T_j(z)-i)\prod_{i=1}^{n}(T_j(z)+n+i)$ and $D_{n,j}(z)=\prod_{0\le k\le n,\ k\ne j}(T_j(z)+k)$. Let $S_{n,j}=N_{n,j}(D_{n,j}^9)^{-1}$ in $\mathbb Q[[z]]$. For every formal power series $S\in\mathbb Q[[z]]$,

$$S D_{n,j}^9=N_{n,j}\quad\Longrightarrow\quad S=S_{n,j}.$$

The actual denominator has nonzero constant coefficient, so this is the unique formal local quotient of the genuine shifted products. The uniqueness statement holds for all natural $j$; its application to a pole of the original rational function uses $j\le n$. No numerical evaluation or analytic convergence of the formal series is asserted.""",
r"""Let $n,j,s$ be natural numbers with $j\le n$ and $1\le s\le9$, and let $W\in\mathbb Q[X]$ be arbitrary. From the actual shifted numerator $N_{n,j}$ and erased-factor denominator $D_{n,j}$, define $S_{n,j}=N_{n,j}(D_{n,j}^9)^{-1}\in\mathbb Q[[z]]$. Set $U_{n,j}(z)=-j(n-j)+(n-2j)z+z^2$, $c_{n,j,\ell}=[z^{9-\ell}]S_{n,j}$ and $c^W_{n,j,s}=[z^{9-s}](S_{n,j}W(U_{n,j}))$. Then

$$c^W_{n,j,s}=\sum_{\ell=s}^{9}c_{n,j,\ell}[z^{\ell-s}]W\bigl(-j(n-j)+(n-2j)z+z^2\bigr).$$

Every coefficient is extracted from the genuine formal quotient. The identity covers all nine local orders, all natural $n$ including zero, and all polynomial multipliers including zero. It supplies a local finite convolution; it does not assert a global partial-fraction formula, a full aggregate coefficient map, or its inverse.""",
r"""Let $n,j,s$ be natural numbers with $j\le n$ and $1\le s\le9$, and let $W\in\mathbb Z[X]$ be arbitrary. Put $U^{\mathbb Z}_{n,j}(z)=-j(n-j)+(n-2j)z+z^2\in\mathbb Z[z]$, and let $\overline W\in\mathbb Q[X]$ be the coefficientwise image of $W$. Define the actual formal quotient $S_{n,j}=N_{n,j}(D_{n,j}^9)^{-1}$ from the shifted finite products and set $c_{n,j,\ell}=[z^{9-\ell}]S_{n,j}$, $c^{\overline W}_{n,j,s}=[z^{9-s}](S_{n,j}\overline W(U_{n,j}))$. Then

$$c^{\overline W}_{n,j,s}=\sum_{\ell=s}^{9}c_{n,j,\ell}\,\iota\!\left([z^{\ell-s}]W(U^{\mathbb Z}_{n,j}(z))\right),$$

where $\iota:\mathbb Z\to\mathbb Q$ is the natural inclusion. The multiplier coefficients inside $\iota$ are integers, while the actual local coefficients $c_{n,j,\ell}$ remain rational and need not be integers. This applies in particular to integer quartic multipliers. Arbitrary-degree local validity does not imply the degree constraints or convergence needed for an infinite-sum application."""
]
preamble = "import " + definition_path.removesuffix(".lean").replace("/", ".") + "\n\nset_option autoImplicit false\nopen scoped BigOperators\nopen Finset Polynomial\nopen " + NS + "\n"
deletions = [(f["declStart"]["offset"], f["declEnd"]["offset"], b"") for f in definition_facts]
diagnostic_facts = [f for f in commands if f["syntaxKind"] == "Lean.Parser.Command.printAxioms"]
assert len(diagnostic_facts) == 10
diagnostics = [(f["span"]["start"]["offset"], f["span"]["end"]["offset"], b"") for f in diagnostic_facts]
solution_header = "import " + definition_path.removesuffix(".lean").replace("/", ".") + "\nimport Mathlib.Tactic\n" + "\n".join("import " + m for m in MATHLIB) + "\n\n" + bridge
provenance = {"source": SOURCE.relative_to(ROOT).as_posix(), "source_sha256": EXPECTED, "source_bytes": len(SOURCE.read_bytes()), "base_source": BASE_SOURCE.relative_to(ROOT).as_posix(), "base_source_sha256": BASE_EXPECTED,
              "source_position_authority": "Actually executed official Stage1 cross-module declaration graph, official Stage2 parser/ref oracle, and exact Lean Parser.parseHeader span. Frozen prior actual Base parser snapshot and facts are reused hash-bound.", "regex_mathematical_source_position_queries": False,
              "stage1_records": len(graph), "Jet_source_declarations": len(jet_source_records), "Jet_spanless_generated_records": [r for r in graph if r["module"].endswith(".CoefficientMapJet") and r["startLine"] == 0],
              "stage2_fact_counts": {"decl": len(decls), "ref": len(refs), "command": len(commands)}, "definition_facts": definition_facts, "definition_sha256": sha(definition_code.encode()),
              "base_helper_declaration_facts": base_helper_facts, "base_helper_names": [r["userName"] for r in base_helpers], "base_bridge_sha256": sha(bridge.encode()), "header_fact": header, "solution_header": solution_header,
              "base_parser_facts": (BASE_BATCH / "sketch_info.jsonl").relative_to(TASK).as_posix(), "base_parser_facts_sha256": sha((BASE_BATCH / "sketch_info.jsonl").read_bytes()), "base_parser_snapshot_sha256": sha(base_source),
              "base_definition": base_definition_path, "base_definition_source_sha256": sha((BASE_BATCH / "staged" / base_definition_path).read_bytes()),
              "diagnostic_deletion_facts": diagnostic_facts, "all_Jet_mathematical_helpers_preserved": True, "targets": {}}
problems, target_plan = [], []
for i, short in enumerate(TARGETS):
    full = NS + "." + short
    fact = declaration(full)
    start, value = [fact[k]["offset"] for k in ["declStart", "valStart"]]
    target_refs = [r for r in refs if r["const"] == full]
    binding = [r for r in target_refs if start <= r["start"]["offset"] < value]
    assert len(binding) == 1
    binding = binding[0]
    bs, be = binding["start"]["offset"], binding["end"]["offset"]
    assert source[bs:be].decode() == short
    signature = source[be:value].decode()
    checked = "checked_" + short
    renames, removed_refs = [], []
    for ref in target_refs:
        a, b = ref["start"]["offset"], ref["end"]["offset"]
        old = source[a:b].decode()
        assert old in [short, full]
        if any(ca <= a and b <= cb for ca, cb, _ in diagnostics):
            removed_refs.append(ref)
        else:
            renames.append((a, b, (checked if old == short else NS + "." + checked).encode()))
    core = edit(source, [(0, header_end, b"")] + deletions + diagnostics + renames).decode()
    solution = solution_header + "\n" + core + "\n\nopen " + NS + "\n\ntheorem solution" + signature + ":= by\n  exact " + NS + "." + checked + " " + ARGS[i] + "\n\n#print axioms solution\n"
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
    problems.append({"theorem_name": full, "theorem_title": titles[i], "formal_statement": formal, "natural_language_statement": natural[i], "preamble": preamble, "source": source_reference + f" Original endpoint declaration lines {fact['declStart']['line']}–{fact['declEnd']['line']}.", "tags": ["number-theory", "formal-power-series", "coefficient-convolution", "formalization"]})
    target_plan.append({"theorem_name": full, "local_solution": solution_path, "local_reference": reference_path, "wrapper_arguments": ARGS[i], "definition_dependencies": ["ZetaNine_CoefficientMap", definition_name]})
    provenance["targets"][full] = {"stage2_declaration_fact": fact, "stage2_target_reference_facts": target_refs, "references_removed_with_diagnostics": removed_refs, "actual_rename_spans": [[a,b] for a,b,_ in renames], "binding_fact": binding, "checked_name": NS + "." + checked, "solution_sha256": sha(solution.encode()), "reference_sha256": sha(reference.encode()), "formal_statement_sha256": sha(formal.encode()), "extra_top_level_solution_binders": [], "wrapper_arguments": ARGS[i]}
dump(OUT / "problems-request.json", {"env": REV, "private": False, "problems": problems})
dump(OUT / "target-plan.json", {"definition_name": definition_name, "local_definition": definition_path, "base_definition": base_definition_path, "targets": target_plan, "API_request_bodies_contain_only_documented_fields": True})
dump(OUT / "integration-provenance.json", provenance)
roots = [NS + "." + short for short in TARGETS]
root_union = closure(roots + [r["name"] for r in graph if r["isInstance"]])
dump(OUT / "decl-plan.json", {"selected_public_endpoints": roots, "root_union_reachable_declarations": sorted(root_union), "all_retained_Jet_core_closure": sorted(all_core_closure),
                             "retained_Jet_definition_names": [NS + "." + name for name in DEFS], "retained_Base_definition_names": [BASE_NS + "." + name for name in BASE_DEFS],
                             "Jet_source_declarations": 28, "moved_Jet_definitions": 9, "Jet_helpers_and_theorems_preserved_inline": 19,
                             "Jet_graph_records": 37, "Jet_spanless_generated_records": 9, "Base_inline_helper_names": [r["userName"] for r in base_helpers],
                             "no_lemmas_in_Def": True, "no_closed_formula_substitute_Def": True, "new_external_theorem_boundaries": [],
                             "retention_reason": "Keep all 19 original Jet proofs unchanged; retain all nine genuine Jet definitions. Inline the actual Base proof closure required by the retained Jet core; generated eq_1 auxiliaries are regenerated from their original defs rather than treated as source declarations."})

def type_report(module, names):
    code = "import " + module + "\nimport Lean\nopen Lean\nset_option pp.fullNames true\nset_option pp.universes false\nrun_meta do\n  let emit (label : String) (name : Name) : Lean.Meta.MetaM Unit := do\n    let ci ← getConstInfo name\n    let typ ← Lean.Meta.ppExpr ci.type\n    let value ← match ci with\n      | .defnInfo d => pure (some (← Lean.Meta.ppExpr d.value).pretty)\n      | _ => pure none\n    let axioms ← Lean.collectAxioms name\n    IO.println (Json.mkObj [(\"label\", Json.str label), (\"declaration\", Json.str name.toString),\n      (\"type\", Json.str typ.pretty), (\"value\", toJson value), (\"axioms\", toJson (axioms.toList.map Name.toString))]).compress\n"
    return code + "\n".join('  emit "' + label + '" `' + name for label, name in names) + "\n"
def_names = [BASE_NS + "." + name for name in BASE_DEFS] + [NS + "." + name for name in DEFS]
write(OUT / "types_original.lean", type_report("missions.zeta9.formalization.CoefficientMapJet", [(name,name) for name in def_names + roots]))
write(OUT / "types_definition.lean", type_report(definition_path.removesuffix(".lean").replace("/", "."), [(name,name) for name in def_names]))
for i, p in enumerate(target_plan):
    for kind, decl, key in [("solution", "solution", "local_solution"), ("reference", p["theorem_name"], "local_reference")]:
        names = [(name,name) for name in def_names] + [(p["theorem_name"], decl)]
        write(OUT / f"types_{i}_{kind}.lean", type_report(p[key].removesuffix(".lean").replace("/", "."), names))
print(json.dumps({"definition": definition_path, "Jet_definitions": 9, "Jet_inline_proofs": 19, "actual_Base_inline_helpers": provenance["base_helper_names"], "source_sha256": EXPECTED}, ensure_ascii=False, indent=2))
