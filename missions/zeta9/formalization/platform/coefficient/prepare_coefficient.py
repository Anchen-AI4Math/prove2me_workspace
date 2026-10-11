"""Offline C3 transplantation driven only by actual Lean graph/sketch facts.

Every source cut and rename uses Stage2 byte spans. No regex is used to locate
declarations, proof cuts, docstrings, binding names, or reference occurrences.
"""
from pathlib import Path
import hashlib
import json

OUT = Path(__file__).resolve().parent
TASK = OUT.parents[2]
ROOT = TASK.parents[1]
SOURCE = TASK / "formalization/ShortZeroCoefficient.lean"
EXPECTED = "9bf18387c4a51dd6dca03ecf197fc1cd85337fabf5b1d3421e2302e452347dbc"
NAMESPACE = "ZetaNine.ShortZeroCoefficient"

def sha(data):
    return hashlib.sha256(data).hexdigest()

def load(path):
    return json.loads(path.read_text(encoding="utf-8-sig"))

def write(path, text):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(text.encode("utf-8"))

source_disk = SOURCE.read_bytes()
assert sha(source_disk) == EXPECTED
source = (OUT / "oracle-input.lean").read_bytes()
assert source == source_disk.replace(b"\r\n", b"\n"), "Oracle input differs by more than Lean mkInputContext CRLF normalization"
candidate = load(TASK / "formalization/platform/coefficient-review-candidates.json")
assert candidate["verified_source_sha256"] == EXPECTED
graph = [json.loads(line) for line in (OUT / "decl_graph.jsonl").read_text(encoding="utf-8-sig").splitlines() if line.startswith("{")]
facts = [json.loads(line) for line in (OUT / "sketch_info.jsonl").read_text(encoding="utf-8-sig").splitlines() if line.startswith("{")]
decls = [row for row in facts if row["kind"] == "decl"]
refs = [row for row in facts if row["kind"] == "ref"]
assert len(decls) == 104 and len(refs) == 578

def declaration(full):
    row = next(row for row in graph if row["userName"] == full and row["startLine"] > 0)
    matches = [fact for fact in decls if fact["declStart"]["line"] <= row["startLine"] <= fact["declEnd"]["line"]]
    assert len(matches) == 1, full
    return matches[0]

def transform(data, edits):
    edits = sorted(set(edits), reverse=True)
    boundary = len(data)
    for start, end, replacement in edits:
        assert 0 <= start <= end <= boundary, (start, end, boundary)
        data = data[:start] + replacement + data[end:]
        boundary = start
    return data

definitions = [declaration(NAMESPACE + "." + name) for name in ["weightedCoeff", "A"]]
definition_decls = b"\n\n".join(source[row["declStart"]["offset"]:row["declEnd"]["offset"]] for row in definitions).decode("utf-8")
definition_imports = "\n".join([
    "import Mathlib.Data.Nat.Choose.Basic",
    "import Mathlib.Algebra.BigOperators.Group.Finset.Basic",
    "import Mathlib.Data.Finset.Range",
    "import Mathlib.Data.Int.Basic",
])
definition_code = definition_imports + "\n\nset_option autoImplicit false\nopen scoped BigOperators\n\nnamespace " + NAMESPACE + "\n\n" + definition_decls + "\n\nend " + NAMESPACE + "\n"
definition = dict(candidate["definitions"][0])
definition["definition"] = definition_code
definition_path = ROOT / definition["local_path"]
if definition_path.exists() and definition_path.read_bytes() != definition_code.encode("utf-8"):
    # Only recover this script's own pre-snapshot failed draft, never another file.
    old_decls = b"\n\n".join(source_disk[row["declStart"]["offset"]:row["declEnd"]["offset"]] for row in definitions).decode("utf-8")
    old_code = definition_imports + "\n\nset_option autoImplicit false\nopen scoped BigOperators\n\nnamespace " + NAMESPACE + "\n\n" + old_decls + "\n\nend " + NAMESPACE + "\n"
    assert definition_path.read_bytes() == old_code.encode("utf-8"), "Existing independent shared definition would be changed"
write(definition_path, definition_code)

problems = []
provenance = {
    "source": SOURCE.relative_to(ROOT).as_posix(), "source_sha256": EXPECTED,
    "source_bytes": len(source_disk), "oracle_input_bytes": len(source), "oracle_input_sha256": sha(source),
    "position_source": "Official extract_decl_graph.lean and extract_sketch_info.lean, actually executed under Lean 4.33.1; every byte span addresses the persisted actual oracle input",
    "stage1_declarations": len(graph), "stage2_declarations": len(decls), "stage2_references": len(refs),
    "extractor_api_patches": [{"change": "Persist Parser.mkInputContext.inputString with IO.FS.writeBinFile", "reason": "Lean Parser.mkInputContext defaults normalizeLineEndings=true and calls crlfToLf; its actual input removes 882 CRLF bytes. The original source hash is retained separately and no mathematical tokens change."}], "regex_mathematical_source_position_queries": False,
    "definition_selected_from_exact_stage2_decl_spans": [row for row in definitions],
    "targets": {},
}
deletion_edits = [(row["declStart"]["offset"], row["declEnd"]["offset"], b"") for row in definitions]
for p in candidate["problems"]:
    p = dict(p)
    full = p["theorem_name"]
    short = full.rsplit(".", 1)[-1]
    fact = declaration(full)
    dstart, dend, vstart = (fact[key]["offset"] for key in ["declStart", "declEnd", "valStart"])
    target_refs = [row for row in refs if row["const"] == full]
    bindings = [row for row in target_refs if dstart <= row["start"]["offset"] < vstart]
    assert len(bindings) == 1, (full, "missing binding ref fact")
    binding = bindings[0]
    bstart, bend = binding["start"]["offset"], binding["end"]["offset"]
    assert source[bstart:bend].decode("utf-8") == short
    signature = source[bend:vstart].decode("utf-8")
    checked = "checked_" + short
    rename_edits = []
    for ref in target_refs:
        rstart, rend = ref["start"]["offset"], ref["end"]["offset"]
        text = source[rstart:rend].decode("utf-8")
        assert text in [short, full], (full, text)
        replacement = checked if text == short else NAMESPACE + "." + checked
        rename_edits.append((rstart, rend, replacement.encode("utf-8")))
    core = transform(source, deletion_edits + rename_edits).decode("utf-8")
    args = {"A_even_signed_lower": "d m", "A_ne_zero_of_even": "n m hn"}[short]
    solution = "import Definitions.Def_ZetaNine_ShortZeroCoefficient\n" + core + "\n\nopen " + NAMESPACE + "\n\ntheorem solution" + signature + ":= by\n  exact " + NAMESPACE + "." + checked + " " + args + "\n\n#print axioms solution\n"
    solution_path = ROOT / p["local_solution"]
    assert not solution_path.exists() or solution_path.read_bytes() == solution.encode("utf-8"), "Existing solution would be changed"
    write(solution_path, solution)
    stub_edits = [(bstart - dstart, bend - dstart, full.encode("utf-8"))]
    if fact["docstring"]:
        stub_edits.append((fact["docstring"]["start"]["offset"] - dstart,
                           fact["docstring"]["end"]["offset"] - dstart, b""))
    formal = transform(source[dstart:vstart], stub_edits).decode("utf-8").strip() + ":= by sorry"
    p["formal_statement"] = formal
    reference = p["preamble"] + "\nset_option autoImplicit false\n\n" + formal + "\n"
    reference_path = ROOT / p["local_reference"]
    assert not reference_path.exists() or reference_path.read_bytes() == reference.encode("utf-8"), "Existing reference would be changed"
    write(reference_path, reference)
    p["source"] += f" Verified Lean source: missions/zeta9/formalization/ShortZeroCoefficient.lean, lines {fact['declStart']['line']}–{fact['declEnd']['line']}, SHA256 {EXPECTED}."
    p["proof_size_note"] = "Full actual mathematical helper core preserved; only two real definition spans removed and this target's recorded binding/reference spans renamed."
    problems.append(p)
    provenance["targets"][full] = {
        "stage2_declaration_fact": fact, "stage2_target_reference_facts": target_refs,
        "name_rename": {full: NAMESPACE + "." + checked},
        "deleted_definition_spans": deletion_edits,
        "solution_sha256": sha(solution.encode("utf-8")),
        "reference_sha256": sha(reference.encode("utf-8")),
        "formal_statement_sha256": sha(formal.encode("utf-8")),
        "extra_top_level_solution_binders": [],
    }
    provenance["targets"][full]["deleted_definition_spans"] = [[a,b] for a,b,_ in deletion_edits]

write(OUT / "definitions-request.json", json.dumps([definition], ensure_ascii=False, indent=2) + "\n")
write(OUT / "problems-request.json", json.dumps({"env": candidate["env"], "private": False, "problems": problems}, ensure_ascii=False, indent=2) + "\n")
provenance["shared_definition_sha256"] = sha(definition_code.encode("utf-8"))
write(OUT / "integration-provenance.json", json.dumps(provenance, ensure_ascii=False, indent=2) + "\n")

# Exact original and staged elaborated-type reports: separate environments
# prevent collisions among original target, registered stub, and solution.
labels = [NAMESPACE + ".weightedCoeff", NAMESPACE + ".A"] + [p["theorem_name"] for p in problems]
def type_report(imports, names, outname):
    entries = "\n".join('  emit "' + label + '" `' + name for label, name in names)
    return "\n".join("import " + imp for imp in imports) + '''
open Lean
set_option pp.fullNames true
set_option pp.universes false
run_meta do
  let emit (label : String) (name : Name) : Lean.Meta.MetaM Unit := do
    let ci ← getConstInfo name
    let type ← Lean.Meta.ppExpr ci.type
    let value ← match ci with
      | .defnInfo info => pure (some (← Lean.Meta.ppExpr info.value).pretty)
      | _ => pure none
    IO.println (Json.mkObj [("label", Json.str label), ("declaration", Json.str name.toString),
      ("type", Json.str type.pretty), ("value", toJson value)]).compress
''' + entries + "\n"

write(OUT / "types_original.lean", type_report(["missions.zeta9.formalization.ShortZeroCoefficient"], [(x,x) for x in labels], "original"))
write(OUT / "types_definition.lean", type_report([definition["local_path"].removesuffix(".lean").replace("/", ".")], [(x,x) for x in labels[:2]], "definition"))
for index, p in enumerate(problems):
    for kind, name, field in [("reference", p["theorem_name"], "local_reference"), ("solution", "solution", "local_solution")]:
        module = p[field].removesuffix(".lean").replace("/", ".")
        write(OUT / f"types_{index}_{kind}.lean", type_report([module], [(p["theorem_name"], name)], f"{index}_{kind}"))

print(json.dumps({"definition": definition["local_path"], "solutions": [p["local_solution"] for p in problems],
                  "references": [p["local_reference"] for p in problems], "stage2_span_generation": True,
                  "source_sha256": EXPECTED}, ensure_ascii=True))
