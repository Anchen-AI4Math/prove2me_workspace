"""Offline author-side C3 integration gates; no uploads or credential access.

Mathematical source transformations are reconstructed solely from the actual
Lean graph/sketch facts and the parser's persisted input. This is an author
audit, not the independent integration reviewer report.
"""
from pathlib import Path
import hashlib
import json
from datetime import datetime, timezone

OUT = Path(__file__).resolve().parent
TASK = OUT.parents[2]
ROOT = TASK.parents[1]
NS = "ZetaNine.ShortZeroCoefficient"
SOURCE = TASK / "formalization/ShortZeroCoefficient.lean"
SOURCE_SHA = "9bf18387c4a51dd6dca03ecf197fc1cd85337fabf5b1d3421e2302e452347dbc"
ZIP_SHA = "50e1058a1c44f65271837a1943bc0a0a7c80385c941413d284e7dcb70ad82405"

def digest(data):
    return hashlib.sha256(data).hexdigest()

def load(path):
    return json.loads(path.read_text(encoding="utf-8-sig"))

def jsonl(path):
    return [json.loads(line) for line in path.read_text(encoding="utf-8-sig").splitlines()
            if line.startswith("{")]

checks = []

def check(label, predicate, detail=None):
    checks.append({"check": label, "pass": bool(predicate), "detail": detail})

def apply(data, edits):
    boundary = len(data)
    for start, end, replacement in sorted(set(edits), reverse=True):
        assert 0 <= start <= end <= boundary
        data = data[:start] + replacement + data[end:]
        boundary = start
    return data

source_disk = SOURCE.read_bytes()
source = (OUT / "oracle-input.lean").read_bytes()
graph = jsonl(OUT / "decl_graph.jsonl")
facts = jsonl(OUT / "sketch_info.jsonl")
decls = [row for row in facts if row["kind"] == "decl"]
refs = [row for row in facts if row["kind"] == "ref"]
provenance = load(OUT / "integration-provenance.json")
definitions = load(OUT / "definitions-request.json")
request = load(OUT / "problems-request.json")
problems = request["problems"]
check("original source immutable", digest(source_disk) == SOURCE_SHA)
check("exact parser normalization only", source == source_disk.replace(b"\r\n", b"\n"),
      {"disk_bytes": len(source_disk), "parser_bytes": len(source), "CRLF_pairs": source_disk.count(b"\r\n")})
check("actual oracle extraction passed", all(int((OUT / f"{x}-exit.txt").read_text()) == 0 for x in ["graph", "sketch"]))
check("actual oracle counts", len(graph) == 145 and len(decls) == 104 and len(refs) == 578)
check("two public targets and one definition bundle", len(problems) == 2 and len(definitions) == 1)
check("pinned environment", request["env"] == "0df444a360eaa60ab8c11dca51a86af692955474")
check("explicit staged build passed", int((OUT / "staged-build-exit.txt").read_text()) == 0)

def decl_for(name):
    row = next(row for row in graph if row["userName"] == name and row["startLine"] > 0)
    matches = [fact for fact in decls if fact["declStart"]["line"] <= row["startLine"] <= fact["declEnd"]["line"]]
    assert len(matches) == 1
    return matches[0]

definition_facts = [decl_for(NS + "." + name) for name in ["weightedCoeff", "A"]]
deletions = [(fact["declStart"]["offset"], fact["declEnd"]["offset"], b"") for fact in definition_facts]
definition_payload = definitions[0]["definition"].encode("utf-8")
check("definition payload is exact shared bytes", definition_payload == (ROOT / definitions[0]["local_path"]).read_bytes())
check("definition contains exactly two actual declarations",
      definition_payload == ("import Mathlib.Data.Nat.Choose.Basic\n"
       "import Mathlib.Algebra.BigOperators.Group.Finset.Basic\n"
       "import Mathlib.Data.Finset.Range\nimport Mathlib.Data.Int.Basic\n\n"
       "set_option autoImplicit false\nopen scoped BigOperators\n\nnamespace " + NS + "\n\n").encode()
      + b"\n\n".join(source[a:b] for a,b,_ in deletions)
      + ("\n\nend " + NS + "\n").encode())

original = {row["label"]: row for row in jsonl(OUT / "types-original.jsonl")}
definition_types = {row["label"]: row for row in jsonl(OUT / "types-definition.jsonl")}
type_comparisons = []
for tag in ["original", "definition", "0_reference", "0_solution", "1_reference", "1_solution"]:
    check("type-report compiled " + tag, int((OUT / f"types-{tag}-exit.txt").read_text()) == 0)
for name in [NS + ".weightedCoeff", NS + ".A"]:
    row = {"declaration": name,
           "type_equal": original[name]["type"] == definition_types[name]["type"],
           "value_equal": original[name]["value"] == definition_types[name]["value"]}
    type_comparisons.append(row)
    check("definition type and value preserved " + name, row["type_equal"] and row["value_equal"])

build_log = (OUT / "staged-build.log").read_text(encoding="utf-8-sig")
axiom_reports = {}
for index, problem in enumerate(problems):
    name = problem["theorem_name"]
    short = name.rsplit(".", 1)[1]
    fact = decl_for(name)
    start, end, val = [fact[k]["offset"] for k in ["declStart", "declEnd", "valStart"]]
    target_refs = [ref for ref in refs if ref["const"] == name]
    binding = [ref for ref in target_refs if start <= ref["start"]["offset"] < val]
    assert len(binding) == 1
    binding = binding[0]
    bs, be = binding["start"]["offset"], binding["end"]["offset"]
    assert source[bs:be].decode() == short
    edits = []
    for ref in target_refs:
        a, b = ref["start"]["offset"], ref["end"]["offset"]
        token = source[a:b].decode()
        assert token in [name, short]
        checked = "checked_" + short
        edits.append((a, b, (checked if token == short else NS + "." + checked).encode()))
    signature = source[be:val]
    args = {"A_even_signed_lower": "d m", "A_ne_zero_of_even": "n m hn"}[short]
    expected = b"import Definitions.Def_ZetaNine_ShortZeroCoefficient\n" + apply(source, deletions + edits)
    expected += ("\n\nopen " + NS + "\n\ntheorem solution").encode() + signature
    expected += (":= by\n  exact " + NS + ".checked_" + short + " " + args + "\n\n#print axioms solution\n").encode()
    solution = (ROOT / problem["local_solution"]).read_bytes()
    reference = (ROOT / problem["local_reference"]).read_bytes()
    check("entire helper proof core preserved " + short, solution == expected)
    check("reference bytes equal exact platform concatenation " + short,
          reference == (problem["preamble"] + "\nset_option autoImplicit false\n\n" + problem["formal_statement"] + "\n").encode())
    check("solution imports no reference stub " + short,
          not any(line.startswith(b"import Theorems.") for line in solution.splitlines()))
    graph_row = next(row for row in graph if row["userName"] == name)
    check("public type only needs actual A " + short, graph_row["typeDeps"] == [NS + ".A"])
    for kind in ["reference", "solution"]:
        rows = jsonl(OUT / f"types-{index}_{kind}.jsonl")
        check("one exact type emitted " + str(index) + " " + kind, len(rows) == 1)
        row = {"declaration": name, "stage": kind,
               "type_equal": original[name]["type"] == rows[0]["type"]}
        type_comparisons.append(row)
        check("original elaborated type equals " + kind + " " + short, row["type_equal"])
    relevant = [line for line in build_log.splitlines()
                if problem["local_solution"] + ":" in line and "'solution' depends on axioms:" in line]
    check("actual solution axiom report present " + short, len(relevant) == 1)
    if len(relevant) == 1:
        axioms = relevant[0].split("depends on axioms: [", 1)[1].split("]", 1)[0].split(", ")
        axiom_reports[name] = axioms
        check("only standard three actual solution axioms " + short,
              sorted(axioms) == sorted(["propext", "Classical.choice", "Quot.sound"]))

# Confirm the already reviewed batches and the existing attachment remain frozen.
frozen_checked = {}
first = load(TASK / "formalization/platform/independent-statement-review.json")["sha256"]
second = load(TASK / "formalization/platform/prime-valuation/independent-integration-review.json")["sha256"]
for batch, entries in [(1, first), (2, second)]:
    for name, expected in entries.items():
        if not (name.startswith(("Definitions/", "Theorems/", "Solutions/")) or
                name.endswith(("definitions-request.json", "problems-request.json", "integration-provenance.json"))):
            continue
        path = ROOT / name if name.startswith(("Definitions/", "Theorems/", "Solutions/", "missions/")) else TASK / name
        actual = digest(path.read_bytes())
        frozen_checked[str(path.relative_to(ROOT)).replace("\\", "/")] = actual
        check("frozen batch " + str(batch) + " unchanged " + name, actual == expected)
attachment = TASK / "publication/2026-10-02/formal-proofs/zeta9-formal-proofs-2026-10-02.zip"
check("frozen nine-proof attachment unchanged", digest(attachment.read_bytes()) == ZIP_SHA)

paths = [SOURCE, TASK / "research/short-zero-coefficient-nonvanishing.md",
         OUT / "definitions-request.json", OUT / "problems-request.json", OUT / "integration-provenance.json",
         OUT / "README.md", OUT / "audit_coefficient.py",
         OUT / "prepare_coefficient.py", OUT / "extract_decl_graph.lean", OUT / "extract_sketch_info.lean",
         OUT / "decl_graph.jsonl", OUT / "sketch_info.jsonl", OUT / "oracle-input.lean",
         OUT / "staged-build.log", OUT / "staged-build-exit.txt"]
paths += [ROOT / definitions[0]["local_path"]]
for p in problems:
    paths += [ROOT / p["local_solution"], ROOT / p["local_reference"]]
for tag in ["original", "definition", "0_reference", "0_solution", "1_reference", "1_solution"]:
    paths += [OUT / f"types_{tag}.lean", OUT / f"types-{tag}.jsonl", OUT / f"types-{tag}-exit.txt"]
hashes = {p.relative_to(ROOT).as_posix(): digest(p.read_bytes()) for p in paths}
audit = {
    "checked_at": datetime.now(timezone.utc).isoformat(),
    "status": "PASS" if all(c["pass"] for c in checks) else "FAIL",
    "role": "author integration audit; independent report must be supplied by a different reviewer",
    "checks": checks, "axioms": axiom_reports, "exact_type_comparisons": type_comparisons,
    "mathematical_scope": {
        "signed_bound": "For every d,m in Nat, 28*choose(2d,d)*choose(3d,d)*choose(d+m,m)^14 <= (-1)^(m+d)*A(2d,m).",
        "nonzero": "For every n,m in Nat with Even n, actual A(n,m) != 0; n=0 and all m included.",
        "paper_subset": "Every even n>=2 and m>=0, including 14m<=3n+1, is covered.",
        "linear_form_nonvanishing_or_irrationality_claimed": False,
        "note_dated_pre_formalization_status_preserved": True,
        "unproved_reference_stubs": "Two registered formal statements only; never imported by complete Solutions.",
        "platform_acceptance_claimed": False,
    },
    "auxiliary_api_repair": "Type collector run_meta uses MetaM, not TermElabM; failed first diagnostics preserved in type-report-initial. No mathematical proof edits.",
    "sha256": hashes, "frozen_previous_batch_sha256": frozen_checked,
    "frozen_attachment_sha256": ZIP_SHA,
}
(OUT / "integration-audit.json").write_text(json.dumps(audit, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
(OUT / "SHA256SUMS.txt").write_text("".join(f"{value}  {name}\n" for name,value in sorted(hashes.items())), encoding="utf-8")
print(json.dumps({"status": audit["status"], "checks": len(checks),
                  "failed": [c for c in checks if not c["pass"]]}, ensure_ascii=False))
raise SystemExit(0 if audit["status"] == "PASS" else 1)
