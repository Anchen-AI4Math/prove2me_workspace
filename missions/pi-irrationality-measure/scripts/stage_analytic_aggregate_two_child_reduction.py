"""Pure pending AP19 reduction of the original analytic aggregate to its two direct children.

This prepares exact source interfaces and an Open sketch. It does not finalize
compiler manifests, claim a closed proof, run Lean, or contact the platform.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import stage_source_root_graph as source_root


TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
V = TASK / "verification"
STAGE = V / "ap19/analytic-aggregate-two-child-reduction-v2"
SELF = Path(__file__).resolve()
SOURCE_MODULE = "OAI.NumberTheory.PiExponent.Analysis.AnalyticAggregate"
SOURCE_FILE = TASK / ("port/lean/" + SOURCE_MODULE.replace(".", "/") + ".lean")
ORIGINAL_FILE = TASK / ("source/lean/" + SOURCE_MODULE.replace(".", "/") + ".lean")
AST = V / "ast-unit-inventory.json"
SCOPES = V / "ast-scope-inventory.json"
GRAPH = V / "decl_graph.jsonl"
SNAPSHOT_CORE = V / "TypeOnlyTheoremSnapshotCore.inc"
PARENT_READBACK = V / "graph-source-root-20261011/publication-v2/parent-readbacks/analytic.json"
PARENT_PUBLICATION = V / "graph-source-root-20261011/publication-v2/publication.json"
PARENT_ORIGINAL_WIRE = V / "graph-source-root-20261011/parents/analytic/wire-theorem-source.lean"
PARENT_METADATA = V / "graph-source-root-20261011/parents/analytic/academic-metadata.json"
PROVIDER_MODULE = "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData"
PROVIDER_STAGE = V / "ap19/analytic-remainder-data"
PROVIDER_CERT = PROVIDER_STAGE / "actual-provider-validation.json"
PROVIDER_PUBLICATION = PROVIDER_STAGE / "publication/publication.json"
CORE_MODULE = "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData"
CANONICAL_MODULE = "Definitions.Def_OAI_PiExponent_ApproximationDefinitions"
PARENT = "OAI.PiExponent.LiteralAnalytic.analyticAggregate"
CHILDREN = [
    ("OAI.PiExponent.LiteralAnalytic.tendsto_analyticRemainder", 3610, 4682, 74, 94),
    ("OAI.PiExponent.LiteralAnalytic.actual_minor_analytic_bound", 2486, 3606, 53, 72),
]
PARENT_RANGE = (4686, 4986, 96, 101)
PARENT_ID = "c873700d-6b99-4966-899b-2afef157b779"
COMMIT = "adc7f1241b42e322a6451854ab7e4b4c146bf78a"
SOLUTION_MODULE = "Solutions.Sol_OAI_PiExponent_LiteralAnalytic_analyticAggregate_two_children_ap19"
SOLUTION_FILE = SOLUTION_MODULE.replace(".", "/") + ".lean"
SOURCE_SNAPSHOT = "SourceTypeAndRefsSnapshot.lean"
GENERATED_SNAPSHOT = "GeneratedTypeAndRefsSnapshot.lean"


def need(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def digest(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha(path: Path) -> str:
    return digest(path.read_bytes())


def read(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def encode(value) -> bytes:
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode("utf-8")


def rel(path: Path) -> str:
    return path.resolve().relative_to(TASK.resolve()).as_posix()


def workspace_rel(path: Path) -> str:
    return path.resolve().relative_to(ROOT.resolve()).as_posix()


def authority(name: str, start: int, end: int, first: int, last: int):
    raw = SOURCE_FILE.read_bytes()
    original = ORIGINAL_FILE.read_bytes()
    module = next(m for m in read(AST)["modules"] if m["module"] == SOURCE_MODULE)
    scope_module = next(m for m in read(SCOPES)["modules"]
                        if m["source"] == SOURCE_MODULE.replace(".", "/") + ".lean")
    unit = next(u for u in module["units"] if name in u["graph_names"])
    scope = next(s for s in scope_module["declarations"] if s["verified_name"] == name)
    graph = next(json.loads(line) for line in GRAPH.read_text(encoding="utf-8").splitlines()
                 if line and json.loads(line)["name"] == name)
    proof = raw[unit["valueStart"]["offset"]:end]
    contexts = [raw[c["range"]["start"]["offset"]:c["range"]["end"]["offset"]].decode("utf-8")
                for c in scope["context_commands"]]
    expected_contexts = ["open scoped BigOperators Topology", "open Filter", "open DeterminantContradiction"]
    need(module["source_sha256"] == scope_module["source_sha256"] == sha(SOURCE_FILE)
         and [unit["start"]["offset"], unit["end"]["offset"]] == [start, end]
         and [unit["start"]["line"], unit["end"]["line"]] == [first, last]
         and unit["graph_names"] == [name] and unit["graph_kinds"] == ["theorem"]
         and unit["privateTok"] is None and not unit["is_instance_command"]
         and not unit["is_local_instance"] and scope["namespace"] == name.rsplit(".", 1)[0]
         and contexts == expected_contexts and all(x["kind"] == "namespace" for x in scope["scope_stack"])
         and original.replace(b"\r\n", b"\n").count(raw[start:end].replace(b"\r\n", b"\n")) == 1
         and proof.startswith(b":= by") and raw[unit["nameRange"]["start"]["offset"]:
                                               unit["nameRange"]["end"]["offset"]]
         == name.rsplit(".", 1)[1].encode(), "Original analytic theorem AST/scope changed: " + name)
    return {"name": name, "source_module": SOURCE_MODULE, "source_path": rel(SOURCE_FILE),
            "source_sha256": sha(SOURCE_FILE), "original_path": rel(ORIGINAL_FILE),
            "original_sha256": sha(ORIGINAL_FILE), "start": start, "end": end,
            "source_lines": [first, last], "source_command_sha256": digest(raw[start:end]),
            "source_proof_sha256": digest(proof), "ast": unit, "scope": scope, "graph": graph,
            "command": raw[start:end], "proof": proof}


def child_comparator(row) -> bytes:
    unit = row["command"]
    unit_start = row["start"]
    a = row["ast"]["nameRange"]["start"]["offset"] - unit_start
    b = row["ast"]["nameRange"]["end"]["offset"] - unit_start
    v = row["ast"]["valueStart"]["offset"] - unit_start
    formal = unit[:a] + row["name"].encode() + unit[b:v] + b":= by\n  sorry\n"
    # Source scopes remain explicit. The extra open names only restore the
    # original nested-namespace lookup for this global, qualified declaration.
    preamble = ("import " + CANONICAL_MODULE + "\nimport " + CORE_MODULE +
                "\nimport " + PROVIDER_MODULE + "\n\n"
                "open scoped BigOperators Topology\nopen Filter\n"
                "open OAI.PiExponent OAI.PiExponent.DeterminantContradiction "
                "OAI.PiExponent.LiteralAnalytic\n\n").encode()
    need(formal.count(b"sorry") == 1 and formal.count(row["name"].encode()) == 1,
         "Child comparator must contain exactly the original qualified declaration and Open placeholder")
    return preamble + formal


def solution(parent) -> bytes:
    unit = parent["command"]
    a = parent["ast"]["nameRange"]["start"]["offset"] - parent["start"]
    b = parent["ast"]["nameRange"]["end"]["offset"] - parent["start"]
    renamed = unit[:a] + b"solution" + unit[b:]
    need(renamed.replace(b"solution", b"analyticAggregate", 1) == unit,
         "Parent theorem name is not the sole source-command modification")
    imports = [CANONICAL_MODULE, CORE_MODULE, PROVIDER_MODULE] + [theorem_module(n) for n, *_ in CHILDREN]
    preamble = ("".join("import " + m + "\n" for m in imports) +
                "\nopen scoped BigOperators Topology\nopen Filter\n"
                "open OAI.PiExponent OAI.PiExponent.DeterminantContradiction "
                "OAI.PiExponent.LiteralAnalytic\n\n").encode()
    need(renamed[renamed.index(b":= by"):] == parent["proof"],
         "Original six-line parent proof bytes changed")
    return preamble + renamed.rstrip(b"\r\n") + b"\n"


def theorem_module(name: str) -> str:
    return "Theorems.Thm_" + name.replace(".", "_")


def snapshot(source: bool) -> bytes:
    names = [n for n, *_ in CHILDREN] + ([PARENT] if source else ["solution"])
    owners = [SOURCE_MODULE] * 3 if source else [theorem_module(n) for n, *_ in CHILDREN] + [SOLUTION_MODULE]
    module = SOURCE_MODULE if source else SOLUTION_MODULE
    output = STAGE / ("source-types-and-refs.json" if source else "generated-types-and-refs.json")
    name_array = "#[" + ", ".join("`" + n for n in names) + "]"
    owner_array = "#[" + ", ".join(json.dumps(o) for o in owners) + "]"
    return ("import Lean\nimport " + module + "\n\n" +
            SNAPSHOT_CORE.read_text(encoding="utf-8").rstrip() + "\n" + source_root.PROBE +
            "\nrun_meta do\n  SourceRootGraphSnapshot.exportRows " + name_array + " " +
            owner_array + " " + json.dumps(workspace_rel(output)) + " " +
            ("false" if source else "true") + "\n" +
            "".join("#print axioms " + n + "\n" for n in names)).encode("utf-8")


def files():
    rows = [authority(*x) for x in CHILDREN]
    parent = authority(PARENT, *PARENT_RANGE)
    saved = read(PARENT_READBACK)
    publication = read(PARENT_PUBLICATION)
    old_wire = PARENT_ORIGINAL_WIRE.read_bytes()
    need(saved["theorem_id"] == PARENT_ID and saved["theorem_name"] == PARENT
         and saved["status"] == "Open" and saved["visibility"] == "public"
         and saved["mathlib_rev"] == "0df444a360eaa60ab8c11dca51a86af692955474"
         and publication["parent_ids"][PARENT] == PARENT_ID
         and old_wire == (saved["preamble"] + saved["formal_statement"]).encode(),
         "Existing public analyticAggregate parent wire/ID differs")
    need(saved["formal_statement"] == "theorem " + PARENT + " : AnalyticAggregateStatement := by\n  sorry\n",
         "Existing parent comparator type differs")
    output = {"parent-existing-wire.lean": old_wire,
              "parent-existing-academic-metadata.json": PARENT_METADATA.read_bytes(),
              SOLUTION_FILE: solution(parent),
              SOURCE_SNAPSHOT: snapshot(True), GENERATED_SNAPSHOT: snapshot(False)}
    for row in rows:
        name = row["name"]
        output[theorem_module(name).replace(".", "/") + ".lean"] = child_comparator(row)
        output["source-commands/" + name.rsplit(".", 1)[1] + ".lean.txt"] = row["command"]
        is_limit = name.endswith("tendsto_analyticRemainder")
        title = ("The original analytic remainder tends to zero" if is_limit else
                 "The original selected-minor analytic bound")
        statement = (r"For every real $\nu$ and original fixed admissible datum $d$, the exact source remainder $R_d(H)$ tends to zero as $H\to+\infty$: $\operatorname{Tendsto}(R_d,\operatorname{atTop},\mathcal N(0))$."
                     if is_limit else
                     r"For the original fixed datum $d$, $\nu\ge0$, height $H>0$, and a column selection with nonzero selected-minor determinant, the normalized logarithmic determinant is at most $d.analyticError+R_d(H)+\max\{-collisionRate_d(H),-\nu((d.A)(1-d.eta)-actualMean_d(H))\}$, with every term and binder exactly as in the source theorem.")
        output["children/" + name.rsplit(".", 1)[1] + "/academic-metadata.json"] = encode({
            "title": title, "statement": statement, "tags": ["number-theory", "openai-pi-exponent-017"],
            "source_commit": COMMIT,
            "source_url": "https://github.com/openai/math/blob/" + COMMIT +
                          "/lean/" + SOURCE_MODULE.replace(".", "/") +
                          ".lean#L" + str(row["source_lines"][0]) + "-L" + str(row["source_lines"][1])})
    output["source-commands/analyticAggregate.lean.txt"] = parent["command"]
    pins = {rel(p): sha(p) for p in [SELF, SOURCE_FILE, ORIGINAL_FILE, AST, SCOPES, GRAPH,
                                     SNAPSHOT_CORE, PARENT_READBACK, PARENT_PUBLICATION,
                                     PARENT_ORIGINAL_WIRE, PARENT_METADATA, Path(source_root.__file__)]}
    plan = {"schema_version": 1, "artifact_kind": "ap19-analyticAggregate-two-child-Open-sketch-candidate",
            "source_commit": COMMIT, "parent_existing_theorem_id": PARENT_ID,
            "parent_platform_name": PARENT, "parent_existing_wire": "parent-existing-wire.lean",
            "parent_existing_wire_sha256": digest(old_wire), "parent_wire_unchanged": True,
            "parent_existing_academic_metadata": "parent-existing-academic-metadata.json",
            "source_rows": [{k: v for k, v in r.items() if k not in ("command", "proof")} for r in rows + [parent]],
            "child_names": [n for n, *_ in CHILDREN],
            "child_module_imports": [theorem_module(n) for n, *_ in CHILDREN],
            "child_comparators_are_original_full_signatures": True,
            "child_sorry_placeholders": True, "child_closed_proofs": False,
            "provider_module": PROVIDER_MODULE, "provider_stage": rel(PROVIDER_STAGE),
            "provider_certificate_pending": rel(PROVIDER_CERT),
            "provider_publication_pending": rel(PROVIDER_PUBLICATION),
            "root_exact_child_name_lookups_pending": True,
            "solution_file": SOLUTION_FILE, "solution_global_name": "solution",
            "solution_original_proof_suffix_sha256": parent["source_proof_sha256"],
            "solution_proof_bytes_unchanged": True,
            "source_snapshot": SOURCE_SNAPSHOT, "generated_snapshot": GENERATED_SNAPSHOT,
            "snapshot_strategy": "Source imports the original AnalyticAggregate module and checks three genuine theorem CIs. Generated imports two Open child modules and the global solution; its three type-only theorem values are null, actual owners/closed values/proof refs are exported, and sorryAx is required for sketch dependencies. Compare source child full kernel types, level parameters and type refs with generated child CIs; compare source parent with global solution after name normalization; distinguish source Std3 closure from generated sorryAx. Final context records and certificates remain pending.",
            "planned_contexts": [
                {"key": "child-tendsto", "output": theorem_module(CHILDREN[0][0]).replace(".", "/") + ".lean", "mode": "emit-olean", "timeout_seconds": 300},
                {"key": "child-bound", "output": theorem_module(CHILDREN[1][0]).replace(".", "/") + ".lean", "mode": "emit-olean", "timeout_seconds": 300},
                {"key": "parent-solution-sketch", "output": SOLUTION_FILE, "mode": "emit-olean", "timeout_seconds": 300},
                {"key": "source-type-and-refs", "output": SOURCE_SNAPSHOT, "mode": "modecheck", "timeout_seconds": 300},
                {"key": "generated-type-and-refs", "output": GENERATED_SNAPSHOT, "mode": "modecheck", "timeout_seconds": 300}],
            "final_compiler_manifests_created": False, "validated": False,
            "submission_ready": False, "proposal_status": "Draft", "Lean_started": False, "API_used": False,
            "input_hashes": pins,
            "candidate_file_sha256": {path: digest(raw) for path, raw in output.items()}}
    output["pending-preparation.json"] = encode(plan)
    return output


def check_only():
    expected = files()
    for name, raw in expected.items():
        need((STAGE / name).read_bytes() == raw, "Immutable pending analytic reduction differs: " + name)
    return {"checked_files": len(expected), "Open_sketch_only": True,
            "closed_proof": False, "final_compiler_manifests_created": False,
            "validated": False, "Lean_started": False, "API_used": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    flags = parser.add_mutually_exclusive_group(required=True)
    flags.add_argument("--prepare", action="store_true")
    flags.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    if args.prepare:
        for name, raw in files().items():
            path = STAGE / name
            if path.exists():
                need(path.read_bytes() == raw, "Refusing overwrite of pending analytic reduction: " + name)
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(raw)
    print(json.dumps(check_only(), ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
