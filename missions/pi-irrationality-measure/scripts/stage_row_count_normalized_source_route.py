"""Pure source-only AP21 route for MatrixCounting.tendsto_rowCount_normalized.

This script extracts source commands and records the exact dependency frontier.  It
does not run Lean, construct a compiler manifest, or call the Prove2Me API.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


TASK = Path(__file__).resolve().parents[1]
SELF = Path(__file__).resolve()
V = TASK / "verification"
STAGE = V / "ap21/row-count-normalized-source-route"
AST = V / "ast-unit-inventory.json"
SCOPES = V / "ast-scope-inventory.json"
GRAPH = V / "decl_graph.jsonl"
OWNERS = V / "shared-source-snapshot/complete-source/CompleteSource875.owners.json"
COMMIT = "adc7f1241b42e322a6451854ab7e4b4c146bf78a"
TARGET = "OAI.PiExponent.MatrixCounting.tendsto_rowCount_normalized"
FUTURE_DATA_MODULE = (
    "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_"
    "MatrixCounting_RowCountData"
)

MISSING_DEFS = [
    "OAI.PiExponent.MatrixCounting.rationalLogWeights",
    "OAI.PiExponent.MatrixCounting.rowCount",
    "OAI.PiExponent.natWeightedSimplex",
    "OAI.PiExponent.residueRectangle",
]

PUBLISHED_BOUNDARY = {
    "OAI.PiExponent.tendsto_natFloor_affine_atTop",
    "OAI.PiExponent.tendsto_natFloor_affine_div",
    "OAI.PiExponent.tendsto_normalized_natFloor_affine",
    "OAI.PiExponent.unweightedSimplex",
    "OAI.PiExponent.mem_unweightedSimplex",
    "OAI.PiExponent.card_unweightedSimplex",
    "OAI.PiExponent.tendsto_choose_normalized",
    "OAI.PiExponent.tendsto_choose_add_normalized",
    "OAI.PiExponent.tendsto_card_unweightedSimplex",
    "OAI.PiExponent.tendsto_card_unweightedSimplex_add",
    "OAI.PiExponent.realWeightedSimplex",
    "OAI.PiExponent.strictWeightedSimplex",
    "OAI.PiExponent.InterpolationMatrix.rowWeights",
    "OAI.PiExponent.InterpolationMatrix.Row",
    "OAI.PiExponent.MatrixArithmetic.logWeights",
}

PUBLICATIONS = [
    (
        "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexFloor",
        V / "providers-complete-preview/all-shared-safe-leaves/validation/"
        "Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexFloor/publication.json",
        sorted(n for n in PUBLISHED_BOUNDARY if "natFloor" in n),
    ),
    (
        "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexUnweighted",
        V / "providers-complete-preview/all-shared-safe-leaves/validation/"
        "Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexUnweighted/publication.json",
        sorted(n for n in PUBLISHED_BOUNDARY if "unweightedSimplex" in n or "choose" in n),
    ),
    (
        "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexCounting_WeightedDomains",
        V / "ap9/simplex/publication/publication.json",
        ["OAI.PiExponent.realWeightedSimplex", "OAI.PiExponent.strictWeightedSimplex"],
    ),
    (
        "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_Domains",
        V / "ap9/domains/publication/publication.json",
        ["OAI.PiExponent.InterpolationMatrix.rowWeights", "OAI.PiExponent.InterpolationMatrix.Row"],
    ),
    (
        "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_MatrixArithmetic_CoreData",
        V / "ap10/arithmetic/publication/publication.json",
        ["OAI.PiExponent.MatrixArithmetic.logWeights"],
    ),
]


def need(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def sha_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha(path: Path) -> str:
    return sha_bytes(path.read_bytes())


def read(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def encode(value) -> bytes:
    return (json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + "\n").encode()


def rel(path: Path) -> str:
    return path.resolve().relative_to(TASK.resolve()).as_posix()


def source_path(module: str, tree: str = "port") -> Path:
    return TASK / tree / "lean" / (module.replace(".", "/") + ".lean")


def published_evidence() -> tuple[list[dict], dict[str, str]]:
    rows, pins = [], {}
    covered: set[str] = set()
    for module, path, names in PUBLICATIONS:
        doc = read(path)
        body = doc["target_readback"]["body"]
        verdict = doc["last_publish_verdict"]["body"]
        wire = doc["publish_intent"]["payload"]["definition"]
        need(
            body["status"] == "Definition"
            and verdict["status"] == "PUBLISHED"
            and body["theorem_id"] == doc["definition_id"]
            and body["definition"] == wire,
            "Published Definition identity or exact readback differs: " + module,
        )
        for name in names:
            short = name.rsplit(".", 1)[1]
            need(short in wire, "Published Definition wire lacks boundary: " + name)
        covered.update(names)
        pins[rel(path)] = sha(path)
        rows.append(
            {
                "platform_module": module,
                "definition_id": doc["definition_id"],
                "publication_record": rel(path),
                "publication_record_sha256": sha(path),
                "exact_public_wire_sha256": sha_bytes(wire.encode()),
                "provided_boundary_names": names,
                "status": "PUBLISHED",
            }
        )
    need(covered == PUBLISHED_BOUNDARY, "Published boundary partition differs")
    return rows, pins


def graph_closure(graph: dict[str, dict]) -> set[str]:
    reached: set[str] = set()
    pending = [TARGET]
    while pending:
        name = pending.pop()
        if name in reached:
            continue
        need(name in graph, "Unknown project declaration in rowCount closure: " + name)
        reached.add(name)
        pending.extend(graph[name]["typeDeps"])
        pending.extend(graph[name]["valueDeps"])
    return reached


def authority():
    ast, scopes = read(AST), read(SCOPES)
    graph = {row["name"]: row for row in map(json.loads, GRAPH.read_text(encoding="utf-8").splitlines())}
    owners = {row["source_name"]: row for row in read(OWNERS)["owners"]}
    closure = graph_closure(graph)
    closure_theorems = {n for n in closure if graph[n]["kind"] == "theorem"}
    closure_defs = {n for n in closure if graph[n]["kind"] == "def"}
    missing = closure - PUBLISHED_BOUNDARY
    missing_defs = {n for n in missing if graph[n]["kind"] == "def"}
    missing_theorems = {n for n in missing if graph[n]["kind"] == "theorem"}
    need(len(closure) == 39 and len(closure_theorems) == 29 and len(closure_defs) == 10
         and len(PUBLISHED_BOUNDARY) == 15,
         "Expected 29-theorem/10-definition closure with 15 published boundaries")
    need(missing_defs == set(MISSING_DEFS), "Exact four missing source definitions differ")
    need(len(missing_theorems) == 20 and TARGET in missing_theorems,
         "Expected exact twenty-theorem unpublished source closure")

    module_by_name: dict[str, dict] = {}
    for module in ast["modules"]:
        for unit in module["units"]:
            for name in unit["graph_names"]:
                if name in missing:
                    module_by_name[name] = {"module": module, "unit": unit}
    need(set(module_by_name) == missing, "AST inventory does not cover exact remaining frontier")

    rows = {}
    pins = {rel(p): sha(p) for p in (SELF, AST, SCOPES, GRAPH, OWNERS)}
    for name in sorted(missing):
        module = module_by_name[name]["module"]
        unit = module_by_name[name]["unit"]
        module_name = module["module"]
        source = source_path(module_name)
        original = source_path(module_name, "source")
        raw = source.read_bytes()
        a, b = unit["start"]["offset"], unit["end"]["offset"]
        command = raw[a:b]
        scope_module = next(
            m for m in scopes["modules"] if m["source"] == module_name.replace(".", "/") + ".lean"
        )
        scope = next(s for s in scope_module["declarations"] if s["verified_name"] == name)
        contexts = [
            raw[c["range"]["start"]["offset"]:c["range"]["end"]["offset"]].decode()
            for c in scope["context_commands"]
        ]
        owner = owners[name]
        normalized_command = command.replace(b"\r\n", b"\n")
        need(
            unit["graph_names"] == [name]
            and unit["graph_kinds"] == [graph[name]["kind"]]
            and unit["privateTok"] is None
            and not unit["is_instance_command"]
            and not unit["is_local_instance"]
            and module["source_sha256"] == scope_module["source_sha256"] == sha(source)
            and owner["source_sha256"] == sha(source)
            and original.read_bytes().replace(b"\r\n", b"\n").count(normalized_command) == 1,
            "Original AST/scope/owner/source command differs: " + name,
        )
        proof_suffix_sha = None
        if graph[name]["kind"] == "theorem":
            value = unit["valueStart"]["offset"] - a
            need(command[value:value + 5] == b":= by", "Unexpected theorem proof delimiter: " + name)
            proof_suffix_sha = sha_bytes(command[value:])
        rows[name] = {
            "name": name,
            "kind": graph[name]["kind"],
            "module": module_name,
            "source": rel(source),
            "source_sha256": sha(source),
            "original_source": rel(original),
            "original_source_sha256": sha(original),
            "start": a,
            "end": b,
            "source_lines": [unit["start"]["line"], unit["end"]["line"]],
            "command_sha256": sha_bytes(command),
            "proof_suffix_sha256": proof_suffix_sha,
            "source_original_command_equal_modulo_line_endings": True,
            "namespace": scope["namespace"],
            "contexts": contexts,
            "scope_stack": scope["scope_stack"],
            "direct_type_dependencies": graph[name]["typeDeps"],
            "direct_value_dependencies": graph[name]["valueDeps"],
            "ast": unit,
            "owner": owner,
            "bytes": command,
        }
        pins[rel(source)] = sha(source)
        pins[rel(original)] = sha(original)
    return graph, closure, rows, pins


def theorem_order(graph: dict[str, dict], theorem_names: set[str]) -> list[str]:
    result: list[str] = []
    active: set[str] = set()
    done: set[str] = set()

    def visit(name: str) -> None:
        if name in done or name not in theorem_names:
            return
        need(name not in active, "Cycle in twenty-theorem source closure: " + name)
        active.add(name)
        for dep in graph[name]["typeDeps"] + graph[name]["valueDeps"]:
            visit(dep)
        active.remove(name)
        done.add(name)
        result.append(name)

    visit(TARGET)
    need(set(result) == theorem_names and result[-1] == TARGET,
         "Target traversal does not cover exact twenty original theorems")
    return result


def private_theorem(command: bytes) -> bytes:
    marker = b"theorem "
    pos = command.find(marker)
    need(pos >= 0 and b"private theorem " not in command, "Unexpected theorem command form")
    return command[:pos] + b"private " + command[pos:]


def scoped_command(row: dict, command: bytes) -> bytes:
    namespace = row["namespace"]
    need(namespace.startswith("OAI.PiExponent"), "Unexpected rowCount route namespace")
    context = "\n".join(row["contexts"])
    prefix = ("namespace " + namespace + "\n\n" + (context + "\n\n" if context else "")).encode()
    return prefix + command.rstrip(b"\r\n") + ("\n\nend " + namespace + "\n\n").encode()


def candidate_files(rows: dict[str, dict], order: list[str]) -> tuple[bytes, bytes, dict]:
    imports = [module for module, _, _ in PUBLICATIONS]
    import_block = ("".join("import " + module + "\n" for module in imports) + "\n").encode()

    def_names = [
        "OAI.PiExponent.natWeightedSimplex",
        "OAI.PiExponent.residueRectangle",
        "OAI.PiExponent.MatrixCounting.rowCount",
        "OAI.PiExponent.MatrixCounting.rationalLogWeights",
    ]
    data = import_block
    for name in def_names:
        data += scoped_command(rows[name], rows[name]["bytes"])

    solution = ("import " + FUTURE_DATA_MODULE + "\n").encode() + import_block
    for name in order[:-1]:
        solution += scoped_command(rows[name], private_theorem(rows[name]["bytes"]))
    target = rows[TARGET]
    command = target["bytes"]
    a = target["ast"]["nameRange"]["start"]["offset"] - target["start"]
    b = target["ast"]["nameRange"]["end"]["offset"] - target["start"]
    need(command[a:b] == b"tendsto_rowCount_normalized", "Original target name range differs")
    renamed = command[:a] + b"solution" + command[b:]
    value = target["ast"]["valueStart"]["offset"] - target["start"]
    renamed_value = value - (b - a) + len(b"solution")
    need(renamed[renamed_value:] == command[value:], "Global solution proof suffix changed")
    solution += (
        b"open OAI.PiExponent OAI.PiExponent.MatrixCounting\n"
        b"open Filter Topology\nopen scoped BigOperators\n\n" + renamed.rstrip(b"\r\n") + b"\n"
    )
    facts = {
        "future_data_module_name_is_provisional": True,
        "definition_commands_literal_original": True,
        "helper_proof_commands_literal_original_after_private_prefix": True,
        "target_only_name_changed_to_global_solution": True,
        "target_original_proof_suffix_sha256": target["proof_suffix_sha256"],
        "global_solution_proof_suffix_sha256": sha_bytes(renamed[renamed_value:]),
    }
    return data, solution, facts


def outputs() -> dict[str, bytes]:
    graph, closure, rows, pins = authority()
    publications, publication_pins = published_evidence()
    pins.update(publication_pins)
    theorem_names = {n for n in closure - PUBLISHED_BOUNDARY if graph[n]["kind"] == "theorem"}
    order = theorem_order(graph, theorem_names)
    data_candidate, solution_candidate, candidate_facts = candidate_files(rows, order)
    def_rows = [rows[name] for name in MISSING_DEFS]
    theorem_rows = [rows[name] for name in order]
    source_modules = sorted({row["module"] for row in rows.values()})
    source_line_count = sum(
        row["source_lines"][1] - row["source_lines"][0] + 1 for row in theorem_rows
    )
    route = {
        "schema_version": 1,
        "artifact_kind": "ap21-row-count-normalized-source-only-route",
        "source_commit": COMMIT,
        "target": TARGET,
        "source_modules": source_modules,
        "full_project_closure_count": len(closure),
        "full_project_theorem_count": sum(graph[n]["kind"] == "theorem" for n in closure),
        "full_project_definition_count": sum(graph[n]["kind"] == "def" for n in closure),
        "full_project_closure_names": sorted(closure),
        "published_boundary_count": len(PUBLISHED_BOUNDARY),
        "published_boundary_names": sorted(PUBLISHED_BOUNDARY),
        "published_boundary_records": publications,
        "remaining_original_theorem_AST_count": len(theorem_rows),
        "remaining_original_theorem_source_line_count": source_line_count,
        "remaining_original_theorem_order": order,
        "remaining_original_theorems": [
            {k: v for k, v in row.items() if k != "bytes"} for row in theorem_rows
        ],
        "missing_original_Def_AST_count": len(def_rows),
        "missing_original_Def_names": MISSING_DEFS,
        "missing_original_Definitions": [
            {k: v for k, v in row.items() if k != "bytes"} for row in def_rows
        ],
        "candidate_data_module": FUTURE_DATA_MODULE,
        "candidate_data_sha256": sha_bytes(data_candidate),
        "candidate_solution_sha256": sha_bytes(solution_candidate),
        "candidate_facts": candidate_facts,
        "candidate_statement_is_not_a_published_wire": True,
        "four_Def_package_is_not_published": True,
        "closed_ready": False,
        "pending_gates": [
            "Publish and exactly read back a genuine full-type/full-value/Std3 provider for the four original definitions",
            "Compile the twenty-theorem source-faithful candidate in bounded contexts after that provider exists",
            "Certify full source/generated theorem types, actual proof references, owned CI inventory, and Std3",
            "Perform a fresh exact-name platform lookup before any theorem publication",
        ],
        "compiled": False,
        "Lean_started": False,
        "API_used": False,
        "validated": False,
        "submission_ready": False,
        "proposal_status": "Draft",
        "input_hashes": pins,
    }
    result = {
        "4Def-candidate.lean.txt": data_candidate,
        "Sol-candidate.lean.txt": solution_candidate,
    }
    route["files"] = {name: sha_bytes(raw) for name, raw in result.items()}
    result["route-preparation.json"] = encode(route)
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--prepare", action="store_true")
    modes.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    expected = outputs()
    for name, raw in expected.items():
        path = STAGE / name
        if path.exists():
            need(path.read_bytes() == raw, "Refusing changed source-only route output: " + name)
        elif args.prepare:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(raw)
        else:
            need(False, "Missing source-only route output: " + name)
    report = read(STAGE / "route-preparation.json") if STAGE.exists() else json.loads(expected["route-preparation.json"])
    print(json.dumps({
        "checked_files": len(expected),
        "theorem_AST_count": report["remaining_original_theorem_AST_count"],
        "missing_Def_AST_count": report["missing_original_Def_AST_count"],
        "published_boundary_count": report["published_boundary_count"],
        "closed_ready": False,
        "Lean_started": False,
        "API_used": False,
    }, indent=2))


if __name__ == "__main__":
    main()
