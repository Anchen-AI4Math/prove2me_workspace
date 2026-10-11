"""Make an isolated n2 retry preserving the failed n2 attempt byte-for-byte."""
from __future__ import annotations

import copy
import hashlib
import json
import shutil
from pathlib import Path

import generate_platform_provider_nodes as nodegen
import stage_successive_approximations_frontier as frontier

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
V = TASK / "verification"
OLD = V / "ap4/n2"
STAGE = V / "ap4/n2z"
MODULE = frontier.MODULE
ZERO_KEY = MODULE + ":3545"
ZERO_NAME = "OAI.PiExponent.normalizedLogWeights_zero"


def sha_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha(path: Path) -> str:
    return sha_bytes(path.read_bytes())


def write(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)


def ast_helper(generator, existing_requests):
    g = generator.g
    raw, facts, _, provenance = generator.load_module(MODULE)
    inventory = json.loads((V / "ast-unit-inventory.json").read_text(encoding="utf-8"))
    found = []
    def visit(value):
        if isinstance(value, dict):
            if value.get("nameText") == "normalizedLogWeights_zero":
                found.append(value)
            for child in value.values(): visit(child)
        elif isinstance(value, list):
            for child in value: visit(child)
    visit(inventory)
    if len(found) != 1:
        raise ValueError("Expected one frozen AST unit for normalizedLogWeights_zero")
    unit = found[0]
    if (unit["graph_kinds"] != ["theorem"] or unit["privateTok"] is not None
            or unit["graph_names"] != [ZERO_NAME]):
        raise ValueError("zero helper AST unit is not one public theorem command")
    start, end = unit["start"]["offset"], unit["end"]["offset"]
    command = raw[start:end]
    matches = [row for row in facts if row.get("kind") == "command"
               and row.get("syntax", {}).get("range", {}).get("start", {}).get("offset") == start]
    if len(matches) != 1:
        raise ValueError("zero helper AST command row is not unique")
    syntax = matches[0]
    if (syntax.get("isDeclaration") is not True
            or syntax["syntax"]["range"]["start"]["offset"] != start
            or syntax["syntax"]["range"]["end"]["offset"] != end):
        raise ValueError("zero helper source range and syntax AST differ")
    originals = (TASK / "source/lean/OAI/NumberTheory/PiExponent/Approximation/SuccessiveApproximations.lean").read_bytes()
    original_lines = originals.splitlines()
    original_command = b"\n".join(original_lines[unit["start"]["line"] - 1:unit["end"]["line"]])
    if original_command != command.replace(b"\r\n", b"\n").rstrip(b"\n"):
        raise ValueError("zero helper original and port command bytes differ")
    request = {"source_graph_name": ZERO_NAME, "source_module": MODULE,
               "source_unit": ZERO_KEY, "generated_name": g.mapped_name(ZERO_NAME),
               "source_command_range": {"start": unit["start"], "end": unit["end"]},
               "generated_companion": False}
    row = {
        "source_unit": ZERO_KEY, "source_graph_name": ZERO_NAME,
        "generated_name": request["generated_name"],
        "source_command_range": request["source_command_range"],
        "source_value_start": unit["valueStart"],
        "raw_command_utf8": command.decode("utf-8"),
        "raw_command_sha256": sha_bytes(command),
        "raw_proof_suffix_utf8": command[unit["valueStart"]["offset"] - start:].decode("utf-8"),
        "raw_proof_suffix_sha256": sha_bytes(command[unit["valueStart"]["offset"] - start:]),
        "source_ast_command": syntax,
        "ast_command_sha256": sha_bytes(json.dumps(syntax, sort_keys=True, ensure_ascii=False,
                                                      separators=(",", ":")).encode("utf-8")),
        "graph_kind": g.graph[ZERO_NAME]["kind"],
        "source_private": g.graph[ZERO_NAME]["isPrivate"],
        "source_instance": g.graph[ZERO_NAME]["isInstance"],
        "type_dependencies": g.graph[ZERO_NAME]["typeDeps"],
        "value_dependencies": g.graph[ZERO_NAME]["valueDeps"],
        "generated_companion": False, "no_companion_identity_inferred": True,
        "source_line_span": [unit["start"]["line"], unit["end"]["line"]],
        "source_port_path": provenance["source"], "source_port_sha256": provenance["source_sha256"],
        "source_original_path": provenance["original_source"],
        "source_original_sha256": provenance["original_source_sha256"],
        "source_original_command_normalized_to_port": True,
    }
    request["source_ast_command_sha256"] = row["ast_command_sha256"]
    request["raw_command_sha256"] = row["raw_command_sha256"]
    return request, row, command


def main():
    if STAGE.exists():
        raise ValueError("n2z already exists; never overwrite a staged attempt")
    generator, _, _ = frontier.promoted_generator()
    manifest = json.loads((OLD / "manifest.json").read_text(encoding="utf-8"))
    witness = json.loads((OLD / "inline-helper-ast-witness.json").read_text(encoding="utf-8"))
    request, row, command = ast_helper(generator, manifest["public_inline_ci_requests"])
    # Preserve the failed n2 attempt; copy only source/provenance inputs, not
    # failed compiler sidecars or mutable preparation records.
    STAGE.mkdir(parents=True)
    for name in ("Theorems", "Solutions"):
        shutil.copytree(OLD / name, STAGE / name)
    for name in ("manifest.json", "academic-metadata.json", "definition-input.json",
                 "inline-helper-ast-witness.json", "SnapshotOriginal.lean", "SnapshotGenerated.lean"):
        shutil.copy2(OLD / name, STAGE / name)
    helper = command.replace(b"\r\n", b"\n").rstrip(b"\n") + b"\n\n"
    marker = b"@[simp] theorem normalizedLogWeights_succ"
    for path in (STAGE / "Theorems/Thm_OAI_PiExponent_exists_normalized_selection_of_selector.lean",
                 STAGE / "Solutions/Sol_OAI_PiExponent_exists_normalized_selection_of_selector.lean",
                 STAGE / "SnapshotGenerated.lean"):
        content = path.read_bytes()
        if content.count(marker) != 1:
            raise ValueError("Expected one exact normalized-succ helper insertion point in " + str(path))
        write(path, content.replace(marker, helper + marker, 1))

    # Rebuild both public inline-helper source/generated type collectors from
    # the exact graph identity and module owner; never guess a companion.
    reqs = manifest["public_inline_ci_requests"] + [request]
    source_collect = nodegen.public_inline_snapshot_code(
        reqs, "missions/pi-irrationality-measure/verification/ap4/n2z/original-public-inline-types.json",
        generated=False)
    generated_collect = nodegen.public_inline_snapshot_code(
        reqs, "missions/pi-irrationality-measure/verification/ap4/n2z/generated-public-inline-types.json",
        generated=True)
    original_file = STAGE / "SnapshotOriginal.lean"
    original_file.write_bytes(original_file.read_bytes().replace(b"ap4/n2/", b"ap4/n2z/")
                              + source_collect.encode())
    generated_file = STAGE / "SnapshotGenerated.lean"
    generated_file.write_bytes(generated_file.read_bytes().replace(b"ap4/n2/", b"ap4/n2z/")
                               + generated_collect.encode())

    manifest["statement"] = manifest["statement"].replace("ap4/n2/", "ap4/n2z/")
    manifest["solution"] = manifest["solution"].replace("ap4/n2/", "ap4/n2z/")
    manifest["public_inline_ci_requests"] = reqs
    for key in ("inline_type_json_outputs", "public_inline_type_json_outputs"):
        for side in ("original", "generated"):
            manifest[key][side] = manifest[key][side].replace("ap4/n2/", "ap4/n2z/")
    manifest["snapshot_sha256"] = {name: sha(STAGE / name)
                                   for name in ("SnapshotOriginal.lean", "SnapshotGenerated.lean")}
    manifest["outputs_sha256"]["SnapshotOriginal.lean"] = manifest["snapshot_sha256"]["SnapshotOriginal.lean"]
    manifest["outputs_sha256"]["SnapshotGenerated.lean"] = manifest["snapshot_sha256"]["SnapshotGenerated.lean"]
    manifest["statement_sha256"] = sha(STAGE / "Theorems/Thm_OAI_PiExponent_exists_normalized_selection_of_selector.lean")
    manifest["solution_sha256"] = sha(STAGE / "Solutions/Sol_OAI_PiExponent_exists_normalized_selection_of_selector.lean")

    witness["helpers"].insert(0, row)
    witness["artifact_kind"] = "successive-approximations-n2z-inline-helper-ast-witness"
    witness["helpers"][0]["source_command_range"]["start"]["line"] = row["source_line_span"][0]
    witness["interpretation"] = ("The exact source `@[simp]` zero-case theorem is restored in the original elaboration context; "
                                 "all three public theorem helpers are certified by source/generated CI type snapshots.")
    witness_path = STAGE / "inline-helper-ast-witness.json"
    witness_path.write_text(json.dumps(witness, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    manifest["n2z_inline_helper_ast_witness_sha256"] = sha(witness_path)
    # Redirect all copied producer/input references to this fresh attempt.
    manifest["input_hashes"] = {
        k.replace("verification/ap4/n2/", "verification/ap4/n2z/"): v
        for k, v in manifest["input_hashes"].items()
        if not k.startswith("verification/ap4/n2/")
    }
    manifest["input_hashes"]["verification/ap4/n2/manifest.json"] = sha(OLD / "manifest.json")
    manifest["input_hashes"]["verification/ap4/n2/academic-metadata.json"] = sha(OLD / "academic-metadata.json")
    manifest["input_hashes"]["verification/ap4/n2/inline-helper-ast-witness.json"] = sha(OLD / "inline-helper-ast-witness.json")
    manifest["input_hashes"]["scripts/stage_successive_approximations_n2z.py"] = sha(Path(__file__))
    prep_script = TASK / "scripts/prepare_successive_approximations_n2z.py"
    if not prep_script.is_file():
        raise ValueError("n2z preparation script is required before final input hashes")
    manifest["input_hashes"]["scripts/prepare_successive_approximations_n2z.py"] = sha(prep_script)
    write(STAGE / "manifest.json", json.dumps(manifest, indent=2, ensure_ascii=False).encode())
    return {"stage": "verification/ap4/n2z", "added_source_ast_helper": ZERO_NAME,
            "helper_raw_sha256": row["raw_command_sha256"], "preserved_failed_n2": True,
            "Lean_started": False, "API_used": False}


if __name__ == "__main__":
    print(json.dumps(main(), indent=2, ensure_ascii=False))
