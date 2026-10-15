"""Prepare only the literal original-name collision-remainder child mirror.

This does not create compiler manifests or claim that the server proof is Accepted.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path


TASK = Path(__file__).resolve().parents[1]
STAGE = TASK / "verification/ap20/collision-remainder-child-mirror-pending"
ROUTE = TASK / "verification/ap19/collision-remainder-limit-route"
NODE = TASK / "verification/ap20/collision-remainder-limit-v2"
SOURCE_PROOFS = (
    TASK / "port/lean/OAI/NumberTheory/PiExponent/Polynomials/SimplexLog.lean",
    TASK / "port/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean",
)
ORIGINAL_PROOFS = (
    TASK / "source/lean/OAI/NumberTheory/PiExponent/Polynomials/SimplexLog.lean",
    TASK / "source/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean",
)
MODULE = "Theorems.Thm_OAI_PiExponent_tendsto_collisionRemainder_of_normalized_pow"
TARGET = "OAI.PiExponent.tendsto_collisionRemainder_of_normalized_pow"
HELPER = "OAI.PiExponent.tendsto_log_add_div_of_normalized_pow"
OUTPUT = STAGE / (MODULE.replace(".", "/") + ".lean")


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha(path: Path) -> str:
    return digest(path.read_bytes())


def require(cond: bool, message: str) -> None:
    if not cond:
        raise ValueError(message)


def source_commands() -> tuple[list[bytes], dict]:
    route = json.loads((ROUTE / "route-preparation.json").read_text(encoding="utf-8"))
    require(route["source_commit"] == "adc7f1241b42e322a6451854ab7e4b4c146bf78a"
            and route["target"] == TARGET and route["source_line_count"] == 15
            and route["literal_original_proof_suffixes"] is True,
            "Original source-only route changed")
    specs = [(HELPER, 1069, 1461), (TARGET, 2609, 3065)]
    commands = []
    for spec, port, original in zip(specs, SOURCE_PROOFS, ORIGINAL_PROOFS):
        name, start, end = spec
        row = next(x for x in route["exact_source_units"] if x["name"] == name)
        command = port.read_bytes()[start:end]
        require((row["start"], row["end"], row["command_sha256"]) ==
                (start, end, digest(command)) and
                sha(port) == row["source_sha256"] and
                sha(original) == row["original_sha256"] and
                original.read_bytes().replace(b"\r\n", b"\n").count(command.replace(b"\r\n", b"\n")) == 1 and
                command.count(b":= by") == 1 and b"sorry" not in command,
                "Original command, source hash, or proof bytes changed: " + name)
        commands.append(command)
    return commands, route


def candidate() -> tuple[bytes, dict]:
    (helper, target), route = source_commands()
    sol = (NODE / "Solutions/Sol_collision_remainder_limit_ap20.lean").read_bytes()
    imports = [line for line in sol.splitlines(keepends=True) if line.startswith(b"import ")]
    require(len(imports) == 6 and
            imports[-1] == b"import Theorems.Thm_OAI_PiExponent_tendsto_log_div_of_normalized_pow\n" and
            not any(b"Sol_" in line for line in imports),
            "Accepted LogDiv / Mathlib import profile changed")
    require(helper.startswith(b"theorem tendsto_log_add_div_of_normalized_pow") and
            target.startswith(b"theorem tendsto_collisionRemainder_of_normalized_pow"),
            "Original theorem-name tokens changed")
    # Retain the two actual source contexts as separate reopened namespaces.
    body = b"".join(imports) + b"\nnamespace OAI\n\nopen Filter Topology\nopen scoped BigOperators\n\nnamespace PiExponent\n\n"
    body += b"private " + helper + b"\n\nend PiExponent\n\nend OAI\n\n"
    body += b"namespace OAI\n\nopen scoped BigOperators Topology\nopen Filter\n\nnamespace PiExponent\n\n"
    body += target + b"\n\nend PiExponent\n\nend OAI\n"
    require(b"sorry" not in body and body.count(b"private theorem ") == 1 and
            body.count(b"theorem tendsto_collisionRemainder_of_normalized_pow") == 1,
            "Candidate has wrong theorem visibility or a placeholder")
    require(body[body.index(b"private theorem ") + len(b"private "):].startswith(helper),
            "Private helper was otherwise altered")
    return body, route


def main() -> None:
    body, route = candidate()
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_bytes(body)
    publication = NODE / "publication-v3/publication.json"
    pub = json.loads(publication.read_text(encoding="utf-8"))
    # Platform status is saved as observed state, never promoted to an Accepted pin.
    observed = pub.get("last_verify_verdict", {}).get("body", {}).get("status")
    pins = [Path(__file__), ROUTE / "route-preparation.json", *SOURCE_PROOFS,
            *ORIGINAL_PROOFS, NODE / "Solutions/Sol_collision_remainder_limit_ap20.lean",
            NODE / "source-types.json", NODE / "source-proof-references.json",
            NODE / "node-validation-v3.json", publication]
    report = {
        "schema_version": 1,
        "artifact_kind": "ap20-collision-remainder-original-name-child-mirror-candidate",
        "source_commit": route["source_commit"],
        "module": MODULE,
        "target": TARGET,
        "private_helper": HELPER,
        "original_command_sha256": [r["command_sha256"] for r in route["exact_source_units"]],
        "original_proof_suffix_sha256": [r["proof_suffix_sha256"] for r in route["exact_source_units"]],
        "candidate_sha256": digest(body),
        "sole_source_change": "private visibility prefix on the first original theorem command",
        "source_contexts": ["OAI/PiExponent; open Filter Topology; open scoped BigOperators",
                            "OAI/PiExponent; open scoped BigOperators Topology; open Filter"],
        "public_platform_boundary_names": [TARGET],
        "observed_platform_theorem_id": pub.get("theorem_id"),
        "observed_platform_proof_id": pub.get("submission_id"),
        "observed_platform_proof_status": observed,
        "accepted_binding_pending": observed != "ACCEPTED",
        "compiler_manifests_emitted": False,
        "Lean_started_by_this_script": False,
        "API_used": False,
        "input_hashes": {str(p.relative_to(TASK)).replace("\\", "/"): sha(p) for p in pins},
    }
    (STAGE / "candidate-preparation.json").write_text(
        json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"candidate": str(OUTPUT.relative_to(TASK)).replace("\\", "/"),
                      "sha256": report["candidate_sha256"],
                      "accepted_binding_pending": report["accepted_binding_pending"]}))


if __name__ == "__main__":
    main()
