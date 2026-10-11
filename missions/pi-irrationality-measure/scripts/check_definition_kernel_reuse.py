"""Recheck six existing definitions against immutable source/kernel evidence."""
import hashlib
import json
from pathlib import Path

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
DEST = TASK / "verification"
TRUSTED = {"propext", "Classical.choice", "Quot.sound"}


def read(path):
    return json.loads(path.read_text(encoding="utf-8"))


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def preflight_valid(record):
    if (record["exit_code"] != 0 or record["timed_out"] or
            not record["source_unchanged"] or not 0 < record["timeout_seconds"] <= 300):
        raise ValueError("Interface evidence did not pass strict compilation")
    if digest(ROOT / record["source"]) != record["source_sha256"]:
        raise ValueError("The interface exporter or canonical definition source changed")
    if record.get("output_olean") and digest(ROOT / record["output_olean"]) != record["output_sha256"]:
        raise ValueError("The canonical definition's compiled artifact changed")


def main():
    candidate = read(TASK / "platform/definition-reuse-candidates.json")["reuse_candidates"][0]
    for path_field, hash_field in (("source", "source_sha256"), ("existing_source", "existing_sha256")):
        if digest(ROOT / candidate[path_field]) != candidate[hash_field]:
            raise ValueError("A reuse candidate's immutable input changed")
    validated = read(DEST / "validated-port-manifest.json")
    for relative, expected in validated["port_files_sha256"].items():
        if digest(TASK / "port/lean" / relative) != expected:
            raise ValueError(f"The imported source proof changed after validation: {relative}")
    evidence = read(ROOT / candidate["kernel_validation"])
    for record in (evidence["source_preflight"], evidence["canonical_preflight"],
                   read(DEST / "canonical-definition-preflight.json")):
        preflight_valid(record)
    for filename, field in (("source-interface-snapshot.json", "source_snapshot_sha256"),
                            ("canonical-interface-snapshot.json", "canonical_snapshot_sha256")):
        if digest(DEST / filename) != evidence[field]:
            raise ValueError("The serialized kernel snapshot changed")
    original = {row["name"]: row for row in read(DEST / "source-interface-snapshot.json")}
    canonical = {row["name"]: row for row in read(DEST / "canonical-interface-snapshot.json")}
    if set(canonical) != set(candidate["provided_constants"]):
        raise ValueError("The canonical bundle differs from the six expected declarations")
    for name, row in canonical.items():
        if any(row[field] != original[name][field] for field in ("type", "value", "levelParams")):
            raise ValueError(f"Canonical type/body differs from source: {name}")
    # Universe display suffixes come from pp.universes, not extra axioms.
    log = (ROOT / evidence["canonical_preflight"]["log"]).read_text(encoding="utf-8")
    for name in canonical:
        prefix = f"'{name}' depends on axioms: ["
        line = next(line[line.index(prefix):] for line in log.splitlines() if prefix in line)
        for shown in line[len(prefix):].removesuffix("]").split(","):
            shown = shown.strip()
            if shown and shown not in TRUSTED and not any(
                    shown.startswith(base + ".{") and shown.endswith("}") for base in TRUSTED):
                raise ValueError(f"Unexpected canonical axiom: {shown}")
    print(json.dumps({"definitions": len(canonical), "types_and_values_equal": True,
                      "source_files_unchanged": len(validated["port_files_sha256"]),
                      "strict_compilation_evidence_unchanged": True, "standard_axioms_only": True,
                      "ast_and_scope_comparison_pending": not candidate["validated"]}))


if __name__ == "__main__":
    main()
