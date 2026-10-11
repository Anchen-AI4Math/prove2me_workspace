"""Certify reuse of the existing six-definition bundle with exact oracle AST evidence."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import check_definition_kernel_reuse
from index_ast_scopes import recover_scopes
from validate_ast_facts import validate_facts

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
DEST = TASK / "verification"


def read(path):
    return json.loads(path.read_text(encoding="utf-8"))


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_ast(record, expected_source, expected_hash):
    if (record["source"] != expected_source or record["source_sha256"] != expected_hash
            or record["exit_code"] != 0 or record["timed_out"]
            or not record["source_unchanged"] or not 0 < record["timeout_seconds"] <= 300):
        raise ValueError("Definition AST extraction must pass strict compilation for the exact source")
    source = ROOT / expected_source
    facts_path = ROOT / record["log"]
    facts = [json.loads(line) for line in facts_path.read_text(encoding="utf-8").splitlines()]
    positions = validate_facts(source, facts, expected_hash)
    for name, field in (("TargetAxioms/SketchOracle.lean", "oracle_sha256"),
                        ("RunSketchOracle.lean", "runner_sha256")):
        if digest(DEST / name) != record[field]:
            raise ValueError("The canonical and source facts must use the current sanctioned oracle")
    return source.read_bytes(), facts, {"facts": record["log"],
                                       "facts_sha256": digest(facts_path),
                                       "raw_byte_validation": positions,
                                       "preflight": record}


def declaration_map(data, facts, names, label):
    scopes = recover_scopes(label, facts, set(names))
    decls = {fact["declStart"]["offset"]: fact for fact in facts if fact["kind"] == "decl"}
    result = {}
    for scope in scopes:
        name = scope["verified_name"]
        if name not in names or name in result:
            raise ValueError("The canonical module must provide each expected definition once")
        decl = decls[scope["range"]["start"]["offset"]]
        start, end = decl["declStart"]["offset"], decl["declEnd"]["offset"]
        contexts = [{"syntaxKind": command["syntaxKind"],
                     "bytes": data[command["range"]["start"]["offset"]:
                                   command["range"]["end"]["offset"]]}
                    for command in scope["context_commands"]]
        result[name] = {"bytes": data[start:end], "namespace": scope["namespace"],
                        "scope_stack": [{"kind": frame["kind"], "name": frame["name"]}
                                        for frame in scope["scope_stack"]],
                        "contexts": contexts, "range": scope["range"]}
    if set(result) != set(names):
        raise ValueError("AST declaration set differs from the kernel-certified definition set")
    return result


def main():
    # This independently verifies the types, values, level parameters and axioms.
    check_definition_kernel_reuse.main()
    candidate_path = TASK / "platform/definition-reuse-candidates.json"
    candidates = read(candidate_path)
    candidate = candidates["reuse_candidates"][0]
    state = read(DEST / "extraction-state.json")
    relative = candidate["source_module"].replace(".", "/") + ".lean"
    entry = state["stage2"][relative]
    if digest(ROOT / entry["facts"]) != entry["facts_sha256"]:
        raise ValueError("The source AST differs from the validated extraction state")
    source_data, source_facts, source_evidence = load_ast(
        entry["preflight"], candidate["source"], candidate["source_sha256"])
    canonical_data, canonical_facts, canonical_evidence = load_ast(
        read(DEST / "canonical-definition-ast-preflight.json"),
        candidate["existing_source"], candidate["existing_sha256"])
    names = candidate["provided_constants"]
    source = declaration_map(source_data, source_facts, names, relative)
    canonical = declaration_map(canonical_data, canonical_facts, names, candidate["existing_source"])
    matches = []
    for name in names:
        for field in ("bytes", "namespace", "scope_stack", "contexts"):
            if source[name][field] != canonical[name][field]:
                raise ValueError(f"Definition AST reuse differs in {field}: {name}")
        matches.append({"name": name, "command_bytes_equal": True,
                        "command_sha256": hashlib.sha256(source[name]["bytes"]).hexdigest(),
                        "namespace": source[name]["namespace"],
                        "scopes_and_context_equal": True,
                        "source_range": source[name]["range"],
                        "canonical_range": canonical[name]["range"]})
    output = DEST / "definition-reuse-ast-validation.json"
    report = {"at_utc": datetime.now(timezone.utc).isoformat(),
              "definitions": matches, "source_evidence": source_evidence,
              "canonical_evidence": canonical_evidence,
              "kernel_evidence": candidate["kernel_validation"],
              "kernel_evidence_sha256": digest(ROOT / candidate["kernel_validation"]),
              "validated": True,
              "generated_consumer_type_diff_still_required": True}
    output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    candidate.update({"validated": True, "pending_checks": [],
                      "ast_validation": output.relative_to(ROOT).as_posix(),
                      "ast_validation_sha256": digest(output)})
    candidates["definition_reuse_validated"] = True
    candidate_path.write_text(json.dumps(candidates, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"definitions": len(matches), "command_bytes_equal": True,
                      "scopes_and_context_equal": True, "kernel_validated": True,
                      "definition_reuse_validated": True,
                      "generated_consumer_type_diff_still_required": True}))


if __name__ == "__main__":
    main()
