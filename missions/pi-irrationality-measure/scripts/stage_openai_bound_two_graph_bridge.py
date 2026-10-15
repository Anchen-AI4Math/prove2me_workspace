"""Stage the source-faithful epsilon/2 bridge for the canonical pi root.

The two server theorem reference modules intentionally reproduce current Open
theorem sketches and therefore contain ``sorry`` only for type validation.
The submitted solution has no ``sorry`` or ``#print`` and changes only the
parent import relative to the already compiled source solution.  This script
does not start Lean, use credentials, or call an API.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import preflight_staged_module as preflight


TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
V = TASK / "verification"
STAGE = V / "graph-bridge-20261011"
REFRESH = V / "graph-refresh-20261011T131418_012581Z"
SELF = Path(__file__).resolve()
RUNTIME = V / "lean-runtime.json"
SOURCE = ROOT / "Solutions/Sol_PiIrrationality_openai_bound_two_transfer.lean"
TARGET_ID = "406736ed-98ce-4177-b97f-24de96ba4188"
PARENT_ID = "e717eef2-11b1-4b14-9789-65f52c0502e1"
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"
TARGET_JSON = REFRESH / f"{TARGET_ID}-target.json"
PARENT_JSON = REFRESH / f"{PARENT_ID}-target.json"
SOURCE_IMPORT = b"import OAI.NumberTheory.PiExponent.Main"
PLATFORM_IMPORT = b"import Theorems.Thm_OAI_PiExponent_pi_eventual_lower_bound"
PLATFORM_IMPORT_BLOCK = b"import Mathlib.Tactic\n" + PLATFORM_IMPORT
PARENT_MODULE = "Theorems.Thm_OAI_PiExponent_pi_eventual_lower_bound"
SOLUTION_MODULE = "Solutions.Sol_PiIrrationality_openai_bound_two_transfer_graph_bridge"
TARGET_SKETCH_MODULE = "Theorems.Thm_PiIrrationality_openai_bound_two_graph_bridge_target_sketch"
SOURCE_MIRROR_MODULE = "Solutions.Sol_PiIrrationality_openai_bound_two_transfer_source_mirror"
PARENT_FILE = PARENT_MODULE.replace(".", "/") + ".lean"
SOLUTION_FILE = SOLUTION_MODULE.replace(".", "/") + ".lean"
TARGET_SKETCH_FILE = TARGET_SKETCH_MODULE.replace(".", "/") + ".lean"
OPEN_AUDIT_FILE = "OpenParentSolutionAudit.lean"
SOURCE_MIRROR_FILE = SOURCE_MIRROR_MODULE.replace(".", "/") + ".lean"
SOURCE_AUDIT_FILE = "SourceMirrorSolutionAudit.lean"
FILES = [PARENT_FILE, SOLUTION_FILE, TARGET_SKETCH_FILE, OPEN_AUDIT_FILE,
         SOURCE_MIRROR_FILE, SOURCE_AUDIT_FILE]
MANIFESTS = [f"c{i}.json" for i in range(1, 7)]
MODES = ["emit-olean", "emit-olean", "emit-olean", "modecheck", "emit-olean", "modecheck"]


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha_bytes(raw):
    return hashlib.sha256(raw).hexdigest()


def sha(path):
    return sha_bytes(Path(path).read_bytes())


def read(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def encode(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode()


def rel(path):
    return Path(path).resolve().relative_to(TASK.resolve()).as_posix()


def workspace_rel(path):
    return Path(path).resolve().relative_to(ROOT.resolve()).as_posix()


def verification_rel(path):
    return Path(path).resolve().relative_to(V.resolve()).as_posix()


def server_sketch(record):
    return (record["preamble"].rstrip() + "\n\n" +
            record["formal_statement"].rstrip() + "\n").encode()


def without_axiom_print(raw):
    marker = b"\n#print axioms solution"
    need(raw.count(marker) == 1 and raw.rstrip().endswith(b"#print axioms solution"),
         "Shared source solution has a different audit suffix")
    return raw[:raw.index(marker)] + b"\n"


def source_units():
    raw = SOURCE.read_bytes()
    need(raw.count(SOURCE_IMPORT) == 1 and PLATFORM_IMPORT not in raw,
         "Shared bridge source import differs")
    mirror = without_axiom_print(raw)
    submitted = without_axiom_print(raw.replace(SOURCE_IMPORT, PLATFORM_IMPORT_BLOCK, 1))
    start = raw.index(b"theorem solution")
    end = raw.index(b"\n#print axioms solution")
    command = raw[start:end]
    need(command in mirror and command in submitted
         and mirror.count(b"theorem solution") == 1
         and submitted.count(b"theorem solution") == 1
         and b"sorry" not in command and b"#print" not in submitted,
         "Submitted theorem body is not the literal closed shared bridge")
    need(submitted.replace(PLATFORM_IMPORT_BLOCK, SOURCE_IMPORT, 1) == mirror,
         "Submitted bridge changes outside its explicit import-header replacement")
    return raw, mirror, submitted, command


def stage_files():
    target, parent = read(TARGET_JSON), read(PARENT_JSON)
    need(target["theorem_id"] == TARGET_ID
         and target["theorem_name"] == "PiIrrationality.openai_bound_two"
         and target["status"] == "Open" and target["mathlib_rev"] == ENV
         and target["preamble"] == "import Definitions.Def_PiIrrationality_UpperBound",
         "Canonical target GET snapshot differs")
    need(parent["theorem_id"] == PARENT_ID
         and parent["theorem_name"] == "OAI.PiExponent.pi_eventual_lower_bound"
         and parent["status"] == "Open" and parent["mathlib_rev"] == ENV
         and parent["formal_statement"] ==
             "theorem OAI.PiExponent.pi_eventual_lower_bound : PiEventualLowerBound := by sorry",
         "Open parent GET snapshot differs")
    source_raw, mirror, submitted, command = source_units()
    parent_sketch, target_sketch = server_sketch(parent), server_sketch(target)
    open_audit = ("import " + SOLUTION_MODULE + "\nimport " + TARGET_SKETCH_MODULE +
        "\n\nexample : PiIrrationality.UpperBound (2 : ℝ) := solution\n\n"
        "#print axioms solution\n").encode()
    source_audit = ("import " + SOURCE_MIRROR_MODULE +
        "\n\nexample : PiIrrationality.UpperBound (2 : ℝ) := solution\n\n"
        "#print axioms solution\n").encode()
    generated = {PARENT_FILE: parent_sketch, SOLUTION_FILE: submitted,
                 TARGET_SKETCH_FILE: target_sketch, OPEN_AUDIT_FILE: open_audit,
                 SOURCE_MIRROR_FILE: mirror, SOURCE_AUDIT_FILE: source_audit,
                 "literal-theorem-command.lean.txt": command,
                 "original-shared-solution.lean.txt": source_raw,
                 "submitted-solution.lean": submitted}
    inputs = {rel(path): sha(path) for path in
              [SELF, TARGET_JSON, PARENT_JSON, RUNTIME, Path(preflight.__file__)]}
    inputs[rel(STAGE / "original-shared-solution.lean.txt")] = sha_bytes(source_raw)
    imports = [
        ["Definitions.Def_OAI_PiExponent_ApproximationDefinitions"],
        [PARENT_MODULE, "Definitions.Def_PiIrrationality_UpperBound"],
        ["Definitions.Def_PiIrrationality_UpperBound"],
        [SOLUTION_MODULE, TARGET_SKETCH_MODULE],
        ["OAI.NumberTheory.PiExponent.Main", "Definitions.Def_PiIrrationality_UpperBound"],
        [SOURCE_MIRROR_MODULE],
    ]
    files, commands = {}, {}
    for output, manifest, mode, imported in zip(FILES, MANIFESTS, MODES, imports, strict=True):
        files[output] = {"sha256": sha_bytes(generated[output]), "manifest": manifest,
                         "mode": mode, "emit_olean": mode == "emit-olean", "imports": imported}
        generated[manifest] = encode({
            "schema_version": 1,
            "artifact_kind": "canonical-openai-bound-two-graph-bridge-compiler-manifest",
            "output": workspace_rel(STAGE / output),
            "output_sha256": sha_bytes(generated[output]),
            "imports": imported,
            "input_hashes": inputs,
            "runtime_sha256": sha(RUNTIME),
            "mode": mode,
            "emit_olean": mode == "emit-olean",
            "timeout_seconds": 300,
            "validated": False,
            "submission_ready": False,
        })
        commands[output] = ("python scripts/preflight_staged_module.py " +
            verification_rel(STAGE / output) + " --root graph-bridge-20261011" +
            " --imports-manifest " + verification_rel(STAGE / manifest) +
            " --timeout-seconds 300" + (" --emit-olean" if mode == "emit-olean" else ""))
    generated["preparation.json"] = encode({
        "schema_version": 1,
        "artifact_kind": "canonical-openai-bound-two-graph-bridge-preparation",
        "target_theorem_id": TARGET_ID,
        "target_theorem_name": target["theorem_name"],
        "parent_theorem_id": PARENT_ID,
        "parent_theorem_name": parent["theorem_name"],
        "environment": ENV,
        "source_solution": workspace_rel(SOURCE),
        "source_solution_sha256": sha_bytes(source_raw),
        "literal_theorem_command_sha256": sha_bytes(command),
        "submitted_solution_sha256": sha_bytes(submitted),
        "submitted_solution_changes_only_import_header": True,
        "submitted_import_replacement": {
            "removed": SOURCE_IMPORT.decode(),
            "added": PLATFORM_IMPORT_BLOCK.decode().splitlines(),
            "Mathlib_Tactic_is_library_only_not_platform_child": True,
        },
        "theorem_solution_command_literal_source_bytes": True,
        "submitted_solution_has_no_sorry_or_print": True,
        "server_parent_reference_is_open_sketch_type_validation_only": True,
        "server_parent_reference_is_not_closed_proof_evidence": True,
        "server_parent_preamble_sha256": sha_bytes(parent["preamble"].encode()),
        "server_parent_formal_statement_sha256": sha_bytes(parent["formal_statement"].encode()),
        "server_parent_reference_module_sha256": sha_bytes(parent_sketch),
        "canonical_target_reference_is_open_sketch_type_validation_only": True,
        "canonical_target_reference_module_sha256": sha_bytes(target_sketch),
        "actual_source_olean_mirror_is_independent_closure_check": True,
        "files": files,
        "compile_commands": commands,
        "compile_order": FILES,
        "single_compiler_sequential": True,
        "input_hashes": inputs,
        "runtime_sha256": sha(RUNTIME),
        "Lean_started": False,
        "API_used": False,
        "network_used": False,
        "validated": False,
        "submission_ready": False,
    })
    return generated


def check_only(generated=None):
    generated = stage_files() if generated is None else generated
    for name, raw in generated.items():
        path = STAGE / name
        need(path.is_file() and path.read_bytes() == raw, "Immutable graph bridge stage differs: " + name)
    return {"checked_files": len(generated), "compiler_contexts": 6,
            "Lean_started": False, "API_used": False, "network_used": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--prepare", action="store_true")
    modes.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    generated = stage_files()
    for name, raw in generated.items():
        path = STAGE / name
        if path.exists():
            need(path.read_bytes() == raw, "Refusing to overwrite changed graph bridge stage: " + name)
        elif args.prepare:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(raw)
        else:
            raise ValueError("Missing graph bridge stage: " + name)
    print(json.dumps(check_only(generated), ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
