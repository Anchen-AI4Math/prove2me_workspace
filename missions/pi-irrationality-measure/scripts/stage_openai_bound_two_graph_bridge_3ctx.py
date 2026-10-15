"""Minimal three-context stage for the canonical epsilon/2 graph bridge.

This immutable micro-stage reuses the already frozen bridge bytes.  It omits
the redundant target and closed-source recompilations, binding the latter to
the existing full-build certificate and Std3 audit instead.  No mode starts
Lean, reads credentials, or uses an API.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import stage_openai_bound_two_graph_bridge as full


TASK, ROOT, V = full.TASK, full.ROOT, full.V
BASE = full.STAGE
STAGE = BASE / "three-context"
SELF = Path(__file__).resolve()
HISTORICAL = V / "validated-port-manifest.json"
HISTORICAL_LOG = V / "build-20261007-204658.log"
PARENT_FILE = full.PARENT_FILE
SOLUTION_FILE = full.SOLUTION_FILE
AUDIT_FILE = "OpenParentSolutionAudit.lean"
FILES = [PARENT_FILE, SOLUTION_FILE, AUDIT_FILE]
MANIFESTS = ["c1.json", "c2.json", "c4.json"]
MODES = ["emit-olean", "emit-olean", "modecheck"]


def historical_closure(source_sha):
    record = full.read(HISTORICAL)
    line = ("info: Solutions/Sol_PiIrrationality_openai_bound_two_transfer.lean:18:0: "
            "'solution' depends on axioms: [propext, Classical.choice, Quot.sound]")
    full.need(record["build"]["exit_code"] == 0
              and 0 < record["build"]["seconds"] <= 300
              and record["toolchain"] == "leanprover/lean4:v4.33.1"
              and record["mathlib_rev"] == full.ENV
              and record["upper_bound_solution_sha256"] == source_sha
              and line in record["axiom_audits"]
              and line in HISTORICAL_LOG.read_text(encoding="utf-8"),
              "Historical closed source solution certificate/Std3 audit differs")
    return {"certificate": full.rel(HISTORICAL), "certificate_sha256": full.sha(HISTORICAL),
            "log": full.rel(HISTORICAL_LOG), "log_sha256": full.sha(HISTORICAL_LOG),
            "source_solution_sha256": source_sha, "axioms": ["propext", "Classical.choice", "Quot.sound"],
            "closed_full_build": True}


def stage_files():
    full.check_only()
    old = full.stage_files()
    plan = full.read(BASE / "preparation.json")
    source_sha = plan["source_solution_sha256"]
    closure = historical_closure(source_sha)
    audit = ("import " + full.SOLUTION_MODULE +
             "\n\nexample : PiIrrationality.UpperBound (2 : ℝ) := solution\n\n"
             "#print axioms solution\n").encode()
    generated = {PARENT_FILE: old[PARENT_FILE], SOLUTION_FILE: old[SOLUTION_FILE],
                 AUDIT_FILE: audit, "submitted-solution.lean": old[SOLUTION_FILE],
                 "literal-theorem-command.lean.txt": old["literal-theorem-command.lean.txt"]}
    inputs = {full.rel(path): full.sha(path) for path in
              [SELF, Path(full.__file__), BASE / "preparation.json",
               BASE / "original-shared-solution.lean.txt", HISTORICAL, HISTORICAL_LOG,
               full.TARGET_JSON, full.PARENT_JSON, full.RUNTIME,
               TASK / "scripts/preflight_staged_module.py"]}
    imports = [["Definitions.Def_OAI_PiExponent_ApproximationDefinitions"],
               [full.PARENT_MODULE, "Definitions.Def_PiIrrationality_UpperBound", "Mathlib.Tactic"],
               [full.SOLUTION_MODULE]]
    files, commands = {}, {}
    for output, manifest, mode, imported in zip(FILES, MANIFESTS, MODES, imports, strict=True):
        files[output] = {"sha256": full.sha_bytes(generated[output]), "manifest": manifest,
                         "mode": mode, "emit_olean": mode == "emit-olean", "imports": imported}
        generated[manifest] = full.encode({
            "schema_version": 1,
            "artifact_kind": "canonical-openai-bound-two-graph-bridge-3ctx-compiler-manifest",
            "output": full.workspace_rel(STAGE / output),
            "output_sha256": full.sha_bytes(generated[output]),
            "imports": imported,
            "input_hashes": inputs,
            "runtime_sha256": full.sha(full.RUNTIME),
            "mode": mode,
            "emit_olean": mode == "emit-olean",
            "timeout_seconds": 300,
            "validated": False,
            "submission_ready": False,
        })
        commands[output] = ("python scripts/preflight_staged_module.py " +
            full.verification_rel(STAGE / output) + " --root graph-bridge-20261011/three-context" +
            " --imports-manifest " + full.verification_rel(STAGE / manifest) +
            " --timeout-seconds 300" + (" --emit-olean" if mode == "emit-olean" else ""))
    generated["preparation.json"] = full.encode({
        "schema_version": 1,
        "artifact_kind": "canonical-openai-bound-two-graph-bridge-3ctx-preparation",
        "target_theorem_id": full.TARGET_ID,
        "target_theorem_name": "PiIrrationality.openai_bound_two",
        "parent_theorem_id": full.PARENT_ID,
        "parent_theorem_name": "OAI.PiExponent.pi_eventual_lower_bound",
        "environment": full.ENV,
        "files": files,
        "compile_order": FILES,
        "compile_commands": commands,
        "context_roles": {
            PARENT_FILE: "exact latest-GET Open parent sketch emitter; expected sorryAx; type validation only",
            SOLUTION_FILE: "exact submitted solution emitter; no own sorry, #print, or target import",
            AUDIT_FILE: "checks the complete solution type is UpperBound 2 and audits axioms",
        },
        "open_parent_sorryAx_expected": True,
        "open_parent_reference_is_not_closed_proof_evidence": True,
        "solution_own_code_has_sorry": False,
        "solution_body_literal_source_bytes": True,
        "canonical_target_type_from_exact_GET": "PiIrrationality.UpperBound (2 : ℝ)",
        "canonical_target_definition_already_kernel_certified": True,
        "historical_closed_source_solution": closure,
        "input_hashes": inputs,
        "runtime_sha256": full.sha(full.RUNTIME),
        "single_compiler_sequential": True,
        "Lean_started": False, "API_used": False, "network_used": False,
        "validated": False, "submission_ready": False,
    })
    return generated


def check_only(generated=None):
    generated = stage_files() if generated is None else generated
    for name, raw in generated.items():
        path = STAGE / name
        full.need(path.is_file() and path.read_bytes() == raw,
                  "Immutable three-context graph bridge stage differs: " + name)
    return {"checked_files": len(generated), "compiler_contexts": 3,
            "historical_closed_mirror_reused": True,
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
            full.need(path.read_bytes() == raw,
                      "Refusing to overwrite changed three-context bridge stage: " + name)
        elif args.prepare:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(raw)
        else:
            raise ValueError("Missing three-context bridge stage: " + name)
    print(json.dumps(check_only(generated), ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
