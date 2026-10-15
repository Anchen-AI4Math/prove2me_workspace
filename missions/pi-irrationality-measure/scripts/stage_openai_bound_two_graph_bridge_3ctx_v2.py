"""Corrected three-context bridge stage with literal c2 import order."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import stage_openai_bound_two_graph_bridge as full
import stage_openai_bound_two_graph_bridge_3ctx as prior


TASK, ROOT, V = prior.TASK, prior.ROOT, prior.V
BASE = prior.BASE
STAGE = BASE / "three-context-v2"
SELF = Path(__file__).resolve()
PARENT_FILE, SOLUTION_FILE, AUDIT_FILE = prior.PARENT_FILE, prior.SOLUTION_FILE, prior.AUDIT_FILE
FILES, MANIFESTS, MODES = prior.FILES, prior.MANIFESTS, prior.MODES


def stage_files():
    full.check_only()
    frozen = full.stage_files()
    old_plan = full.read(BASE / "preparation.json")
    source_sha = old_plan["source_solution_sha256"]
    closure = prior.historical_closure(source_sha)
    audit = ("import " + full.SOLUTION_MODULE +
             "\n\nexample : PiIrrationality.UpperBound (2 : ℝ) := solution\n\n"
             "#print axioms solution\n").encode()
    generated = {PARENT_FILE: frozen[PARENT_FILE], SOLUTION_FILE: frozen[SOLUTION_FILE],
                 AUDIT_FILE: audit, "submitted-solution.lean": frozen[SOLUTION_FILE],
                 "literal-theorem-command.lean.txt": frozen["literal-theorem-command.lean.txt"]}
    inputs = {full.rel(path): full.sha(path) for path in
              [SELF, Path(full.__file__), Path(prior.__file__), BASE / "preparation.json",
               BASE / "original-shared-solution.lean.txt", prior.HISTORICAL,
               prior.HISTORICAL_LOG, full.TARGET_JSON, full.PARENT_JSON,
               full.RUNTIME, TASK / "scripts/preflight_staged_module.py"]}
    imports = [["Definitions.Def_OAI_PiExponent_ApproximationDefinitions"],
               ["Mathlib.Tactic", full.PARENT_MODULE, "Definitions.Def_PiIrrationality_UpperBound"],
               [full.SOLUTION_MODULE]]
    files, commands = {}, {}
    for output, manifest, mode, imported in zip(FILES, MANIFESTS, MODES, imports, strict=True):
        files[output] = {"sha256": full.sha_bytes(generated[output]), "manifest": manifest,
                         "mode": mode, "emit_olean": mode == "emit-olean", "imports": imported}
        generated[manifest] = full.encode({
            "schema_version": 1,
            "artifact_kind": "canonical-openai-bound-two-graph-bridge-3ctx-v2-compiler-manifest",
            "output": full.workspace_rel(STAGE / output),
            "output_sha256": full.sha_bytes(generated[output]),
            "imports": imported,
            "input_hashes": inputs,
            "runtime_sha256": full.sha(full.RUNTIME),
            "mode": mode, "emit_olean": mode == "emit-olean", "timeout_seconds": 300,
            "validated": False, "submission_ready": False,
        })
        commands[output] = ("python scripts/preflight_staged_module.py " +
            full.verification_rel(STAGE / output) + " --root graph-bridge-20261011/three-context-v2" +
            " --imports-manifest " + full.verification_rel(STAGE / manifest) +
            " --timeout-seconds 300" + (" --emit-olean" if mode == "emit-olean" else ""))
    generated["preparation.json"] = full.encode({
        "schema_version": 1,
        "artifact_kind": "canonical-openai-bound-two-graph-bridge-3ctx-v2-preparation",
        "supersedes_uncompiled_micro_stage": full.rel(prior.STAGE),
        "superseded_reason": "c2 manifest import order did not match literal source header",
        "old_actual_parent_context_reused": full.rel(BASE / full.PARENT_FILE),
        "old_actual_parent_olean_sha256_expected":
            "593bf91b2c603a564cc2daf39f7257c577ddfa39ff4e31e15a22edf29146b8a5",
        "target_theorem_id": full.TARGET_ID, "target_theorem_name": "PiIrrationality.openai_bound_two",
        "parent_theorem_id": full.PARENT_ID,
        "parent_theorem_name": "OAI.PiExponent.pi_eventual_lower_bound",
        "environment": full.ENV, "files": files, "compile_order": FILES,
        "compile_commands": commands,
        "context_roles": {
            PARENT_FILE: "byte-identical old-stage c1 actual emitter reused; expected sorryAx/type-only",
            SOLUTION_FILE: "exact submitted solution emitter with literal import order",
            AUDIT_FILE: "complete UpperBound 2 typecheck and expected Open-parent axiom audit",
        },
        "c2_literal_import_order": imports[1],
        "open_parent_sorryAx_expected": True,
        "open_parent_reference_is_not_closed_proof_evidence": True,
        "solution_own_code_has_sorry": False,
        "solution_body_literal_source_bytes": True,
        "canonical_target_type_from_exact_GET": "PiIrrationality.UpperBound (2 : ℝ)",
        "historical_closed_source_solution": closure,
        "input_hashes": inputs, "runtime_sha256": full.sha(full.RUNTIME),
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
                  "Immutable corrected three-context bridge stage differs: " + name)
    return {"checked_files": len(generated), "compiler_contexts": 3,
            "c1_actual_old_stage_reused": True, "historical_closed_mirror_reused": True,
            "Lean_started": False, "API_used": False, "network_used": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--prepare", action="store_true")
    modes.add_argument("--check-only", action="store_true")
    args = parser.parse_args(); generated = stage_files()
    for name, raw in generated.items():
        path = STAGE / name
        if path.exists():
            full.need(path.read_bytes() == raw, "Refusing to overwrite corrected bridge stage: " + name)
        elif args.prepare:
            path.parent.mkdir(parents=True, exist_ok=True); path.write_bytes(raw)
        else:
            raise ValueError("Missing corrected bridge stage: " + name)
    print(json.dumps(check_only(generated), ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
