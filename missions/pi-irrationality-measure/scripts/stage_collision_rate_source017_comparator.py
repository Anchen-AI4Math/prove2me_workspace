"""Pure one-token _source017 comparator bridge for certified AP11 collisionRate.

Only a new target name is staged. The AP11 source, solution, certificate and
publication preparation remain immutable; Lean/API execution belongs to root.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import preflight_staged_module as runner
import stage_grouped_collision_rate_node as ap11

TASK, ROOT, V = ap11.TASK, ap11.ROOT, ap11.V
SELF = Path(__file__).resolve()
STAGE = V / "ap11/collision-rate-source017"
AP11 = ap11.STAGE
CERT = AP11 / "node-validation.json"
PREP = AP11 / "preparation.json"
ORIGINAL_WIRE = AP11 / "wire-theorem-source.lean"
PUBLIC_NAME = ap11.TARGET + "_source017"
OUTPUT = "Theorems/Thm_OAI_PiExponent_DeterminantContradiction_tendsto_collisionRate_source017.lean"
MANIFEST = "c1.json"
AUDIT = "naming-binding-audit.json"
OLD_TOKEN = b"theorem tendsto_collisionRate"
NEW_TOKEN = b"theorem tendsto_collisionRate_source017"


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha_bytes(raw):
    return hashlib.sha256(raw).hexdigest()


def sha(path):
    return sha_bytes(Path(path).read_bytes())


def read(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def encode(doc):
    return (json.dumps(doc, ensure_ascii=False, indent=2) + "\n").encode()


def rel(path):
    return Path(path).resolve().relative_to(TASK.resolve()).as_posix()


def workspace_rel(path):
    return Path(path).resolve().relative_to(ROOT.resolve()).as_posix()


def verification_rel(path):
    return Path(path).resolve().relative_to(V.resolve()).as_posix()


def stage_files():
    cert, prep = read(CERT), read(PREP)
    old = ORIGINAL_WIRE.read_bytes()
    need(cert["validated"] is True and cert["source_name"] == ap11.TARGET
         and cert["source_module"] == ap11.TARGET_MODULE
         and cert["solution_name"] == "solution"
         and cert["source_commit"] == ap11.COMMIT
         and cert["source_type_equals_global_solution_type"] is True
         and cert["source_original_proof_byte_exact_after_name_change"] is True
         and cert["global_top_level_theorem_solution"] is True
         and cert["Std3_only"] is True and cert["wire_theorem_sha256"] == sha_bytes(old),
         "Frozen AP11 actual proof certificate does not bind original comparator")
    need(prep["source_name"] == ap11.TARGET and prep["source_commit"] == ap11.COMMIT
         and prep["source_module"] == ap11.TARGET_MODULE
         and len(prep["inline_exact_source_units"]) == 30
         and len(prep["graph_closure_names"]) == 71,
         "Frozen AP11 source/preparation identity differs")
    olean = TASK / cert["solution_olean"]
    need(olean.is_file() and sha(olean) == cert["solution_olean_sha256"],
         "Certified AP11 solution OLean is missing or changed")
    formal = prep["formal_statement"].replace("\r\n", "\n").encode()
    need(old.count(formal) == 1 and formal.count(OLD_TOKEN) == 1
         and old.count(OLD_TOKEN) == 1,
         "Original AP11 theorem formal/wire name token is not unique")
    start = old.index(formal)
    preamble, suffix = old[:start], old[start + len(formal):]
    need(suffix == b"\n" + ap11.GROUP_FOOTERS[ap11.TARGET_MODULE]
         and b"import Theorems.Thm_" not in preamble,
         "Original AP11 comparator namespace closure or import guard differs")
    new_formal = formal.replace(OLD_TOKEN, NEW_TOKEN, 1)
    new = preamble + new_formal + suffix
    need(new == old.replace(OLD_TOKEN, NEW_TOKEN, 1)
         and new.count(NEW_TOKEN) == 1
         and new.replace(NEW_TOKEN, OLD_TOKEN, 1) == old,
         "The _source017 target changes bytes beyond its one theorem-name token")
    wire = preamble + new_formal
    need(wire == new[:-len(suffix)] and b"sorry" in new_formal,
         "Renamed upload wire/formal placeholder differs")
    inputs = {rel(p): sha(p) for p in [SELF, Path(runner.__file__), ap11.RUNTIME,
                                       CERT, PREP, ORIGINAL_WIRE, olean]}
    manifest = {
        "schema_version": 1,
        "artifact_kind": "ap11-collision-rate-source017-one-comparator-manifest",
        "output": workspace_rel(STAGE / OUTPUT), "output_sha256": sha_bytes(new),
        "imports": ap11.IMPORTS, "input_hashes": inputs,
        "runtime_sha256": sha(ap11.RUNTIME), "mode": "modecheck",
        "emit_olean": False, "timeout_seconds": 300,
        "validated": False, "submission_ready": False,
    }
    audit = {
        "schema_version": 1,
        "artifact_kind": "ap11-collision-rate-source017-finite-naming-binding-audit",
        "status": "prepared-uncompiled", "source_commit": ap11.COMMIT,
        "original_source_name": ap11.TARGET, "public_platform_name": PUBLIC_NAME,
        "old_platform_name_collision_requires_root_GET": True,
        "existing_community_theorem_signature_requires_root_GET": True,
        "old_AP11_wire": rel(ORIGINAL_WIRE), "old_AP11_wire_sha256": sha(ORIGINAL_WIRE),
        "new_exact_comparator": rel(STAGE / OUTPUT),
        "new_exact_comparator_sha256": sha_bytes(new),
        "single_ast_name_token_before": OLD_TOKEN.decode(),
        "single_ast_name_token_after": NEW_TOKEN.decode(),
        "single_name_token_byte_offset": old.index(OLD_TOKEN) + len(b"theorem "),
        "preamble": preamble.decode(), "preamble_sha256": sha_bytes(preamble),
        "renamed_formal_statement": new_formal.decode(),
        "renamed_formal_statement_sha256": sha_bytes(new_formal),
        "namespace_closure_sha256": sha_bytes(suffix),
        "exact_platform_wire_sha256": sha_bytes(wire),
        "renamed_theorem_type_basis": (
            "Only the theorem-name AST token changes. The original source target "
            "and global solution kernel types already match in the immutable AP11 certificate; "
            "the new comparator must modecheck before any platform POST."),
        "AP11_certificate": rel(CERT), "AP11_certificate_sha256": sha(CERT),
        "AP11_solution_olean": rel(olean), "AP11_solution_olean_sha256": sha(olean),
        "AP11_original_solution_reused_without_recompile": True,
        "compiler_manifest": rel(STAGE / MANIFEST),
        "compiler_manifest_sha256": sha_bytes(encode(manifest)),
        "compile_command": ("python scripts/preflight_staged_module.py " +
            verification_rel(STAGE / OUTPUT) +
            " --root ap11/collision-rate-source017 --imports-manifest " +
            verification_rel(STAGE / MANIFEST) + " --timeout-seconds 300"),
        "publication_binding_gate": [
            "Actual comparator c1 modecheck passes within 300 seconds and emits no OLean",
            "Public target name/readback equals OAI.PiExponent.DeterminantContradiction.tendsto_collisionRate_source017",
            "Public preamble and formal_statement reproduce the exact_platform_wire_sha256 bytes",
            "Public solution payload reuses the certified unchanged AP11 global theorem solution",
            "The prior community theorem remains separate and is not cited as a dependency",
        ],
        "input_hashes": inputs, "Lean_started": False, "API_used": False,
        "validated": False, "submission_ready": False, "proposal_status": "Draft",
    }
    return {OUTPUT: new, MANIFEST: encode(manifest), AUDIT: encode(audit)}


def check_only(generated=None):
    generated = stage_files() if generated is None else generated
    for filename, raw in generated.items():
        need((STAGE / filename).is_file() and (STAGE / filename).read_bytes() == raw,
             "Exact isolated _source017 bridge differs: " + filename)
    manifest = read(STAGE / MANIFEST)
    runner.verify_manifest_inputs(manifest)
    runner.verify_source_certificate(STAGE / OUTPUT, manifest)
    return {"checked_files": len(generated), "exact_one_name_token": True,
            "original_AP11_certificate_reused": True, "Lean_started": False,
            "API_used": False, "validated": False, "submission_ready": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--prepare", action="store_true")
    modes.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    generated = None
    if args.prepare:
        generated = stage_files()
        for filename, raw in generated.items():
            path = STAGE / filename
            if path.exists():
                need(path.read_bytes() == raw, "Refusing to overwrite isolated _source017 stage")
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(raw)
    print(json.dumps(check_only(generated), ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
