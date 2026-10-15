"""Pure successor stage: inline five exact source AdmissibleParameters helpers.

Reuse the five actually compiled Open child theorem modules from v1. Recompile
only a new global solution and two type/reference snapshot modules. The v1
failed source/sidecar/log and all v1 compiler inputs remain untouched.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import stage_graph_no_fixed_data_five_children as old


TASK, ROOT = old.TASK, old.ROOT
STAGE = TASK / "verification/graph-no-fixed-data-route-20261011-v2"
SELF = Path(__file__).resolve()
ADMISSIBLE_PORT = TASK / "port/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleParameters.lean"
ADMISSIBLE_SOURCE = TASK / "source/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleParameters.lean"
ADMISSIBLE_MODULE = "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters"
SOL_MODULE = "Solutions.Sol_OAI_PiExponent_DeterminantContradiction_no_fixed_data_five_children_v2"
SOL_FILE = SOL_MODULE.replace(".", "/") + ".lean"
SOURCE_FILE = "SourceSnapshot.lean"
GENERATED_FILE = "GeneratedSnapshot.lean"
SOURCE_JSON = "source-eleven-types-and-refs.json"
GENERATED_HELPERS_JSON = "generated-five-helper-types-and-refs.json"
GENERATED_SEVEN_JSON = "generated-seven-types-and-refs.json"
NAMES = ["total_error_lt_gap", "collision_exceeds_one_add_error", "error_sum_eq",
         "error_sum_lt_gap", "collision_exceeds_error_sum"]
SOURCE_NAMES = ["OAI.PiExponent.AdmissibleParameters." + name for name in NAMES]
FOLLOWERS = ["theorem collision_exceeds_one_add_error", "noncomputable def arithmeticError",
             "theorem error_sum_lt_gap", "theorem collision_exceeds_error_sum",
             "end AdmissibleParameters"]
FAILED_SOL = old.STAGE / old.SOL_FILE
FAILED_SIDECAR = FAILED_SOL.with_suffix(".lean.preflight.json")


def need(ok, message):
    if not ok:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def sha(path):
    return digest(Path(path).read_bytes())


def read(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def encode(doc):
    return (json.dumps(doc, ensure_ascii=False, indent=2) + "\n").encode()


def task_rel(path):
    return Path(path).resolve().relative_to(TASK.resolve()).as_posix()


def root_rel(path):
    return Path(path).resolve().relative_to(ROOT.resolve()).as_posix()


def verification_rel(path):
    return Path(path).resolve().relative_to((TASK / "verification").resolve()).as_posix()


def source_commands():
    raw = ADMISSIBLE_SOURCE.read_bytes()
    cmds = []
    spans = []
    for name, follower in zip(NAMES, FOLLOWERS, strict=True):
        start = raw.index(("theorem " + name + " ").encode()) if name != "error_sum_eq" else raw.index(b"theorem error_sum_eq :")
        end = raw.index(follower.encode(), start + 1)
        command = raw[start:end].rstrip(b"\r\n") + b"\n"
        need(command.count(("theorem " + name).encode()) == 1 and
             command.count(b":= by") == 1,
             "Actual source helper theorem command boundary differs: " + name)
        cmds.append(command)
        spans.append({"name": "OAI.PiExponent.AdmissibleParameters." + name,
                      "source_start_byte": start, "source_end_byte_exclusive": end,
                      "source_lines": [raw[:start].count(b"\n") + 1,
                                       raw[:end].count(b"\n") + 1],
                      "original_command_sha256": digest(command),
                      "original_proof_sha256": digest(command.partition(b":= by")[2])})
    return cmds, spans


def snapshot_exporter():
    raw = old.EXPORTER.read_text(encoding="utf-8")
    body = raw[raw.index("open Lean Meta"):raw.index("run_meta do")]
    need("namespace SourceRootGraphSnapshot" in body and "valueRefs" in body and
         "actualOwner" in body, "Actual prior snapshot exporter changed")
    return body


def snapshot_call(names, owners, output, open_targets):
    need(len(names) == len(owners), "Snapshot names/owners differ")
    qnames = ", ".join("`" + name for name in names)
    qowners = ", ".join(json.dumps(owner) for owner in owners)
    return ("run_meta do\n  SourceRootGraphSnapshot.exportRows #[" + qnames +
            "] #[" + qowners + "] \"" + root_rel(STAGE / output) + "\" " +
            ("true" if open_targets else "false") + "\n\n" +
            "".join("#print axioms " + name + "\n" for name in names))


def old_open_emitters():
    old.check()
    records = []
    for i, child in enumerate(old.CHILDREN + [("arithmetic", old.ARITH, old.ARITH_SOURCE,
                                                old.ARITH_MODULE, None, "Open")], 1):
        module = child[3]
        source = old.STAGE / (module.replace(".", "/") + ".lean")
        manifest = old.STAGE / f"c{i}.json"
        sidecar = source.with_suffix(".lean.preflight.json")
        d = read(sidecar)
        need(d["success"] is True and d["exit_code"] == 0 and
             d["mode"] == "emit-olean" and d["actual_module_identity"] == module and
             d["source_sha256_before"] == sha(source) and
             d["manifest_sha256_before"] == sha(manifest) and
             0 < d["seconds"] <= 300,
             "Previous actual child emitter lacks successful bounded evidence: " + module)
        output = TASK / d["output_olean"]
        need(output.is_file() and sha(output) == d["output_olean_sha256"],
             "Previous actual child emitter OLean changed: " + module)
        records.append({"module": module, "source": task_rel(source), "source_sha256": sha(source),
                        "manifest": task_rel(manifest), "manifest_sha256": sha(manifest),
                        "sidecar": task_rel(sidecar), "sidecar_sha256": sha(sidecar),
                        "output_olean": task_rel(output), "output_olean_sha256": sha(output),
                        "seconds": d["seconds"]})
    return records


def stages():
    emitters = old_open_emitters()
    failed = read(FAILED_SIDECAR)
    failed_log = TASK / failed["log"]
    need(failed["success"] is False and failed["exit_code"] != 0 and
         failed["actual_module_identity"] == old.SOL_MODULE and
         failed["source_sha256_before"] == sha(FAILED_SOL) and
         failed_log.is_file() and
         "error_sum_lt_gap" in failed_log.read_text(encoding="utf-8") and
         "collision_exceeds_error_sum" in failed_log.read_text(encoding="utf-8"),
         "Frozen v1 failed preflight does not show the two missing source lemmas")
    commands, spans = source_commands()
    port_raw = ADMISSIBLE_PORT.read_bytes().replace(b"\r\n", b"\n")
    source_raw = ADMISSIBLE_SOURCE.read_bytes().replace(b"\r\n", b"\n")
    for name, follower, command in zip(NAMES, FOLLOWERS, commands, strict=True):
        start = port_raw.index(("theorem " + name).encode())
        end = port_raw.index(follower.encode(), start + 1)
        need(port_raw[start:end].strip() == command.replace(b"\r\n", b"\n").strip() and
             command in source_raw,
             "Original source and port source-helper AST/proof bytes differ: " + name)
    original = FAILED_SOL.read_bytes()
    where = original.index(b"theorem solution")
    preamble, theorem = original[:where], original[where:]
    old_source = (old.STAGE / "original-no-fixed-data-command.lean.txt").read_bytes()
    _head, _sep, old_proof = old_source.partition(b":= by")
    new_proof = theorem.partition(b":= by")[2]
    old_proof = old_proof.replace(b"(tendsto_collisionRate d).sub",
                                  b"(tendsto_collisionRate_source017 d).sub", 1)
    old_proof = old_proof.replace(b"have hlower := actual_minor_arithmetic_lower_bound d H hH selection hdet'",
                                  b"have hlower := actual_minor_arithmetic_lower_bound_source017 d H hH selection hdet'", 1)
    need(new_proof == old_proof and theorem.count(b"theorem solution") == 1,
         "NoFixedData 41-line proof changed beyond the original two source names")
    helper_prefix = ("namespace OAI\nnamespace PiExponent\nnamespace AdmissibleParameters\n\n"
                     "variable {nu Lambda c : ℝ} (d : AdmissibleParameters nu Lambda c)\n\n").encode()
    helper_footer = b"end AdmissibleParameters\nend PiExponent\nend OAI\n\n"
    helper_body = b"\n".join(commands)
    solution = preamble + helper_prefix + helper_body + helper_footer + theorem
    need(solution.count(b"theorem solution") == 1 and b"sorry" not in solution and
         all(solution.count(("theorem " + n).encode()) == 1 for n in NAMES),
         "Successor global solution/helper prefix differs")
    old_prep = read(old.STAGE / "preparation.json")
    source_six = old_prep["source_snapshot_names"]
    source_six_owners = old_prep["source_snapshot_owners"]
    generated_seven = old_prep["generated_snapshot_names"]
    generated_seven[-1] = "solution"
    generated_seven_owners = old_prep["generated_snapshot_owners"]
    generated_seven_owners[-1] = SOL_MODULE
    source_names = SOURCE_NAMES + source_six
    source_owners = [ADMISSIBLE_MODULE] * 5 + source_six_owners
    generated_helper_owners = [SOL_MODULE] * 5
    exporter = snapshot_exporter()
    source_imports = ["Lean", ADMISSIBLE_MODULE, old.SOURCE_MODULE,
                      "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
                      "OAI.NumberTheory.PiExponent.Approximation.Comparison"]
    generated_imports = ["Lean", *old.DEF_IMPORTS, old.NFD_MODULE,
                         *[row["module"] for row in emitters], SOL_MODULE]
    source_snapshot = ("".join("import " + imp + "\n" for imp in source_imports) + "\n" +
                       exporter + snapshot_call(source_names, source_owners, SOURCE_JSON, False)).encode()
    generated_snapshot = ("".join("import " + imp + "\n" for imp in generated_imports) + "\n" +
                          exporter + snapshot_call(SOURCE_NAMES, generated_helper_owners,
                                                   GENERATED_HELPERS_JSON, False) +
                          snapshot_call(generated_seven, generated_seven_owners,
                                        GENERATED_SEVEN_JSON, True)).encode()
    files = {SOL_FILE: solution, SOURCE_FILE: source_snapshot, GENERATED_FILE: generated_snapshot}
    for name, command in zip(NAMES, commands, strict=True):
        files["original-helper-commands/" + name + ".lean.txt"] = command
    input_paths = [SELF, ADMISSIBLE_PORT, ADMISSIBLE_SOURCE, FAILED_SOL, FAILED_SIDECAR,
                   failed_log, old.STAGE / "preparation.json",
                   old.STAGE / "original-no-fixed-data-command.lean.txt",
                   old.STAGE / old.NFD_FILE, old.STAGE / "arithmetic-source017-open-wire.lean",
                   old.EXPORTER, old.RUNTIME, old.RUNNER,
                   *[TASK / item[key] for item in emitters
                     for key in ("source", "manifest", "sidecar", "output_olean")]]
    input_hashes = {task_rel(path): sha(path) for path in input_paths}
    compile_order = [("c1.json", SOL_FILE, "emit-olean"),
                     ("c2.json", SOURCE_FILE, "modecheck"),
                     ("c3.json", GENERATED_FILE, "modecheck")]
    commands_to_run = {}
    for manifest_name, filename, mode in compile_order:
        imports = [row[len("import "):] for row in files[filename].decode().splitlines()
                   if row.startswith("import ")]
        manifest = {"schema_version": 1,
                    "artifact_kind": "NoFixedData-five-child-source-helpers-successor-preflight",
                    "output": root_rel(STAGE / filename), "output_sha256": digest(files[filename]),
                    "imports": imports, "input_hashes": input_hashes,
                    "runtime_sha256": sha(old.RUNTIME), "mode": mode,
                    "emit_olean": mode == "emit-olean", "timeout_seconds": 300,
                    "validated": False, "submission_ready": False}
        files[manifest_name] = encode(manifest)
        commands_to_run[manifest_name] = (
            "python scripts/preflight_staged_module.py " + verification_rel(STAGE / filename) +
            " --root graph-no-fixed-data-route-20261011-v2 --imports-manifest " +
            verification_rel(STAGE / manifest_name) + " --timeout-seconds 300" +
            (" --emit-olean" if mode == "emit-olean" else ""))
    prep = {"schema_version": 1,
            "artifact_kind": "NoFixedData-five-child-five-original-helper-successor-preparation",
            "validated": False, "proposal_status": "Draft", "submission_ready": False,
            "source_commit": "adc7f1241b42e322a6451854ab7e4b4c146bf78a",
            "original_41_line_NoFixedData_proof_only_two_name_replacements": True,
            "original_NoFixedData_comparator_sha256": sha(old.STAGE / old.NFD_FILE),
            "original_arithmetic_Open_wire_sha256": sha(old.STAGE / "arithmetic-source017-open-wire.lean"),
            "five_original_helper_commands": spans,
            "source_helper_namespace_context": ["namespace OAI", "namespace PiExponent",
                                                "namespace AdmissibleParameters",
                                                "variable {nu Lambda c : ℝ} (d : AdmissibleParameters nu Lambda c)"],
            "source_helper_names": SOURCE_NAMES,
            "source_snapshot_names": source_names, "source_snapshot_owners": source_owners,
            "generated_helper_names": SOURCE_NAMES,
            "generated_helper_owners": generated_helper_owners,
            "generated_open_names": generated_seven,
            "generated_open_owners": generated_seven_owners,
            "five_reused_actual_Open_child_emitters": emitters,
            "old_failed_solution_preimage": {"source": task_rel(FAILED_SOL),
                                             "source_sha256": sha(FAILED_SOL),
                                             "sidecar": task_rel(FAILED_SIDECAR),
                                             "sidecar_sha256": sha(FAILED_SIDECAR),
                                             "log": task_rel(failed_log), "log_sha256": sha(failed_log)},
            "new_solution_module": SOL_MODULE, "new_solution_sha256": digest(solution),
            "three_compiler_manifests": [row[0] for row in compile_order],
            "compile_commands": commands_to_run, "input_sha256": input_hashes,
            "file_sha256": {name: digest(raw) for name, raw in files.items()},
            "closed_helper_proofs_expected": True,
            "NoFixedData_graph_sketch_only": True,
            "Lean_started": False, "API_used": False}
    files["preparation.json"] = encode(prep)
    return files


def check(files=None):
    files = stages() if files is None else files
    for name, raw in files.items():
        path = STAGE / name
        need(path.is_file() and path.read_bytes() == raw, "Successor stage changed: " + str(path))
    return {"files": len(files), "new_preflights": 3, "reused_actual_child_emitters": 5,
            "source_helpers_inlined": 5, "Lean_started": False, "API_used": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--prepare", action="store_true")
    mode.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    files = stages()
    if args.prepare:
        for name, raw in files.items():
            path = STAGE / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(raw)
    print(json.dumps(check(files), ensure_ascii=False, sort_keys=True))


if __name__ == "__main__":
    main()
