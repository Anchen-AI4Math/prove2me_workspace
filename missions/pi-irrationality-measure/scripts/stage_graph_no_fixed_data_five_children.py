"""Pure staging of the genuine NoFixedData proof against five public child interfaces.

All local child modules are type-only Open stubs. This script neither runs Lean
nor accesses the API. The original proof has exactly two identifier edits.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import stage_graph_conditional_open_chain as prior


TASK, ROOT = prior.TASK, prior.ROOT
STAGE = TASK / "verification/graph-no-fixed-data-route-20261011"
SELF = Path(__file__).resolve()
PORT = prior.previous.PORT
ORIGINAL = prior.previous.ORIGINAL
V2 = prior.STAGE
NFD = prior.previous.NO_FIXED
CORE = TASK / "verification/TypeOnlyTheoremSnapshotCore.inc"
RUNTIME = TASK / "verification/lean-runtime.json"
RUNNER = TASK / "scripts/preflight_staged_module.py"
EXPORTER = V2 / "SourceSnapshot.lean"
SOURCE_MODULE = "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction"
NFD_MODULE = prior.NFD_MODULE
SOL_MODULE = "Solutions.Sol_OAI_PiExponent_DeterminantContradiction_no_fixed_data_five_children"
DEF_IMPORTS = prior.DEF_IMPORTS
CHILDREN = [
    ("collision", "OAI.PiExponent.DeterminantContradiction.tendsto_collisionRate_source017",
     "OAI.PiExponent.DeterminantContradiction.tendsto_collisionRate",
     "Theorems.Thm_OAI_PiExponent_DeterminantContradiction_tendsto_collisionRate_source017",
     TASK / "verification/ap11/collision-rate-source017/publication/publication.json", "Proved"),
    ("minor", "OAI.PiExponent.InterpolationMatrix.exists_full_row_minor_of_surjective",
     "OAI.PiExponent.InterpolationMatrix.exists_full_row_minor_of_surjective",
     "Theorems.Thm_OAI_PiExponent_InterpolationMatrix_exists_full_row_minor_of_surjective",
     TASK / "verification/ap8/minor/publication/publication.json", "Proved"),
    ("comparison", "OAI.PiExponent.determinant_bounds_inconsistent",
     "OAI.PiExponent.determinant_bounds_inconsistent",
     "Theorems.Thm_OAI_PiExponent_determinant_bounds_inconsistent",
     TASK / "verification/ap7/determinant-bounds-global-v2/publication-v3/publication.json", "Proved"),
    ("mean", "OAI.PiExponent.DeterminantContradiction.actualMean_bounds",
     "OAI.PiExponent.DeterminantContradiction.actualMean_bounds",
     "Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actualMean_bounds",
     TASK / "verification/ap12/mean-bounds/publication-v2/publication.json", "Open"),
]
ARITH = "OAI.PiExponent.DeterminantContradiction.actual_minor_arithmetic_lower_bound_source017"
ARITH_SOURCE = "OAI.PiExponent.DeterminantContradiction.actual_minor_arithmetic_lower_bound"
ARITH_MODULE = "Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actual_minor_arithmetic_lower_bound_source017"
NFD_FILE = "no-fixed-data-published-comparator.lean"
SOL_FILE = "Solutions/Sol_OAI_PiExponent_DeterminantContradiction_no_fixed_data_five_children.lean"
SOURCE_JSON = "source-six-types-and-refs.json"
GENERATED_JSON = "generated-seven-types-and-refs.json"


def require(value, message):
    if not value:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def sha(path):
    return digest(Path(path).read_bytes())


def read(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def encoded(obj):
    return (json.dumps(obj, ensure_ascii=False, indent=2) + "\n").encode("utf-8")


def task_rel(path):
    return path.resolve().relative_to(TASK.resolve()).as_posix()


def root_rel(path):
    return path.resolve().relative_to(ROOT.resolve()).as_posix()


def verification_rel(path):
    return path.resolve().relative_to((TASK / "verification").resolve()).as_posix()


def original_arithmetic_command():
    raw = PORT.read_bytes()
    start = raw.index(b"theorem actual_minor_arithmetic_lower_bound ")
    end = raw.index(b"\ntheorem actualMean_bounds ", start)
    result = raw[start:end].rstrip(b"\r\n") + b"\n"
    require(result.count(b"theorem actual_minor_arithmetic_lower_bound ") == 1 and
            result.count(b":= by") == 1, "Original arithmetic AST boundary differs")
    return result


def public_child(label, name, path, expected_status, readback_path=None):
    record = read(readback_path or path)
    body = record["target_readback"]["body"]
    require(record["theorem_name"] == name and body["theorem_name"] == name and
            body["status"] == expected_status and body["visibility"] == "public" and
            body["mathlib_rev"] == "0df444a360eaa60ab8c11dca51a86af692955474",
            f"{label} public readback changed")
    if expected_status == "Proved":
        require(record["confirmed_proved"] is True and
                record["last_verify_verdict"]["body"]["status"] == "ACCEPTED",
                f"{label} is not actually Accepted/Proved")
    else:
        require(record.get("confirmed_proved") is not True, f"{label} status must be revisited")
    wire = (body["preamble"] + body["formal_statement"]).encode("utf-8")
    require(wire == (path.parent / "wire-theorem-source.lean").read_bytes(),
            f"{label} saved wire differs from platform readback")
    used_path = readback_path or path
    return wire, {"name": name, "theorem_id": body["theorem_id"],
                  "status_at_staging": body["status"], "record": task_rel(used_path),
                  "record_sha256": sha(used_path), "exact_wire_sha256": digest(wire),
                  "local_stub_sorryAx": True,
                  "platform_proved_at_staging": expected_status == "Proved"}


def snapshot_body(names, owners, output, open_targets):
    exporter = EXPORTER.read_text(encoding="utf-8")
    body = exporter[exporter.index("open Lean Meta"):exporter.index("run_meta do")]
    require("namespace SourceRootGraphSnapshot" in body and "def exportRows" in body and "valueRefs" in body and
            "actualOwner" in body and "closedValue" in body, "Snapshot exporter contract differs")
    qnames = ", ".join("`" + n for n in names)
    qowners = ", ".join(json.dumps(n) for n in owners)
    tail = ("run_meta do\n  SourceRootGraphSnapshot.exportRows #[" + qnames +
            "] #[" + qowners + "] \"" + root_rel(STAGE / output) + "\" " +
            ("true" if open_targets else "false") + "\n\n" +
            "".join("#print axioms " + n + "\n" for n in names))
    return body + tail


def stages():
    prior.check()
    source_nfd = (V2 / "original-no-fixed-data-command.lean.txt").read_bytes()
    comparator = (V2 / "Theorems/Thm_OAI_PiExponent_DeterminantContradiction_no_fixed_data_of_interpolation_and_analytic_aggregate.lean").read_bytes()
    require(sha(PORT) == "74329150cc64ac655ee0ce56454519170ce15b4b58dfd85ba5a9ab850c740e53" and
            sha(ORIGINAL) == "b9c6643a0b8eb48868d597c1e4a613ec2f1da5d49cedc3484c67b3ca057a8130",
            "Source/port provenance changed")
    require(digest(source_nfd) == read(V2 / "preparation.json")["NoFixedData"]["source_command_sha256"],
            "NoFixedData original source command changed")
    require(comparator == (read(V2 / "preparation.json")["NoFixedData"]["preamble"] +
                           read(V2 / "preparation.json")["NoFixedData"]["formal_statement"]).encode(),
            "NoFixedData target comparator differs from v2")
    head, sep, proof = source_nfd.partition(b":= by")
    require(sep == b":= by" and proof and
            head.count(b"theorem no_fixed_data_of_interpolation_and_analytic_aggregate") == 1,
            "NoFixedData source theorem AST differs")
    patched = proof
    edits = [(b"(tendsto_collisionRate d).sub", b"(tendsto_collisionRate_source017 d).sub"),
             (b"have hlower := actual_minor_arithmetic_lower_bound d H hH selection hdet'",
              b"have hlower := actual_minor_arithmetic_lower_bound_source017 d H hH selection hdet'")]
    for before, after in edits:
        require(patched.count(before) == 1, "Expected precisely one original proof reference: " + before.decode())
        patched = patched.replace(before, after, 1)
    restored = patched
    for before, after in edits:
        require(restored.count(after) == 1, "Generated proof name count differs")
        restored = restored.replace(after, before, 1)
    require(restored == proof, "Generated proof is not the two-name exact original proof")
    sol_head = head.replace(b"theorem no_fixed_data_of_interpolation_and_analytic_aggregate",
                            b"theorem solution", 1)
    source_names = [NFD, "OAI.PiExponent.DeterminantContradiction.tendsto_collisionRate",
                    "OAI.PiExponent.InterpolationMatrix.exists_full_row_minor_of_surjective",
                    "OAI.PiExponent.determinant_bounds_inconsistent",
                    "OAI.PiExponent.DeterminantContradiction.actualMean_bounds", ARITH_SOURCE]
    source_owners = [SOURCE_MODULE, SOURCE_MODULE,
                     "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
                     "OAI.NumberTheory.PiExponent.Approximation.Comparison", SOURCE_MODULE, SOURCE_MODULE]
    generated_names = [NFD, *[c[1] for c in CHILDREN], ARITH, "solution"]
    generated_owners = [NFD_MODULE, *[c[3] for c in CHILDREN], ARITH_MODULE, SOL_MODULE]
    files = {NFD_FILE: comparator, "original-no-fixed-data-command.lean.txt": source_nfd}
    public = {}
    child_modules = []
    for label, name, _source_name, module, record, status in CHILDREN:
        saved_record = STAGE / "saved-public-record/mean-open-at-staging.json"
        if label == "mean":
            record_bytes = saved_record.read_bytes() if saved_record.is_file() else record.read_bytes()
            files["saved-public-record/mean-open-at-staging.json"] = record_bytes
            source_record = saved_record if saved_record.is_file() else record
        else:
            source_record = record
        wire, evidence = public_child(label, name, record, status, source_record)
        if label == "mean":
            evidence["record"] = task_rel(saved_record)
            evidence["record_sha256"] = digest(record_bytes)
        file = module.replace(".", "/") + ".lean"
        files[file] = wire
        files[f"saved-public-wire/{label}.lean"] = wire
        public[label] = evidence
        child_modules.append(module)
    arith_command = original_arithmetic_command()
    files["original-arithmetic-command.lean.txt"] = arith_command
    arith_head, sep, arith_proof = arith_command.partition(b":= by")
    require(sep == b":= by" and arith_proof, "Arithmetic original theorem AST differs")
    local_head = arith_head.replace(b"theorem actual_minor_arithmetic_lower_bound",
                                    ("theorem " + ARITH).encode(), 1)
    arith_wire = comparator.split(b"theorem ", 1)[0] + local_head + b":= by\n  sorry\n"
    files[ARITH_MODULE.replace(".", "/") + ".lean"] = arith_wire
    files["arithmetic-source017-open-wire.lean"] = arith_wire
    solution_imports = ["Mathlib.Tactic", *DEF_IMPORTS, *child_modules, ARITH_MODULE]
    files[SOL_FILE] = ("".join("import " + x + "\n" for x in solution_imports) +
                       "\nopen OAI.PiExponent OAI.PiExponent.DeterminantContradiction\nopen Filter\nopen scoped Topology\n\n").encode() + sol_head + sep + patched
    require(b"sorry" not in files[SOL_FILE] and files[SOL_FILE].count(b"theorem solution") == 1,
            "Global solution must contain full original proof and no own sorry")
    source_imports = ["Lean", SOURCE_MODULE,
                      "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
                      "OAI.NumberTheory.PiExponent.Approximation.Comparison"]
    files["SourceSnapshot.lean"] = ("".join("import " + x + "\n" for x in source_imports) + "\n" +
                                    snapshot_body(source_names, source_owners, SOURCE_JSON, False)).encode()
    generated_imports = ["Lean", *DEF_IMPORTS, NFD_MODULE, *child_modules, ARITH_MODULE, SOL_MODULE]
    files["GeneratedSnapshot.lean"] = ("".join("import " + x + "\n" for x in generated_imports) + "\n" +
                                       snapshot_body(generated_names, generated_owners, GENERATED_JSON, True)).encode()
    lookup = TASK / "verification/determinant-core-exact-name-lookup-20261011T135109_614374Z.json"
    matches = [r for r in read(lookup)["records"] if r["theorem_name"] == ARITH]
    require(len(matches) == 1 and matches[0]["matches"] == [] and matches[0]["http_status"] == 200,
            "Arithmetic source017 exact-name lookup differs")
    input_paths = [SELF, PORT, ORIGINAL, V2 / "preparation.json",
                   V2 / "original-no-fixed-data-command.lean.txt",
                   V2 / "Theorems/Thm_OAI_PiExponent_DeterminantContradiction_no_fixed_data_of_interpolation_and_analytic_aggregate.lean",
                   EXPORTER, CORE, RUNTIME, RUNNER, lookup, *[c[4] for c in CHILDREN if c[0] != "mean"],
                   *[c[4].parent / "wire-theorem-source.lean" for c in CHILDREN]]
    input_hashes = {task_rel(p): sha(p) for p in input_paths}
    input_hashes[task_rel(STAGE / "saved-public-record/mean-open-at-staging.json")] = digest(
        files["saved-public-record/mean-open-at-staging.json"])
    compile_order = []
    for i, (label, name, _source_name, module, record, status) in enumerate(CHILDREN, 1):
        compile_order.append((f"c{i}.json", module.replace(".", "/") + ".lean", "emit-olean"))
    compile_order += [("c5.json", ARITH_MODULE.replace(".", "/") + ".lean", "emit-olean"),
                      ("c6.json", SOL_FILE, "emit-olean"),
                      ("c7.json", "SourceSnapshot.lean", "modecheck"),
                      ("c8.json", "GeneratedSnapshot.lean", "modecheck")]
    commands = {}
    for manifest_name, filename, mode in compile_order:
        import_list = [line[len("import "):] for line in files[filename].decode().splitlines()
                       if line.startswith("import ")]
        manifest = {"schema_version": 1,
                    "artifact_kind": "no-fixed-data-five-child-interface-preflight",
                    "output": root_rel(STAGE / filename), "output_sha256": digest(files[filename]),
                    "imports": import_list, "input_hashes": input_hashes,
                    "runtime_sha256": sha(RUNTIME), "mode": mode,
                    "emit_olean": mode == "emit-olean", "timeout_seconds": 300,
                    "validated": False, "submission_ready": False}
        files[manifest_name] = encoded(manifest)
        commands[manifest_name] = ("python scripts/preflight_staged_module.py " +
                                   verification_rel(STAGE / filename) +
                                   " --root graph-no-fixed-data-route-20261011 --imports-manifest " +
                                   verification_rel(STAGE / manifest_name) +
                                   " --timeout-seconds 300" +
                                   (" --emit-olean" if mode == "emit-olean" else ""))
    prep = {"schema_version": 1, "artifact_kind": "NoFixedData-five-children-open-graph-sketch",
            "validated": False, "proposal_status": "Draft", "submission_ready": False,
            "source_commit": "adc7f1241b42e322a6451854ab7e4b4c146bf78a",
            "mathlib_rev": "0df444a360eaa60ab8c11dca51a86af692955474",
            "NoFixedData": {"name": NFD, "source_lines": [125, 165],
                            "original_source_command_sha256": digest(source_nfd),
                            "same_comparator_as_frozen_v2_sha256": digest(comparator),
                            "existing_v2_olean_is_compile_dependency": True},
            "original_arithmetic": {"name": ARITH_SOURCE, "source_lines": [74, 85],
                                    "source_command_sha256": digest(arith_command),
                                    "source017_open_comparator_name": ARITH,
                                    "source017_open_wire_sha256": digest(arith_wire),
                                    "exact_name_lookup": task_rel(lookup), "exact_name_lookup_sha256": sha(lookup)},
            "source_proof_changes": [{"before": a.decode(), "after": b.decode(), "count": 1}
                                     for a, b in edits],
            "global_solution_own_sorry": False,
            "global_solution_dependency_sorryAx": True,
            "public_children_at_staging": public,
            "mean_proved_confirmation_late_bound": True,
            "arithmetic_source017_open_only": True,
            "source_snapshot_names": source_names, "source_snapshot_owners": source_owners,
            "generated_snapshot_names": generated_names, "generated_snapshot_owners": generated_owners,
            "source_snapshot_expected_axioms": "Std3 for all six original source theorem CIs",
            "generated_snapshot_expected_axioms": "sorryAx for NoFixedData, five local stubs, and global sketch; never claim closed platform proof from stubs",
            "theorem_values_exported": False,
            "ordered_compiler_manifests": [r[0] for r in compile_order],
            "compile_commands": commands, "input_sha256": input_hashes,
            "file_sha256": {name: digest(raw) for name, raw in files.items()},
            "Lean_started": False, "API_used": False}
    files["preparation.json"] = encoded(prep)
    return files


def check(files=None):
    files = stages() if files is None else files
    for name, raw in files.items():
        path = STAGE / name
        require(path.is_file() and path.read_bytes() == raw, "Stage changed: " + str(path))
    return {"files": len(files), "pure": True, "validated": False,
            "mean_proved_confirmation_late_bound": True,
            "arithmetic_open": True, "Lean_started": False, "API_used": False}


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
