"""Stage the genuine NoFixedData Open node and conditional A1-reference sketch.

This is pure file preparation. Root runs all bounded Lean preflights and API
steps. A1 is represented by its exact platform wire for local reference/type
checking; its independent accepted closed proof is pinned separately.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import stage_graph_conditional_route as previous


TASK, ROOT = previous.TASK, previous.ROOT
STAGE = TASK / "verification/graph-conditional-route-20261011-v2"
SELF = Path(__file__).resolve()
ORIGINAL = previous.STAGE
SOURCE_ROOT = previous.SOURCE_ROOT
NO_FIXED_GET = TASK / "verification/determinant-core-exact-name-lookup-20261011T135109_614374Z.json"
CONDITIONAL_READBACK = SOURCE_ROOT / "publication-v2/parent-readbacks/conditional.json"
A1_WIRE = TASK / "verification/ap6/a1/source017f/publication-v3/wire-theorem-source.lean"
CORE = TASK / "verification/TypeOnlyTheoremSnapshotCore.inc"
RUNTIME = TASK / "verification/lean-runtime.json"
RUNNER = TASK / "scripts/preflight_staged_module.py"
ROOT_EXPORTER = SOURCE_ROOT / "SourceSnapshot.lean"
CONDITIONAL_MODULE = "Theorems.Thm_OAI_PiExponent_DeterminantContradiction_piEventualLowerBound_of_interpolation_and_analytic_aggregate"
NFD_MODULE = previous.NO_FIXED_CANDIDATE_MODULE
A1_MODULE = previous.A1_MODULE
SOLUTION_MODULE = "Solutions.Sol_OAI_PiExponent_DeterminantContradiction_piEventualLowerBound_conditional"
NFD_FILE = "Theorems/Thm_OAI_PiExponent_DeterminantContradiction_no_fixed_data_of_interpolation_and_analytic_aggregate.lean"
A1_FILE = "Theorems/Thm_OAI_PiExponent_exists_admissible_parameters_source017.lean"
SOLUTION_FILE = "Solutions/Sol_OAI_PiExponent_DeterminantContradiction_piEventualLowerBound_conditional.lean"
SOURCE_SNAPSHOT = "SourceSnapshot.lean"
GENERATED_SNAPSHOT = "GeneratedSnapshot.lean"
SOURCE_JSON = "source-types-and-refs.json"
GENERATED_JSON = "generated-types-and-refs.json"
PREP = "preparation.json"
DEF_IMPORTS = ["Definitions.Def_OAI_PiExponent_ApproximationDefinitions",
               "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData"]


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


def root_rel(path):
    return Path(path).resolve().relative_to(ROOT.resolve()).as_posix()


def root_stage_rel(path):
    return Path(path).resolve().relative_to((TASK / "verification").resolve()).as_posix()


def a1_and_target_status():
    a1 = read(previous.A1_RECORD)
    a1_body = a1["target_readback"]["body"]
    need(a1["confirmed_proved"] is True and a1["last_verify_verdict"]["body"]["status"] == "ACCEPTED"
         and a1_body["theorem_name"] == previous.A1 and a1_body["status"] == "Proved"
         and a1_body["theorem_id"] == "fdcbce8c-d9e6-43dd-8587-cfe865e6e78a",
         "Actual A1 theorem is not accepted/proved")
    conditional = read(CONDITIONAL_READBACK)
    need(conditional["theorem_name"] == previous.TARGET
         and conditional["theorem_id"] == "cbe4fb5f-2db8-4484-b209-ecb4e4efea9a"
         and conditional["status"] == "Open" and conditional["visibility"] == "public",
         "Original conditional Open target readback differs")
    lookup = read(NO_FIXED_GET)
    rows = [x for x in lookup["records"] if x["theorem_name"] == previous.NO_FIXED]
    need(len(rows) == 1 and rows[0]["http_status"] == 200 and rows[0]["matches"] == []
         and lookup["read_only"] is True and lookup["environment"] ==
             "0df444a360eaa60ab8c11dca51a86af692955474",
         "NoFixedData exact public name is not authoritatively free")
    return a1_body, conditional


def snapshot_exporter():
    raw = ROOT_EXPORTER.read_text(encoding="utf-8")
    start = raw.index("open Lean Meta")
    end = raw.index("run_meta do", start)
    return raw[start:end]


def stages():
    previous.check()
    a1_body, conditional_body = a1_and_target_status()
    original_no_fixed = (ORIGINAL / previous.NO_FIXED_COMMAND).read_bytes()
    head, marker, proof = original_no_fixed.partition(b":= by")
    need(marker == b":= by" and proof and head.count(b"theorem no_fixed_data_of_interpolation_and_analytic_aggregate") == 1,
         "Genuine no-fixed-data source theorem boundary differs")
    original_name = b"theorem no_fixed_data_of_interpolation_and_analytic_aggregate"
    qualified_name = ("theorem " + previous.NO_FIXED).encode()
    formal = head.replace(original_name, qualified_name, 1) + b":= by\r\n  sorry\r\n"
    preamble = (SOURCE_ROOT / "parents/conditional/wire-theorem-source.lean").read_bytes().split(b"theorem ", 1)[0]
    need(preamble == ("import " + DEF_IMPORTS[0] + "\nimport " + DEF_IMPORTS[1] +
                      "\n\nopen OAI.PiExponent OAI.PiExponent.DeterminantContradiction\n\n").encode(),
         "Canonical/source Definition preamble differs")
    no_fixed_wire = preamble + formal
    need(b"sorry" in formal and b"import OAI." not in preamble
         and previous.NO_FIXED.encode() in formal,
         "NoFixedData Open comparator is not standalone and exact-name")
    a1_wire = A1_WIRE.read_bytes()
    need((a1_body["preamble"] + a1_body["formal_statement"]).encode() == a1_wire,
         "Local A1 stub differs from actually Accepted platform theorem wire")
    solution = (ORIGINAL / previous.SOLUTION).read_bytes()
    need(solution.count(previous.A1.encode()) == 1
         and solution.count(b"no_fixed_data_of_interpolation_and_analytic_aggregate") == 2
         and solution.count(b"theorem solution") == 1
         and b"sorry" not in solution,
         "Conditional candidate proof is not the exact one-A1-name source route")
    # Verify the target statement is exactly the already published original one.
    original_target = (ORIGINAL / previous.COMPARATOR).read_bytes()
    need((conditional_body["preamble"] + conditional_body["formal_statement"]).encode() == original_target,
         "Conditional source comparator differs from its public Open target")

    exporter = snapshot_exporter()
    source_names = ["OAI.PiExponent.exists_admissible_parameters", previous.NO_FIXED, previous.TARGET]
    source_owners = ["OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
                     "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
                     "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction"]
    generated_names = [previous.A1, previous.NO_FIXED, previous.TARGET, "solution"]
    generated_owners = [A1_MODULE, NFD_MODULE, CONDITIONAL_MODULE, SOLUTION_MODULE]

    def rows_call(names, owners, output, open_targets):
        qnames = ", ".join("`" + n for n in names)
        qowners = ", ".join(json.dumps(n) for n in owners)
        return ("run_meta do\n  SourceRootGraphSnapshot.exportRows #[" + qnames +
                "] #[" + qowners + "] \"" + root_rel(STAGE / output) +
                "\" " + ("true" if open_targets else "false") + "\n\n" +
                "".join("#print axioms " + n + "\n" for n in names))

    source_snapshot = ("import Lean\nimport OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction\n\n" +
                       exporter + rows_call(source_names, source_owners, SOURCE_JSON, False)).encode()
    generated_imports = ["Lean", *DEF_IMPORTS, A1_MODULE, NFD_MODULE,
                         CONDITIONAL_MODULE, SOLUTION_MODULE]
    generated_snapshot = ("".join("import " + imp + "\n" for imp in generated_imports) + "\n" +
                          exporter + rows_call(generated_names, generated_owners, GENERATED_JSON, True)).encode()
    files = {NFD_FILE: no_fixed_wire, A1_FILE: a1_wire, SOLUTION_FILE: solution,
             SOURCE_SNAPSHOT: source_snapshot, GENERATED_SNAPSHOT: generated_snapshot,
             "conditional-published-wire.lean": original_target,
             "original-no-fixed-data-command.lean.txt": original_no_fixed}
    imports = {NFD_FILE: DEF_IMPORTS,
               A1_FILE: ["Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_AdmissibleParameters", "Mathlib"],
               SOLUTION_FILE: [*DEF_IMPORTS, A1_MODULE, NFD_MODULE],
               SOURCE_SNAPSHOT: ["Lean", "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction"],
               GENERATED_SNAPSHOT: generated_imports}
    order = [("c1.json", NFD_FILE, "emit-olean"),
             ("c2.json", A1_FILE, "emit-olean"),
             ("c3.json", SOLUTION_FILE, "emit-olean"),
             ("c4.json", SOURCE_SNAPSHOT, "modecheck"),
             ("c5.json", GENERATED_SNAPSHOT, "modecheck")]
    input_paths = [SELF, Path(previous.__file__), previous.STAGE / previous.PREP,
                   previous.STAGE / previous.NO_FIXED_COMMAND,
                   previous.STAGE / previous.SOLUTION, ROOT_EXPORTER,
                   SOURCE_ROOT / "parents/conditional/wire-theorem-source.lean",
                   SOURCE_ROOT / "actual-source-root-graph-validation.json",
                   SOURCE_ROOT / "publication-v2/parent-readbacks/conditional.json",
                   previous.A1_RECORD, A1_WIRE, NO_FIXED_GET, previous.PORT,
                   previous.ORIGINAL, CORE, RUNNER, RUNTIME]
    input_hashes = {rel(path): sha(path) for path in input_paths}
    manifests = {}
    commands = {}
    for manifest_name, filename, mode in order:
        doc = {
            "schema_version": 1,
            "artifact_kind": "graph-conditional-open-chain-bounded-compiler-manifest",
            "output": root_rel(STAGE / filename), "output_sha256": sha_bytes(files[filename]),
            "imports": imports[filename], "input_hashes": input_hashes,
            "runtime_sha256": sha(RUNTIME), "mode": mode,
            "emit_olean": mode == "emit-olean", "timeout_seconds": 300,
            "validated": False, "submission_ready": False,
        }
        manifests[manifest_name] = doc
        files[manifest_name] = encode(doc)
        commands[manifest_name] = ("python scripts/preflight_staged_module.py " +
            root_stage_rel(STAGE / filename) + " --root graph-conditional-route-20261011-v2" +
            " --imports-manifest " + root_stage_rel(STAGE / manifest_name) +
            " --timeout-seconds 300")
    prep = {
        "schema_version": 1,
        "artifact_kind": "graph-conditional-open-NoFixedData-A1-reference-sketch-preparation",
        "validated": False, "proposal_status": "Draft", "submission_ready": False,
        "source_commit": "adc7f1241b42e322a6451854ab7e4b4c146bf78a",
        "NoFixedData": {"name": previous.NO_FIXED, "source_lines": [125, 165],
                        "source_command_sha256": sha_bytes(original_no_fixed),
                        "preamble": preamble.decode(), "formal_statement": formal.decode(),
                        "complete_compiled_wire_sha256": sha_bytes(no_fixed_wire),
                        "status": "Open target candidate; actual Lean type check and upload pending"},
        "A1_reference": {"name": previous.A1, "platform_theorem_id": a1_body["theorem_id"],
                         "actual_platform_status": "ACCEPTED_AND_PROVED",
                         "local_stub_only_for_type_and_reference_resolution": True,
                         "local_stub_contains_sorryAx": True,
                         "platform_record": rel(previous.A1_RECORD),
                         "platform_record_sha256": sha(previous.A1_RECORD)},
        "conditional": {"name": previous.TARGET,
                        "platform_theorem_id": conditional_body["theorem_id"],
                        "platform_status": "Open", "published_comparator_sha256": sha_bytes(original_target),
                        "original_AST_sha256": sha(previous.STAGE / previous.ORIGINAL_COMMAND),
                        "candidate_solution_sha256": sha_bytes(solution),
                        "single_original_proof_edit": read(previous.STAGE / previous.PREP)["only_source_proof_change"]},
        "source_snapshot_names": source_names,
        "generated_snapshot_names": generated_names,
        "source_snapshot_expected_axioms": "Std3 only for three actual original source proofs",
        "generated_snapshot_expected_axioms": "sorryAx present in four local Open/type sketches; A1 platform Proved is separate evidence",
        "theorem_values_exported": False,
        "ordered_compiler_manifests": [x[0] for x in order],
        "compile_commands": commands,
        "input_sha256": input_hashes,
        "file_sha256": {name: sha_bytes(raw) for name, raw in files.items()},
        "NoFixedData_exact_name_lookup": rel(NO_FIXED_GET),
        "NoFixedData_exact_name_lookup_sha256": sha(NO_FIXED_GET),
        "Lean_started": False, "API_used": False,
    }
    files[PREP] = encode(prep)
    return files


def check(files=None):
    files = stages() if files is None else files
    for name, raw in files.items():
        path = STAGE / name
        need(path.is_file() and path.read_bytes() == raw,
             "Isolated conditional Open-chain stage differs: " + str(path))
    return {"files": len(files), "NoFixedData_original_name_free": True,
            "A1_platform_Proved_local_stub_only": True,
            "conditional_original_proof_single_A1_name_change": True,
            "compiler_commands": read(STAGE / PREP)["compile_commands"],
            "validated": False, "Lean_started": False, "API_used": False}


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
            if path.exists():
                need(path.read_bytes() == raw, "Refusing to overwrite isolated Open-chain stage")
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(raw)
    print(json.dumps(check(files), ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
