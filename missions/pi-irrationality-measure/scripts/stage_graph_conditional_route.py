"""Pure source-exact candidate for the conditional pi lower-bound parent.

The original target is unchanged. Its proof uses the accepted source017 A1
name and awaits the genuine no_fixed_data theorem as an imported parent.
No mode runs Lean or contacts the platform.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
STAGE = TASK / "verification/graph-conditional-route-20261011"
SOURCE_ROOT = TASK / "verification/graph-source-root-20261011"
PORT = TASK / "port/lean/OAI/NumberTheory/PiExponent/Approximation/DeterminantContradiction.lean"
ORIGINAL = TASK / "source/lean/OAI/NumberTheory/PiExponent/Approximation/DeterminantContradiction.lean"
A1_RECORD = TASK / "verification/ap6/a1/source017f/publication-v3/publication.json"
ROOT_PREP = SOURCE_ROOT / "preparation.json"
TARGET = "OAI.PiExponent.DeterminantContradiction.piEventualLowerBound_of_interpolation_and_analytic_aggregate"
A1 = "OAI.PiExponent.exists_admissible_parameters_source017"
NO_FIXED = "OAI.PiExponent.DeterminantContradiction.no_fixed_data_of_interpolation_and_analytic_aggregate"
A1_MODULE = "Theorems.Thm_OAI_PiExponent_exists_admissible_parameters_source017"
NO_FIXED_CANDIDATE_MODULE = (
    "Theorems.Thm_OAI_PiExponent_DeterminantContradiction_"
    "no_fixed_data_of_interpolation_and_analytic_aggregate")
SELF = Path(__file__).resolve()
COMPARATOR = "Theorems/Thm_OAI_PiExponent_DeterminantContradiction_piEventualLowerBound_of_interpolation_and_analytic_aggregate.lean"
SOLUTION = "Solutions/Sol_OAI_PiExponent_DeterminantContradiction_piEventualLowerBound_conditional.lean"
ORIGINAL_COMMAND = "original-conditional-source-command.lean.txt"
NO_FIXED_COMMAND = "original-no-fixed-data-source-command.lean.txt"
PREP = "preparation.json"


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


def stage_files():
    root = read(ROOT_PREP)
    parent = next(item for item in root["parents"] if item["key"] == "conditional")
    need(parent["name"] == TARGET and parent["source_module"] ==
         "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction"
         and root["source_commit"] == "adc7f1241b42e322a6451854ab7e4b4c146bf78a",
         "Source-root conditional identity/commit differs")
    need(sha(PORT) == parent["source_sha256"]
         and sha(ORIGINAL) == parent["source_interface"]["original_sha256"],
         "Port/original source hashes differ")
    port = PORT.read_bytes()
    start, end = parent["range"]
    command = port[start:end]
    need(sha_bytes(command) == parent["unit_sha256"]
         and command == (SOURCE_ROOT / "source/OAI_PiExponent_DeterminantContradiction_piEventualLowerBound_of_interpolation_and_analytic_aggregate.lean.txt").read_bytes(),
         "Conditional theorem is not the exact AST source command")
    name = parent["source_interface"]["ast"]["nameRange"]
    begin, finish = name["start"]["offset"] - start, name["end"]["offset"] - start
    source_name = b"piEventualLowerBound_of_interpolation_and_analytic_aggregate"
    need(command[begin:finish] == source_name and command.count(source_name) == 1,
         "Conditional theorem AST name span differs")
    old_call = b"exists_admissible_parameters nu Arithmetic.lcmConstant"
    new_call = b"OAI.PiExponent.exists_admissible_parameters_source017 nu Arithmetic.lcmConstant"
    need(command.count(old_call) == 1
         and command.count(b"no_fixed_data_of_interpolation_and_analytic_aggregate") == 1,
         "Conditional source proof calls differ")
    renamed = command[:begin] + b"solution" + command[finish:]
    renamed = renamed.replace(old_call, new_call, 1)
    prefix = ("import Definitions.Def_OAI_PiExponent_ApproximationDefinitions\r\n"
              "import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData\r\n"
              "import " + A1_MODULE + "\r\n"
              "import " + NO_FIXED_CANDIDATE_MODULE + "\r\n\r\n"
              "open OAI.PiExponent OAI.PiExponent.DeterminantContradiction\r\n\r\n").encode()
    solution = prefix + b"theorem " + renamed[len(b"theorem "):].rstrip(b"\r\n") + b"\r\n"
    comparator = (SOURCE_ROOT / parent["file"]).read_bytes()
    need(comparator == (SOURCE_ROOT / "parents/conditional/wire-theorem-source.lean").read_bytes()
         and sha_bytes(comparator) == sha_bytes((SOURCE_ROOT / parent["file"]).read_bytes()),
         "Source-root target comparator differs")
    nf_start = port.index(b"theorem no_fixed_data_of_interpolation_and_analytic_aggregate")
    nf_end = port.index(b"\r\n\r\ntheorem piEventualLowerBound_of_interpolation_and_analytic_aggregate", nf_start)
    no_fixed = port[nf_start:nf_end]
    no_fixed_header = no_fixed[:no_fixed.index(b":= by")]
    need(b"(hgeometry : GlobalInterpolationStatement) (hanalytic : AnalyticAggregateStatement)" in no_fixed_header
         and b"(nu : \xe2\x84\x9d) (hnu : 2 < nu) (d : FixedData nu) : False" in no_fixed_header,
         "Genuine source no_fixed_data interface differs")
    a1_record = read(A1_RECORD)
    rb = a1_record["target_readback"]["body"]
    need(a1_record["confirmed_proved"] is True
         and a1_record["last_verify_verdict"]["body"]["status"] == "ACCEPTED"
         and rb["theorem_name"] == A1 and rb["status"] == "Proved"
         and rb["visibility"] == "public"
         and rb["theorem_id"] == "fdcbce8c-d9e6-43dd-8587-cfe865e6e78a",
         "A1 source017 parent is not actually own Accepted/Proved")
    files = {COMPARATOR: comparator, SOLUTION: solution,
             ORIGINAL_COMMAND: command, NO_FIXED_COMMAND: no_fixed}
    inputs = [SELF, ROOT_PREP, PORT, ORIGINAL, A1_RECORD,
              SOURCE_ROOT / parent["file"],
              SOURCE_ROOT / "source/OAI_PiExponent_DeterminantContradiction_piEventualLowerBound_of_interpolation_and_analytic_aggregate.lean.txt"]
    prep = {
        "schema_version": 1,
        "artifact_kind": "source-root-conditional-A1-to-NoFixedData-pure-route",
        "status": "candidate-awaiting-genuine-no-fixed-data-platform-parent-and-local-proved-imports",
        "validated": False, "proposal_status": "Draft", "submission_ready": False,
        "source_commit": root["source_commit"],
        "source_name": TARGET, "source_module": parent["source_module"],
        "source_lines": [167, 180], "source_ast": parent["source_interface"]["ast"],
        "source_scope": parent["source_interface"]["scope"],
        "source_command_sha256": sha_bytes(command),
        "source_proof_suffix_sha256": sha_bytes(command[parent["source_interface"]["ast"]["valueStart"]["offset"]-start:]),
        "only_source_proof_change": {"before": old_call.decode(), "after": new_call.decode(),
                                     "count": 1},
        "global_solution_name": "solution",
        "target_comparator": rel(STAGE / COMPARATOR),
        "target_comparator_sha256": sha_bytes(comparator),
        "candidate_solution": rel(STAGE / SOLUTION),
        "candidate_solution_sha256": sha_bytes(solution),
        "existing_accepted_A1": {"name": A1, "module": A1_MODULE,
                                 "theorem_id": rb["theorem_id"],
                                 "record": rel(A1_RECORD), "record_sha256": sha(A1_RECORD)},
        "genuine_missing_proof_parent": {"name": NO_FIXED,
                                          "candidate_module_not_yet_authoritative": NO_FIXED_CANDIDATE_MODULE,
                                          "source_lines": [125, 165],
                                          "source_command_sha256": sha_bytes(no_fixed),
                                          "exact_type_header_sha256": sha_bytes(no_fixed_header),
                                          "source_type_header": no_fixed_header.decode()},
        "planned_imports_not_yet_compilable": [
            "Definitions.Def_OAI_PiExponent_ApproximationDefinitions",
            "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData",
            A1_MODULE, NO_FIXED_CANDIDATE_MODULE],
        "binding_gates_before_Lean_or_submission": [
            "Publish/read back actual no_fixed_data Open theorem target using exact source type",
            "Bind its real platform name and module; replace candidate module if different",
            "Create/compile no-sorry local import for accepted A1; target stub alone carries sorryAx",
            "Create/compile actual imported no_fixed_data parent; Accepted/Proved required for Std3 child closure",
            "Compile the isolated candidate and compare source/target/global-solution kernel types",
        ],
        "input_sha256": {rel(path): sha(path) for path in inputs},
        "file_sha256": {name: sha_bytes(raw) for name, raw in files.items()},
        "Lean_started": False, "API_used": False,
    }
    files[PREP] = encode(prep)
    return files


def check(files=None):
    files = stage_files() if files is None else files
    for name, raw in files.items():
        path = STAGE / name
        need(path.is_file() and path.read_bytes() == raw,
             "Isolated conditional route differs: " + str(path))
    return {"files": len(files), "source_exact": True,
            "only_A1_call_renamed": True, "pending_no_fixed_data_parent": True,
            "validated": False, "Lean_started": False, "API_used": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--prepare", action="store_true")
    mode.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    files = stage_files()
    if args.prepare:
        for name, raw in files.items():
            path = STAGE / name
            if path.exists():
                need(path.read_bytes() == raw, "Refusing to overwrite candidate route")
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(raw)
    print(json.dumps(check(files), ensure_ascii=False))


if __name__ == "__main__":
    main()
