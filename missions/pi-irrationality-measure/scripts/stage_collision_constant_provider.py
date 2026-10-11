"""Pure staging for the two-declaration collisionConstant Definition provider."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import preflight_staged_module as runner


TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
V = TASK / "verification"
STAGE = V / "ap7/collision-constant"
SOURCE = TASK / "port/lean/OAI/NumberTheory/PiExponent/Approximation/DeterminantContradiction.lean"
QUEUE = V / "ap7/determinant-contradiction-next-node-queue.json"
UNITS = V / "ast-unit-inventory.json"
SCOPES = V / "ast-scope-inventory.json"
GRAPH = V / "decl_graph.jsonl"
OWNERS = V / "shared-source-snapshot/complete-source/CompleteSource875.owners.json"
CORE = V / "StructuralKernelSnapshotCore.inc"
RUNTIME = V / "lean-runtime.json"
PREFLIGHT = TASK / "scripts/preflight_staged_module.py"
CONTEXT = TASK / "scripts/validate_namespace_context_providers.py"
PRODUCER = Path(__file__).resolve()
CONSUMER = TASK / "scripts/certify_collision_constant_provider_existing.py"

COMMIT = "adc7f1241b42e322a6451854ab7e4b4c146bf78a"
SOURCE_SHA256 = "74329150cc64ac655ee0ce56454519170ce15b4b58dfd85ba5a9ab850c740e53"
SOURCE_MODULE = "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction"
PLATFORM_MODULE = (
    "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_"
    "DeterminantContradiction_CollisionConstant"
)
PROVIDER_FILE = "Definitions/Def_OAI_NumberTheory_PiExponent_Approximation_" \
                "DeterminantContradiction_CollisionConstant.lean"
NAMES = [
    "OAI.PiExponent.DeterminantContradiction.collisionConstant",
    "OAI.PiExponent.DeterminantContradiction.collisionConstant_pos",
]
UNIT_SPECS = [
    {"name": NAMES[0], "kind": "def", "start": 463, "end": 522,
     "lines": [15, 15], "owner_kind": "definition",
     "command_unit": SOURCE_MODULE + ":463",
     "row_sha256": "dd1f0febdc04faccd4b5e374f91928f327ce4a31bbeeebe0c7fb60c41e15115e"},
    {"name": NAMES[1], "kind": "theorem", "start": 526, "end": 673,
     "lines": [17, 19], "owner_kind": "inline",
     "command_unit": SOURCE_MODULE + ":526",
     "row_sha256": "e438b1c64aecbfe969ddb1c29774204c1f6c172f81011488e6e24e9ca4641dae"},
]
DECL_GRAPH_SHA256 = "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4"


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def sha_bytes(raw):
    return hashlib.sha256(raw).hexdigest()


def read(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def encode(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode("utf-8")


def task_rel(path):
    return Path(path).resolve().relative_to(TASK.resolve()).as_posix()


def workspace_rel(path):
    return Path(path).resolve().relative_to(ROOT.resolve()).as_posix()


def need(condition, message):
    if not condition:
        raise ValueError(message)


def dictionaries(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from dictionaries(child)
    elif isinstance(value, list):
        for child in value:
            yield from dictionaries(child)


def exact_source_evidence():
    raw = SOURCE.read_bytes()
    need(sha_bytes(raw) == SOURCE_SHA256, "DeterminantContradiction source hash differs")
    expected_text = [
        b"noncomputable def collisionConstant : \xe2\x84\x9d := Real.log 2 / 4",
        (b"theorem collisionConstant_pos : 0 < collisionConstant := by\r\n"
         b"  unfold collisionConstant\r\n"
         b"  exact div_pos (Real.log_pos (by norm_num)) (by norm_num)"),
    ]
    extracted = []
    for spec, expected in zip(UNIT_SPECS, expected_text):
        unit = raw[spec["start"]:spec["end"]]
        need(unit == expected, "Exact source AST bytes differ: " + spec["name"])
        extracted.append(unit)

    queue = read(QUEUE)
    recommendation = queue["immediate_recommendation"]
    need(recommendation["source_commit"] == COMMIT
         and recommendation["source_sha256"] == SOURCE_SHA256
         and recommendation["source_module"] == SOURCE_MODULE,
         "Targeted ap7 queue provenance differs")
    for spec, queued in zip(UNIT_SPECS, recommendation["units"]):
        need(queued["source_name"] == spec["name"]
             and queued["kind"] == spec["kind"]
             and queued["source_lines"] == spec["lines"]
             and queued["ast_start_byte"] == spec["start"]
             and queued["ast_end_byte_exclusive"] == spec["end"]
             and queued["exact_source"].encode("utf-8") == extracted[UNIT_SPECS.index(spec)].replace(b"\r\n", b"\n"),
             "Targeted queue AST unit differs: " + spec["name"])

    unit_module = next((row for row in dictionaries(read(UNITS))
                        if row.get("module") == SOURCE_MODULE and isinstance(row.get("units"), list)), None)
    need(unit_module is not None and unit_module.get("source_sha256") == SOURCE_SHA256,
         "AST unit inventory module/source binding differs")
    unit_rows = {row.get("graph_names", [None])[0]: row for row in unit_module["units"]
                 if row.get("graph_names") and row["graph_names"][0] in NAMES}
    for spec in UNIT_SPECS:
        row = unit_rows.get(spec["name"])
        need(row is not None and row["start"]["offset"] == spec["start"]
             and row["end"]["offset"] == spec["end"]
             and row["graph_kinds"] == [spec["kind"]]
             and row["is_instance_command"] is False and row["is_local_instance"] is False
             and row["privateTok"] is None,
             "AST unit inventory differs: " + spec["name"])

    scope_source = next((row for row in dictionaries(read(SCOPES))
                         if row.get("source") ==
                         "OAI/NumberTheory/PiExponent/Approximation/DeterminantContradiction.lean"
                         and isinstance(row.get("declarations"), list)), None)
    need(scope_source is not None and scope_source.get("source_sha256") == SOURCE_SHA256,
         "AST scope inventory source binding differs")
    scope_rows = {row.get("verified_name"): row for row in scope_source["declarations"]
                  if row.get("verified_name") in NAMES}
    for spec in UNIT_SPECS:
        row = scope_rows.get(spec["name"])
        need(row is not None and row["namespace"] == "OAI.PiExponent.DeterminantContradiction"
             and [item["name"] for item in row["scope_stack"]]
                 == ["OAI", "PiExponent", "DeterminantContradiction"]
             and [item["syntaxKind"] for item in row["context_commands"]]
                 == ["Lean.Parser.Command.open", "Lean.Parser.Command.open"],
             "AST namespace/context differs: " + spec["name"])

    owner_rows = {row["source_name"]: row for row in read(OWNERS)["owners"]
                  if row.get("source_name") in NAMES}
    need(set(owner_rows) == set(NAMES), "Complete owner catalog lacks collisionConstant units")
    for spec in UNIT_SPECS:
        row = owner_rows[spec["name"]]
        need(row["source_module"] == SOURCE_MODULE
             and row["source_sha256"] == SOURCE_SHA256
             and row["command_unit"] == spec["command_unit"]
             and row["owner_kind"] == spec["owner_kind"]
             and row["owner_id"] == spec["command_unit"]
             and row["graph_kind"] == spec["kind"]
             and row["unit_start_offset"] == spec["start"]
             and row["unit_end_offset"] == spec["end"]
             and row["decl_graph_sha256"] == DECL_GRAPH_SHA256
             and row["decl_graph_row_sha256"] == spec["row_sha256"]
             and row["source_private"] is False,
             "Complete owner row differs: " + spec["name"])

    graph_rows = {}
    for line in GRAPH.read_text(encoding="utf-8").splitlines():
        row = json.loads(line)
        if row.get("name") in NAMES:
            graph_rows[row["name"]] = row
    need(graph_rows[NAMES[0]]["typeDeps"] == [] and graph_rows[NAMES[0]]["valueDeps"] == [],
         "collisionConstant graph dependencies are no longer empty")
    need(graph_rows[NAMES[1]]["typeDeps"] == [NAMES[0]]
         and graph_rows[NAMES[1]]["valueDeps"] == [NAMES[0]],
         "collisionConstant_pos graph closure differs")
    return extracted, owner_rows


def request_text(owner, expected_module):
    return (
        "    { sourceName := " + json.dumps(owner["source_name"])
        + ", expectedPublicName := " + json.dumps(owner["source_name"])
        + ", expectedModule := " + json.dumps(expected_module)
        + ", graphKind := " + json.dumps(owner["graph_kind"])
        + ", declGraphSha256 := " + json.dumps(owner["decl_graph_sha256"])
        + ", declGraphRowSha256 := " + json.dumps(owner["decl_graph_row_sha256"])
        + ", ownerKind := " + json.dumps(owner["owner_kind"])
        + ", ownerId := " + json.dumps(owner["owner_id"])
        + ", commandUnit := " + json.dumps(owner["command_unit"])
        + ", familyRoot := " + json.dumps(owner["source_name"]) + " }"
    )


def snapshot_text(import_module, expected_module, output, owner_rows):
    requests = ",\n".join(request_text(owner_rows[name], expected_module) for name in NAMES)
    prints = "\n".join("#print axioms " + name for name in NAMES)
    return (
        "import Lean\n"
        + "import " + import_module + "\n\n"
        + CORE.read_text(encoding="utf-8").rstrip() + "\n\n"
        + "open PiExponentStructuralKernelSnapshot\n\n"
        + "def collisionConstantRequests : Array StructuralRequest := #[\n"
        + requests + "\n  ]\n\n"
        + "run_meta do\n"
        + "  exportStructuralSnapshotJsonl collisionConstantRequests "
        + json.dumps(workspace_rel(output)) + "\n\n"
        + prints + "\n"
    )


def base_input_hashes():
    paths = [PRODUCER, CONSUMER, PREFLIGHT, CONTEXT, SOURCE, QUEUE, UNITS, SCOPES,
             GRAPH, OWNERS, CORE, RUNTIME]
    return {task_rel(path): sha(path) for path in paths}


def stage_files():
    units, owners = exact_source_evidence()
    provider = (
        b"import Mathlib\n\nnamespace OAI\n\nopen Filter\nopen scoped Topology\n\n"
        b"namespace PiExponent.DeterminantContradiction\n\n"
        + units[0] + b"\n\n" + units[1]
        + b"\n\nend PiExponent.DeterminantContradiction\n\nend OAI\n"
    )
    need(provider.count(units[0]) == 1 and provider.count(units[1]) == 1,
         "Provider does not contain each exact AST unit once")
    need(b"sorry" not in provider, "Provider contains sorry")

    source_snapshot_path = STAGE / "SourceSnapshot.lean"
    generated_snapshot_path = STAGE / "GeneratedSnapshot.lean"
    source_output = STAGE / "source-full-ci.jsonl"
    generated_output = STAGE / "generated-full-ci.jsonl"
    source_snapshot = snapshot_text(SOURCE_MODULE, SOURCE_MODULE, source_output, owners).encode("utf-8")
    generated_snapshot = snapshot_text(PLATFORM_MODULE, PLATFORM_MODULE, generated_output, owners).encode("utf-8")
    inputs = base_input_hashes()
    runtime_hash = sha(RUNTIME)

    generated = {
        PROVIDER_FILE: provider,
        "SourceSnapshot.lean": source_snapshot,
        "GeneratedSnapshot.lean": generated_snapshot,
    }
    plans = [
        (PROVIDER_FILE, ["Mathlib"], "emit", PLATFORM_MODULE),
        ("SourceSnapshot.lean", ["Lean", SOURCE_MODULE], "modecheck", "SourceSnapshot"),
        ("GeneratedSnapshot.lean", ["Lean", PLATFORM_MODULE], "modecheck", "GeneratedSnapshot"),
    ]
    manifests = {}
    for index, (filename, imports, mode, module) in enumerate(plans, 1):
        raw = generated[filename]
        manifests[f"c{index}.json"] = encode({
            "schema_version": 1,
            "artifact_kind": "ap7-collision-constant-bounded-compiler-manifest",
            "output": workspace_rel(STAGE / filename),
            "output_sha256": sha_bytes(raw),
            "imports": imports,
            "input_hashes": inputs,
            "runtime_sha256": runtime_hash,
            "source_commit": COMMIT,
            "source_module": SOURCE_MODULE,
            "platform_module": PLATFORM_MODULE,
            "provided_names": NAMES,
            "expected_actual_module_identity": module,
            "mode": "modecheck" if mode == "modecheck" else "emit-olean",
            "emit_olean": mode == "emit",
            "timeout_seconds": 300,
            "validated": False,
            "submission_ready": False,
        })
    generated.update(manifests)

    preparation = {
        "schema_version": 1,
        "artifact_kind": "ap7-collision-constant-provider-preparation",
        "source_commit": COMMIT,
        "source_module": SOURCE_MODULE,
        "platform_module": PLATFORM_MODULE,
        "provided_names": NAMES,
        "source_sha256": SOURCE_SHA256,
        "exact_source_units": [
            {**spec, "sha256": sha_bytes(unit)} for spec, unit in zip(UNIT_SPECS, units)
        ],
        "namespace": "OAI.PiExponent.DeterminantContradiction",
        "source_context_commands": ["open Filter", "open scoped Topology"],
        "minimal_import": "Mathlib",
        "minimal_import_basis": {
            NAMES[0]: {"type_dependencies": [], "value_dependencies": []},
            NAMES[1]: {"type_dependencies": [NAMES[0]], "value_dependencies": [NAMES[0]]},
        },
        "structural_core": task_rel(CORE),
        "structural_core_sha256": sha(CORE),
        "order": [row[0] for row in plans],
        "commands": [
            "python scripts/preflight_staged_module.py ap7/collision-constant/" + PROVIDER_FILE
            + " --root ap7/collision-constant --imports-manifest ap7/collision-constant/c1.json"
              " --emit-olean --timeout-seconds 300",
            "python scripts/preflight_staged_module.py ap7/collision-constant/SourceSnapshot.lean"
            " --root ap7/collision-constant --imports-manifest ap7/collision-constant/c2.json"
            " --timeout-seconds 300",
            "python scripts/preflight_staged_module.py ap7/collision-constant/GeneratedSnapshot.lean"
            " --root ap7/collision-constant --imports-manifest ap7/collision-constant/c3.json"
            " --timeout-seconds 300",
            "python scripts/certify_collision_constant_provider_existing.py --certify-existing",
        ],
        "expected_provider_olean": (
            "verification/staged-build/lib/lean/" + PLATFORM_MODULE.replace(".", "/") + ".olean"
        ),
        "snapshot_outputs": {
            "SourceSnapshot.lean": task_rel(source_output),
            "GeneratedSnapshot.lean": task_rel(generated_output),
        },
        "input_hashes": inputs,
        "Lean_started": False,
        "API_used": False,
        "validated": False,
        "submission_ready": False,
        "proposal_status": "Draft",
    }
    generated["preparation.json"] = encode(preparation)
    generated["academic-metadata.json"] = encode({
        "definition_title": "Collision constant and its positivity",
        "natural_language_statement": (
            "Define the collision constant as log(2)/4. This real constant is strictly positive."
        ),
        "mathematical_role": (
            "This provider supplies only the positive numerical constant used by later collision bounds; "
            "it does not establish the determinant-contradiction argument."
        ),
        "explanation": (
            "The definition is explicit. Positivity follows because log(2) is positive and 4 is positive."
        ),
        "declarations": NAMES,
        "tags": ["number-theory", "real-analysis", "openai-pi-exponent-017"],
        "source": (
            "OpenAI math, commit " + COMMIT + ": https://github.com/openai/math/blob/"
            + COMMIT + "/lean/OAI/NumberTheory/PiExponent/Approximation/"
              "DeterminantContradiction.lean#L15-L19"
        ),
        "source_url": (
            "https://github.com/openai/math/blob/" + COMMIT
            + "/lean/OAI/NumberTheory/PiExponent/Approximation/"
              "DeterminantContradiction.lean#L15-L19"
        ),
        "source_commit": COMMIT,
        "source_lines": [15, 19],
        "source_module": SOURCE_MODULE,
        "platform_module": PLATFORM_MODULE,
        "source_sha256": SOURCE_SHA256,
    })
    return generated


def check_outputs(generated):
    mismatches = []
    for name, raw in generated.items():
        path = STAGE / name
        if not path.is_file() or path.read_bytes() != raw:
            mismatches.append(name)
    if mismatches:
        raise ValueError("CollisionConstant stage differs: " + ", ".join(mismatches))
    return {"checked_files": len(generated), "all_hashes_match": True}


def runner_checks(generated):
    rows = {}
    provider_olean = STAGE.parent.parent / "staged-build/lib/lean" / Path(
        *PLATFORM_MODULE.split(".")).with_suffix(".olean")
    for index, filename in enumerate([PROVIDER_FILE, "SourceSnapshot.lean", "GeneratedSnapshot.lean"], 1):
        manifest = json.loads(generated[f"c{index}.json"])
        source = runner.source_path("ap7/collision-constant/" + filename)
        inputs = runner.verify_manifest_inputs(manifest)
        certificate = runner.verify_source_certificate(source, manifest)
        if filename != "GeneratedSnapshot.lean" or provider_olean.is_file():
            imports = runner.certified_imports(source, manifest)
            status = "certified"
        else:
            need(source.read_bytes().startswith(("import Lean\nimport " + PLATFORM_MODULE + "\n").encode()),
                 "Generated snapshot import header differs")
            imports = manifest["imports"]
            status = "pending-provider-olean"
        rows[filename] = {"manifest_inputs": inputs, "source_certificate": certificate,
                          "imports": imports, "import_status": status}
    return rows


def write_outputs(generated):
    for name, raw in generated.items():
        path = STAGE / name
        if path.exists() and path.read_bytes() != raw:
            raise ValueError("Existing collisionConstant stage would be overwritten: " + name)
        if not path.exists():
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(raw)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--prepare", action="store_true")
    mode.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    generated = stage_files()
    if args.prepare:
        write_outputs(generated)
    result = check_outputs(generated)
    result["runner_checks"] = runner_checks(generated)
    result.update({"Lean_started": False, "API_used": False,
                   "validated": False, "submission_ready": False})
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
