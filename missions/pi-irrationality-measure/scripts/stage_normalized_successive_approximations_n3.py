"""Stage the ap5/n3 normalized-approximations node without Lean or API use.

The generated proof imports only the two locally proved child theorem modules.
The platform statement stub is deliberately not emitted here.  A later
publication preparation must assemble ``wire_preamble + formal_statement`` and
prove byte equality with its separately compiled theorem source.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import shutil
from pathlib import Path

import preflight_staged_module as runner
import stage_formal_log_base_node as refs_producer

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
V = TASK / "verification"
STAGE = V / "ap5/n3"
SELF = Path(__file__).resolve()
VALIDATOR = TASK / "scripts/validate_normalized_successive_approximations_n3.py"
KEY = "OAI.NumberTheory.PiExponent.Approximation.SuccessiveApproximations:5926"
NAME = "OAI.PiExponent.exists_normalized_successive_approximations"
SOURCE_MODULE = "OAI.NumberTheory.PiExponent.Approximation.SuccessiveApproximations"
SOURCE_COMMIT = "adc7f1241b42e322a6451854ab7e4b4c146bf78a"
SOURCE_URL = ("https://github.com/openai/math/blob/" + SOURCE_COMMIT
              + "/lean/OAI/NumberTheory/PiExponent/Approximation/SuccessiveApproximations.lean#L134-L147")
PORT_SOURCE = TASK / "port/lean/OAI/NumberTheory/PiExponent/Approximation/SuccessiveApproximations.lean"
ORIGINAL_SOURCE = TASK / "source/lean/OAI/NumberTheory/PiExponent/Approximation/SuccessiveApproximations.lean"
FACTS = V / "sketch-SuccessiveApproximations-20261007-235252.log"
UNIT_PLAN = V / "platform-unit-plan-preview.json"
TYPE_CORE = V / "TypeOnlyTheoremSnapshotCore.inc"
RUNTIME = V / "lean-runtime.json"
RUNTIME_SHA = "ab61393780988c65493c5969dccfce9a5e88b18a3866e6ed65e2c89ca36fc9ef"
STAGED_LEAN = V / "staged-build/lib/lean"

CHILDREN = (
    {
        "stage": "verification/ap5/c1",
        "module": "Theorems.Thm_OAI_PiExponent_exists_successive_approximations",
        "theorem_name": "OAI.PiExponent.exists_successive_approximations",
        "source": "verification/ap5/c1/Theorems/Thm_OAI_PiExponent_exists_successive_approximations.lean",
        "source_preparation": "verification/ap5/c1/child-source-preparation.json",
        "certificate": "verification/ap5/c1/actual-child-validation.json",
    },
    {
        "stage": "verification/ap5/c2",
        "module": "Theorems.Thm_OAI_PiExponent_exists_normalized_selection_of_selector",
        "theorem_name": "OAI.PiExponent.exists_normalized_selection_of_selector",
        "source": "verification/ap5/c2/Theorems/Thm_OAI_PiExponent_exists_normalized_selection_of_selector.lean",
        "source_preparation": "verification/ap5/c2/child-source-preparation.json",
        "certificate": "verification/ap5/c2/actual-child-validation.json",
    },
)


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sha_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def rel(path: Path) -> str:
    return path.resolve().relative_to(TASK.resolve()).as_posix()


def workspace_rel(path: Path) -> str:
    return path.resolve().relative_to(ROOT.resolve()).as_posix()


def read(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def json_bytes(value) -> bytes:
    return (json.dumps(value, indent=2, ensure_ascii=False, sort_keys=True) + "\n").encode("utf-8")


def write_exact(path: Path, raw: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists() and path.read_bytes() == raw:
        return
    path.write_bytes(raw)


def archive_pending_preimage() -> None:
    prep_path = STAGE / "preparation.json"
    if not prep_path.is_file():
        return
    old = read(prep_path)
    if old.get("child_bindings_ready") is not False:
        return
    archive = STAGE / "pending-preimage"
    if archive.exists():
        return
    archive.mkdir(parents=True)
    names = [
        "academic-metadata.json", "source-command.json", "manifest.json",
        "certified-inputs.json", "preparation.json", "SourceSnapshot.lean",
        "SnapshotGenerated.lean", "SnapshotGeneratedWithRefs.lean",
        "Solutions/Sol_OAI_PiExponent_exists_normalized_successive_approximations.lean",
        "Theorems/Thm_OAI_PiExponent_exists_normalized_successive_approximations.lean",
        "c1.json", "c2.json", "c3.json", "c4.json", "c5.json",
    ]
    copied = {}
    for name in names:
        source = STAGE / name
        if source.is_file():
            target = archive / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, target)
            copied[name] = sha(source)
    write_exact(archive / "archive-manifest.json", json_bytes({
        "schema_version": 1,
        "artifact_kind": "ap5-n3-pending-child-preimage",
        "files": copied,
        "preserves_uncompiled_pending_inputs": True,
        "Lean_started": False,
        "API_used": False,
    }))


def unit_row() -> dict:
    plan = read(UNIT_PLAN)
    matches = [row for row in plan["units"] if row.get("id") == KEY]
    if len(matches) != 1:
        raise ValueError("The frozen source plan does not contain exactly one n3 unit")
    row = matches[0]
    expected = {
        "module": SOURCE_MODULE,
        "graph_names": [NAME],
        "graph_kinds": ["theorem"],
        "private": False,
        "definition_command": False,
        "direct_unit_dependencies": [
            "OAI.NumberTheory.PiExponent.Approximation.SuccessiveApproximations:164",
            "OAI.NumberTheory.PiExponent.Approximation.SuccessiveApproximations:4368",
        ],
    }
    for field, value in expected.items():
        if row.get(field) != value:
            raise ValueError("Frozen source AST unit differs at " + field)
    if row["start"]["offset"] != 5926 or row["end"]["offset"] != 6673:
        raise ValueError("Frozen source AST byte range differs")
    return row


def source_command() -> tuple[dict, bytes]:
    row = unit_row()
    raw_source = PORT_SOURCE.read_bytes()
    if sha(PORT_SOURCE) != row["source_sha256"]:
        raise ValueError("Port source differs from the source AST unit")
    raw = raw_source[row["start"]["offset"]:row["end"]["offset"]]
    if not raw.startswith(b"theorem exists_normalized_successive_approximations\r\n"):
        raise ValueError("n3 raw command prefix differs")
    if not raw.endswith(b"    (exists_successive_approximations nu hnu hbad)"):
        raise ValueError("n3 raw command proof suffix differs")
    return row, raw


def child_binding(spec: dict) -> dict:
    source = TASK / spec["source"]
    source_prep = TASK / spec["source_preparation"]
    if not source.is_file() or not source_prep.is_file():
        raise ValueError("Prepared proved-child source is missing: " + spec["stage"])
    source_doc = read(source_prep)
    if (source_doc.get("source") != workspace_rel(source)
            or source_doc.get("source_sha256") != sha(source)
            or source_doc.get("module") != spec["module"]
            or source_doc.get("theorem_name") != spec["theorem_name"]
            or source_doc.get("sorry_free_actual_proof_body") is not True):
        raise ValueError("Prepared proved-child source certificate differs: " + spec["stage"])
    base = {
        "stage": spec["stage"],
        "module": spec["module"],
        "theorem_name": spec["theorem_name"],
        "child_source": rel(source),
        "child_source_sha256": sha(source),
        "source_preparation": rel(source_prep),
        "source_preparation_sha256": sha(source_prep),
        "expected_certificate": spec["certificate"],
    }
    cert_path = TASK / spec["certificate"]
    if not cert_path.is_file():
        return {**base, "ready": False, "certificate": None,
                "certificate_sha256": None, "output_olean": None,
                "output_olean_sha256": None, "validated": False}
    cert = read(cert_path)
    if (cert.get("validated") is not True or cert.get("Std3_only") is not True
            or cert.get("theorem_name") != spec["theorem_name"]
            or cert.get("module") != spec["module"]
            or cert.get("child_source") != workspace_rel(source)
            or cert.get("child_source_sha256") != sha(source)):
        raise ValueError("Actual proved-child certificate identity differs: " + spec["stage"])
    owner = cert.get("actual_module_owner", {})
    if (owner.get("module") != spec["module"] or owner.get("kind") != "ImportedModule"
            or not isinstance(owner.get("index"), int) or owner["index"] < 0):
        raise ValueError("Actual proved-child module owner is not certified ImportedModule")
    olean = ROOT / cert.get("child_olean", "")
    if not olean.is_file() or sha(olean) != cert.get("child_olean_sha256"):
        raise ValueError("Actual proved-child OLean pin differs: " + spec["stage"])
    return {**base, "ready": True, "certificate": rel(cert_path),
            "certificate_sha256": sha(cert_path), "output_olean": rel(olean),
            "output_olean_sha256": sha(olean), "validated": True,
            "actual_module_owner": owner, "proof_axioms": "Std3"}


def proof_reference_addon(output: Path) -> bytes:
    addon = refs_producer.proof_reference_addon([], output).encode("utf-8")
    old_decl = b"def export ("
    old_call = b"FormalLogProofReferenceSnapshot.export #[`solution]"
    if addon.count(old_decl) != 1 or addon.count(old_call) != 1:
        raise ValueError("Reserved export identifier repair domain differs")
    addon = addon.replace(old_decl, b"def exportProofRefs (", 1)
    addon = addon.replace(
        old_call, b"FormalLogProofReferenceSnapshot.exportProofRefs #[`solution]", 1)
    return addon


def theorem_sources(raw_command: bytes) -> tuple[bytes, bytes]:
    raw = raw_command.replace(b"\r\n", b"\n")
    short = b"theorem exists_normalized_successive_approximations"
    if raw.count(short) != 1:
        raise ValueError("n3 theorem name edit is not singleton")
    solution = raw.replace(short, b"theorem solution", 1)
    for old, new in (
        (b"exists_normalized_selection_of_selector",
         b"OAI.PiExponent.exists_normalized_selection_of_selector"),
        (b"exists_successive_approximations",
         b"OAI.PiExponent.exists_successive_approximations"),
    ):
        if solution.count(old) != 1:
            raise ValueError("n3 proof reference edit is not singleton: " + old.decode())
        solution = solution.replace(old, new, 1)
    source_name = b"theorem OAI.PiExponent.exists_normalized_successive_approximations"
    formal = raw.replace(short, source_name, 1)
    proof_marker = b" := by\n"
    if formal.count(proof_marker) != 1:
        raise ValueError("n3 formal statement proof marker differs")
    formal = formal[:formal.index(proof_marker)] + b" := by sorry\n"
    return solution, formal


def canonical_type_bytes(command: bytes, theorem_prefix: bytes) -> bytes:
    command = command.replace(b"\r\n", b"\n")
    marker = b" := by"
    if command.count(marker) != 1 or command.count(theorem_prefix) != 1:
        raise ValueError("Theorem type extraction markers differ")
    return command[:command.index(marker)].replace(theorem_prefix, b"theorem _", 1) + b"\n"


def metadata() -> dict:
    return {
        "theorem_title": "Normalized successive rational approximations from a uniform power-law hypothesis",
        "natural_language_statement": (
            "Let $\\nu,X,D\\in\\mathbb R$ with $\\nu>0$. Assume the conditional hypothesis "
            "$h_{\\mathrm{bad}}$: for every $Q\\in\\mathbb N$ there are $p\\in\\mathbb Z$ and "
            "$q\\in\\mathbb N$ with $Q\\le q$ and "
            "$$\\left|\\pi-\\frac{p}{q}\\right|\\le q^{-\\nu}. $$\n\n"
            "Then there are sequences $p_n,q_n,x_n$ with $x_0=1$, "
            "$x_{n+1}=\\lceil\\log q_n\\rceil$, the same approximation bound, $q_n\\ge2$, "
            "$p_n\\ne0$, $1\\le\\lceil\\log q_n\\rceil$, $X<x_{n+1}$, and\n\n"
            "$$D\\prod_{j<i}x_j<x_i\\qquad(i>0).$$\n\n"
            "This is conditional on $h_{\\mathrm{bad}}$ and $\\nu>0$; it does not assert that "
            "the hypothesis holds unconditionally for $\\pi$."
        ),
        "explanation": (
            "The result composes two proved steps from the source. The first turns the uniform "
            "power-law hypothesis into successive approximants whose logarithmic weights beat an "
            "arbitrary history-dependent selector. The second chooses the selector to enforce the "
            "$X$ margin and strict $D$-weighted product growth while preserving the approximation "
            "data. Its role in the campaign is the normalized approximation-sequence constructor "
            "used by later admissible-parameter and determinant estimates."
        ),
        "tags": ["openai-pi-exponent-017", "number-theory", "rational-approximation"],
        "source_commit": SOURCE_COMMIT,
        "source_url": SOURCE_URL,
    }


def make_artifacts(bindings: list[dict]) -> dict[str, bytes]:
    row, raw = source_command()
    solution, formal = theorem_sources(raw)
    core = TYPE_CORE.read_bytes().replace(b"\r\n", b"\n")
    imports = b"import Lean\n" + b"".join(
        ("import " + child["module"] + "\n").encode("utf-8") for child in bindings)
    source_snapshot = (
        b"import Lean\nimport " + SOURCE_MODULE.encode() + b"\n\n" + core +
        b"\nset_option pp.universes true\nset_option pp.fullNames true\nset_option pp.explicit true\n"
        b"run_meta do\n  PiExponentInterfaceSnapshot.exportSnapshot "
        b"#[`OAI.PiExponent.exists_normalized_successive_approximations] "
        b"\"missions/pi-irrationality-measure/verification/ap5/n3/original-type.json\"\n"
        b"#print axioms OAI.PiExponent.exists_normalized_successive_approximations\n"
    )
    generated = (
        imports + b"\n" + solution + b"\n\n" + core +
        b"\nset_option pp.universes true\nset_option pp.fullNames true\nset_option pp.explicit true\n"
        b"run_meta do\n  PiExponentInterfaceSnapshot.exportSnapshot #[`solution] "
        b"\"missions/pi-irrationality-measure/verification/ap5/n3/generated-type.json\"\n"
        b"#print axioms solution\n"
    )
    refs_output = STAGE / "proof-references.json"
    with_refs = generated + proof_reference_addon(refs_output)
    exact_solution = imports + b"\n" + solution + b"\n\n#print axioms solution\n"
    exact_statement = imports + b"\n" + formal
    return {
        "SourceSnapshot.lean": source_snapshot,
        "SnapshotGenerated.lean": generated,
        "SnapshotGeneratedWithRefs.lean": with_refs,
        "Solutions/Sol_OAI_PiExponent_exists_normalized_successive_approximations.lean": exact_solution,
        "Theorems/Thm_OAI_PiExponent_exists_normalized_successive_approximations.lean": exact_statement,
        "_formal_statement": formal,
        "_wire_preamble": imports + b"\n",
        "_raw_command": raw,
        "_unit_row": json_bytes(row),
    }


def prepare() -> dict:
    bindings = [child_binding(spec) for spec in CHILDREN]
    all_ready = all(row["ready"] for row in bindings)
    if all_ready:
        archive_pending_preimage()
    artifacts = make_artifacts(bindings)
    STAGE.mkdir(parents=True, exist_ok=True)
    for name, raw in artifacts.items():
        if not name.startswith("_"):
            write_exact(STAGE / name, raw)
    write_exact(STAGE / "academic-metadata.json", json_bytes(metadata()))
    unit = json.loads(artifacts["_unit_row"])
    source_record = {
        "schema_version": 1,
        "artifact_kind": "ap5-n3-exact-source-ast-command",
        "source_commit": SOURCE_COMMIT,
        "source_url": SOURCE_URL,
        "source_module": SOURCE_MODULE,
        "source_unit": unit,
        "raw_command_utf8": artifacts["_raw_command"].decode("utf-8"),
        "raw_command_sha256": sha_bytes(artifacts["_raw_command"]),
        "raw_command_range": {"start": 5926, "end": 6673},
        "port_source": rel(PORT_SOURCE),
        "port_source_sha256": sha(PORT_SOURCE),
        "original_source": rel(ORIGINAL_SOURCE),
        "original_source_sha256": sha(ORIGINAL_SOURCE),
        "facts": rel(FACTS),
        "facts_sha256": sha(FACTS),
        "exact_source_ast_reconstructed": True,
        "Lean_started": False,
        "API_used": False,
    }
    write_exact(STAGE / "source-command.json", json_bytes(source_record))
    input_hashes = {
        rel(SELF): sha(SELF),
        rel(VALIDATOR): sha(VALIDATOR),
        rel(Path(refs_producer.__file__)): sha(Path(refs_producer.__file__)),
        rel(PORT_SOURCE): sha(PORT_SOURCE),
        rel(ORIGINAL_SOURCE): sha(ORIGINAL_SOURCE),
        rel(FACTS): sha(FACTS),
        rel(UNIT_PLAN): sha(UNIT_PLAN),
        rel(TYPE_CORE): sha(TYPE_CORE),
        rel(RUNTIME): sha(RUNTIME),
    }
    for child in bindings:
        input_hashes[child["child_source"]] = child["child_source_sha256"]
        input_hashes[child["source_preparation"]] = child["source_preparation_sha256"]
        if child["ready"]:
            input_hashes[child["certificate"]] = child["certificate_sha256"]
            input_hashes[child["output_olean"]] = child["output_olean_sha256"]
    outputs = {name: sha_bytes(raw) for name, raw in artifacts.items() if not name.startswith("_")}
    formal = artifacts["_formal_statement"]
    preamble = artifacts["_wire_preamble"]
    source_type = canonical_type_bytes(
        artifacts["_raw_command"], b"theorem exists_normalized_successive_approximations")
    solution_type = canonical_type_bytes(
        (STAGE / "Solutions/Sol_OAI_PiExponent_exists_normalized_successive_approximations.lean").read_bytes()
        .split(b"\n\n#print axioms solution", 1)[0].split(b"\n\n", 1)[1],
        b"theorem solution")
    if source_type != solution_type:
        raise ValueError("Source AST theorem type and literal solution type text differ")
    manifest = {
        "schema_version": 1,
        "artifact_kind": "ap5-n3-strict-source-and-proof-stage",
        "node": KEY,
        "theorem_name": NAME,
        "source_graph_name": NAME,
        "source_commit": SOURCE_COMMIT,
        "source_url": SOURCE_URL,
        "mathematical_role": (
            "Composition node: converts the conditional unbounded-denominator approximation input "
            "into the normalized sequence and multiplicative growth package consumed downstream."
        ),
        "source_command": rel(STAGE / "source-command.json"),
        "source_command_sha256": sha(STAGE / "source-command.json"),
        "source_unit": unit,
        "source_components": [{
            "source_module": SOURCE_MODULE,
            "source": rel(PORT_SOURCE), "source_sha256": sha(PORT_SOURCE),
            "original_source": rel(ORIGINAL_SOURCE), "original_source_sha256": sha(ORIGINAL_SOURCE),
            "facts": rel(FACTS), "facts_sha256": sha(FACTS),
        }],
        "child_bindings": bindings,
        "imports": ["Lean", *[row["module"] for row in bindings]],
        "wire_preamble": preamble.decode("utf-8"),
        "formal_statement": formal.decode("utf-8"),
        "formal_statement_sha256": sha_bytes(formal),
        "canonical_source_and_solution_type_sha256": sha_bytes(source_type),
        "canonical_source_and_solution_type_text_equal": True,
        "assembled_wire_theorem_sha256": sha_bytes(preamble + formal),
        "publication_assembly_guard": {
            "required_before_any_API_payload": True,
            "condition": "wire_preamble + formal_statement bytes equal separately compiled Thm bytes",
            "actual_compiled_theorem_source": workspace_rel(
                STAGE / "Theorems/Thm_OAI_PiExponent_exists_normalized_successive_approximations.lean"),
            "actual_compiled_theorem_source_sha256": outputs[
                "Theorems/Thm_OAI_PiExponent_exists_normalized_successive_approximations.lean"],
            "actual_compiled_theorem_preflight": None,
            "satisfied": False,
        },
        "statement": workspace_rel(
            STAGE / "Theorems/Thm_OAI_PiExponent_exists_normalized_successive_approximations.lean"),
        "statement_sha256": outputs[
            "Theorems/Thm_OAI_PiExponent_exists_normalized_successive_approximations.lean"],
        "solution": workspace_rel(STAGE / "Solutions/Sol_OAI_PiExponent_exists_normalized_successive_approximations.lean"),
        "solution_sha256": outputs["Solutions/Sol_OAI_PiExponent_exists_normalized_successive_approximations.lean"],
        "snapshot_outputs": outputs,
        "type_json_outputs": {
            "source": rel(STAGE / "original-type.json"),
            "generated": rel(STAGE / "generated-type.json"),
            "proof_references": rel(STAGE / "proof-references.json"),
        },
        "runtime_sha256": RUNTIME_SHA,
        "input_hashes": input_hashes,
        "top_level_literal_theorem_solution": True,
        "target_statement_stub_source_staged": True,
        "target_statement_stub_olean_emitted": False,
        "target_statement_stub_imported_by_proof_artifact": False,
        "theorem_proof_values_exported": False,
        "Lean_started": False,
        "API_used": False,
        "validated": False,
        "submission_ready": False,
        "pending": ([] if all_ready else ["actual proved child certificates and OLeans"])
                   + ["four strict preflights", "kernel type equality", "Std3 audit",
                      "actual proof-reference and first-search module-owner audit",
                      "compiled theorem wire-byte equality before API use"],
    }
    write_exact(STAGE / "manifest.json", json_bytes(manifest))
    certified = {
        "schema_version": 1,
        "artifact_kind": "ap5-n3-certified-inputs",
        "node": KEY,
        "child_certificates": [row for row in bindings if row["ready"]],
        "pending_children": [row for row in bindings if not row["ready"]],
        "child_bindings_ready": all_ready,
        "Lean_started": False,
        "validated": False,
        "submission_ready": False,
    }
    write_exact(STAGE / "certified-inputs.json", json_bytes(certified))
    manifest = read(STAGE / "manifest.json")
    shared_pins = dict(manifest["input_hashes"])
    shared_pins[rel(STAGE / "manifest.json")] = sha(STAGE / "manifest.json")
    shared_pins[rel(STAGE / "academic-metadata.json")] = sha(STAGE / "academic-metadata.json")
    shared_pins[rel(STAGE / "source-command.json")] = sha(STAGE / "source-command.json")
    shared_pins[rel(STAGE / "certified-inputs.json")] = sha(STAGE / "certified-inputs.json")
    files = [
        "SourceSnapshot.lean", "SnapshotGenerated.lean", "SnapshotGeneratedWithRefs.lean",
        "Solutions/Sol_OAI_PiExponent_exists_normalized_successive_approximations.lean",
        "Theorems/Thm_OAI_PiExponent_exists_normalized_successive_approximations.lean",
    ]
    compile_rows = {}
    for index, name in enumerate(files, 1):
        source = STAGE / name
        source_side = name == "SourceSnapshot.lean"
        required = [] if source_side or all_ready else [row["module"] for row in bindings if not row["ready"]]
        doc = {
            "schema_version": 1,
            "artifact_kind": "ap5-n3-strict-file-import-certificate",
            "output": workspace_rel(source),
            "output_sha256": sha(source),
            "imports": (["Lean", SOURCE_MODULE] if source_side else manifest["imports"]),
            "input_hashes": shared_pins,
            "pending_required_import_pins": required,
            "runtime_sha256": RUNTIME_SHA,
            "node": KEY,
            "node_validated": False,
            "timeout_seconds": 300,
            "Lean_started": False,
            "submission_ready": False,
        }
        path = STAGE / f"c{index}.json"
        write_exact(path, json_bytes(doc))
        compile_rows[name] = {"manifest": rel(path), "manifest_sha256": sha(path),
                              "pending_child_binding": bool(required)}
    preparation = {
        "schema_version": 1,
        "artifact_kind": "ap5-n3-strict-preparation",
        "stage": rel(STAGE),
        "node": KEY,
        "manifest_sha256": sha(STAGE / "manifest.json"),
        "metadata_sha256": sha(STAGE / "academic-metadata.json"),
        "source_command_sha256": sha(STAGE / "source-command.json"),
        "certified_inputs_sha256": sha(STAGE / "certified-inputs.json"),
        "child_bindings": bindings,
        "child_bindings_ready": all_ready,
        "generated_with_refs_prefix": rel(STAGE / "SnapshotGenerated.lean"),
        "generated_with_refs_prefix_sha256": sha(STAGE / "SnapshotGenerated.lean"),
        "generated_with_refs_prefix_bytes": (STAGE / "SnapshotGenerated.lean").stat().st_size,
        "proof_reference_addon_sha256": sha_bytes(proof_reference_addon(STAGE / "proof-references.json")),
        "reserved_export_identifier_fixed_to_exportProofRefs": True,
        "compile_manifests": compile_rows,
        "ready_commands": {
            name: ("python scripts/preflight_staged_module.py ap5/n3/" + name
                   + " --root ap5/n3 --imports-manifest ap5/n3/c" + str(i)
                   + ".json --timeout-seconds 300")
            for i, name in enumerate(files, 1)
        },
        "frozen_outputs_sha256": {name: sha(STAGE / name) for name in files},
        "output_json_pins_pending": manifest["type_json_outputs"],
        "publication_assembly_guard": manifest["publication_assembly_guard"],
        "Lean_started": False,
        "API_used": False,
        "validated": False,
        "submission_ready": False,
    }
    write_exact(STAGE / "preparation.json", json_bytes(preparation))
    return check()


def check() -> dict:
    bindings = [child_binding(spec) for spec in CHILDREN]
    artifacts = make_artifacts(bindings)
    manifest = read(STAGE / "manifest.json")
    preparation = read(STAGE / "preparation.json")
    if manifest["child_bindings"] != bindings or preparation["child_bindings"] != bindings:
        raise ValueError("Child state changed; rerun --prepare to preserve and replace the pending preimage")
    for name, raw in artifacts.items():
        if not name.startswith("_") and (STAGE / name).read_bytes() != raw:
            raise ValueError("Staged n3 source differs from exact reconstruction: " + name)
    base = (STAGE / "SnapshotGenerated.lean").read_bytes()
    extended = (STAGE / "SnapshotGeneratedWithRefs.lean").read_bytes()
    addon = proof_reference_addon(STAGE / "proof-references.json")
    if extended != base + addon:
        raise ValueError("WithRefs is not the exact generated prefix plus exportProofRefs collector")
    if manifest["wire_preamble"].encode() + manifest["formal_statement"].encode() != (
            artifacts["_wire_preamble"] + artifacts["_formal_statement"]):
        raise ValueError("Frozen wire assembly fields differ from reconstruction")
    for name, row in preparation["compile_manifests"].items():
        source = STAGE / name
        mp = TASK / row["manifest"]
        doc = read(mp)
        if sha(mp) != row["manifest_sha256"] or sha(source) != doc["output_sha256"]:
            raise ValueError("Compiler manifest/source pin differs: " + name)
        runner.verify_manifest_inputs(doc)
        runner.verify_source_certificate(source, doc)
        if preparation["child_bindings_ready"] or name == "SourceSnapshot.lean":
            runner.certified_imports(source, doc)
    return {
        "checked": True,
        "node": NAME,
        "stage": rel(STAGE),
        "child_bindings_ready": preparation["child_bindings_ready"],
        "frozen_inputs": manifest["input_hashes"],
        "ready_commands": preparation["ready_commands"],
        "compile_files": list(preparation["compile_manifests"]),
        "target_statement_stub_source_staged": True,
        "target_statement_stub_olean_emitted": False,
        "target_statement_stub_imported_by_proof_artifact": False,
        "Lean_started": False,
        "API_used": False,
        "validated": False,
        "submission_ready": False,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--prepare", action="store_true")
    group.add_argument("--check", action="store_true")
    args = parser.parse_args()
    print(json.dumps(prepare() if args.prepare else check(), indent=2, ensure_ascii=False))
