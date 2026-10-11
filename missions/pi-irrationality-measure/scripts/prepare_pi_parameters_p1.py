"""Repeatably prepare/check the pure-Python Parameters p1 staging node.

This script never runs Lean or calls the platform.  Compilation is performed
later, one file at a time, with the four commands recorded in preparation.json.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys

import preflight_staged_module as runner

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
V = TASK / "verification"
STAGE = V / "ap5" / "p1"
NAME = "OAI.PiExponent.exists_parameters"
MODULE = "Theorems.Thm_OAI_PiExponent_exists_parameters"
SOURCE_MODULE = "OAI.NumberTheory.PiExponent.Approximation.Parameters"
HELPER = "OAI.PiExponent.exists_eta_preserving_exponent_gap"
CHILD = "OAI.PiExponent.exists_rational_parameters"
CHILD_MODULE = "Theorems.Thm_OAI_PiExponent_exists_rational_parameters"
DEF_MODULE = "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Parameters"
DEF_NAME = "OAI.PiExponent.Parameters"
COMMIT = "adc7f1241b42e322a6451854ab7e4b4c146bf78a"
RUNTIME = V / "lean-runtime.json"
AST = V / "ast-unit-inventory.json"
SCOPE = V / "ast-scope-inventory.json"
SOURCE = TASK / "source/lean/OAI/NumberTheory/PiExponent/Approximation/Parameters.lean"
PORT = TASK / "port/lean/OAI/NumberTheory/PiExponent/Approximation/Parameters.lean"
STRUCTURAL = V / "providers-complete-preview/all-shared-safe-leaves/snapshots/Def_OAI_NumberTheory_PiExponent_Approximation_Parameters/provider-validation-structural.json"
PROVIDER_MANIFEST = V / "providers-complete-preview/all-shared-safe-leaves/Definitions/Def_OAI_NumberTheory_PiExponent_Approximation_Parameters.manifest.json"
PROVIDER_SOURCE = V / "providers-complete-preview/all-shared-safe-leaves/Definitions/Def_OAI_NumberTheory_PiExponent_Approximation_Parameters.lean"
PARAMS_OLEAN = V / "staged-build/lib/lean/Definitions/Def_OAI_NumberTheory_PiExponent_Approximation_Parameters.olean"
CHILD_CERT = V / "ap4/c2/actual-child-validation.json"
CHILD_SOURCE = V / "ap4/c2/Theorems/Thm_OAI_PiExponent_exists_rational_parameters.lean"
CHILD_OLEAN = V / "staged-build/lib/lean/Theorems/Thm_OAI_PiExponent_exists_rational_parameters.olean"
CHILD_TYPE = V / "ap4/c2/child-type.json"
CHILD_REFS = V / "ap4/c2/child-proof-references.json"
CORE = V / "TypeOnlyTheoremSnapshotCore.inc"
CONTEXT = TASK / "scripts/validate_namespace_context_providers.py"
PREFLIGHT = TASK / "scripts/preflight_staged_module.py"
PRODUCER = Path(__file__).resolve()
CONSUMER = TASK / "scripts/certify_pi_parameters_p1_existing.py"
STRUCTURAL_SHA = "8b2ac14792ee70c941243f57b6345e9efbb9cfd941785ad674cfc8e667c41939"
PARAMS_OLEAN_SHA = "c51db1038abab3aac8c99d0db3e139f952120bb4627fce3b0254dec50b2f3f45"
CHILD_CERT_SHA = "a79e6b5e7983bcb6116a6e23d50e89f5595971a158d806ca4c4f3c0ff630917b"
CHILD_OLEAN_SHA = "c02d29e033f7859f8127935b7ef0864966756b22606a5ab7ec2ae202c32ef198"


def sha_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha(path: Path) -> str:
    return sha_bytes(path.read_bytes())


def rel(path: Path) -> str:
    return path.resolve().relative_to(TASK.resolve()).as_posix()


def workspace_rel(path: Path) -> str:
    return path.resolve().relative_to(ROOT.resolve()).as_posix()


def read(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def extract_source_command(row: dict) -> str:
    lines = SOURCE.read_bytes().decode("utf-8").splitlines(keepends=True)
    a, b = row["start"], row["end"]
    return "".join([lines[a["line"] - 1][a["col"]:]]
                   + lines[a["line"]:b["line"] - 1]
                   + [lines[b["line"] - 1][:b["col"]]])


def inventory_row(tree, key: str, value: str) -> dict:
    found = []
    def visit(item):
        if isinstance(item, dict):
            if item.get(key) == value:
                found.append(item)
            for child in item.values():
                visit(child)
        elif isinstance(item, list):
            for child in item:
                visit(child)
    visit(tree)
    if len(found) != 1:
        raise ValueError(f"Expected one AST inventory row for {value}; found {len(found)}")
    return found[0]


def source_material():
    source_bytes, port_bytes = SOURCE.read_bytes(), PORT.read_bytes()
    units, scopes = read(AST), read(SCOPE)
    helper_row = inventory_row(units, "nameText", "exists_eta_preserving_exponent_gap")
    target_row = inventory_row(units, "nameText", "exists_parameters")
    helper = extract_source_command(helper_row)
    target = extract_source_command(target_row)
    if (not helper.startswith("theorem exists_eta_preserving_exponent_gap")
            or not target.startswith("theorem exists_parameters ")
            or helper_row.get("graph_names") != [HELPER]
            or target_row.get("graph_names") != [NAME]):
        raise ValueError("Source AST command identity or exact selected rows changed")
    helper_scope = inventory_row(scopes, "verified_name", HELPER)
    target_scope = inventory_row(scopes, "verified_name", NAME)
    for row, scope, expected in ((helper_row, helper_scope, HELPER),
                                 (target_row, target_scope, NAME)):
        if scope.get("namespace") != "OAI.PiExponent" or scope.get("context_commands") != []:
            raise ValueError(f"Source scope witness changed for {expected}")
        if scope.get("range", {}).get("start") != row.get("start") or scope.get("range", {}).get("end") != row.get("end"):
            raise ValueError(f"AST/scope source ranges differ for {expected}")
    if "sorry" in target:
        raise ValueError("Pinned source theorem unexpectedly contains sorry")
    return source_bytes, port_bytes, helper, target, helper_row, target_row, helper_scope, target_scope


def stage_files():
    sb, pb, helper, target, hu, tu, hs, ts = source_material()
    nl_helper = helper.replace("\r\n", "\n")
    nl_target = target.replace("\r\n", "\n")
    imports = (f"import {DEF_MODULE}\nimport {CHILD_MODULE}\nimport Mathlib\n\n")
    preamble = imports + "open OAI OAI.PiExponent\n\n"
    source_formal = nl_target.split(" := by", 1)[0] + " := by\n  sorry\n"
    formal_statement = source_formal.replace("theorem exists_parameters ", f"theorem {NAME} ", 1)
    statement = preamble + formal_statement
    helper_module = "namespace OAI\nnamespace PiExponent\n\n" + helper + "\n\nend PiExponent\nend OAI\n"
    solution = (imports + "\n" + helper_module + "\nopen OAI OAI.PiExponent\n\n"
                + target.replace("theorem exists_parameters ", "theorem solution ", 1)
                + "\n\n#print axioms solution\n")
    core = CORE.read_text(encoding="utf-8")
    snapshot_head = "import Lean\n"
    source_snapshot = (snapshot_head + f"import {SOURCE_MODULE}\n\nopen Lean Meta\n\n" + core
        + f"\nset_option pp.universes true\nset_option pp.fullNames true\nset_option pp.explicit true\n"
        + f"run_meta do\n  PiExponentInterfaceSnapshot.exportSnapshot #[`{HELPER}, `{NAME}] \"verification/ap5/p1/original-type.json\"\n"
        + f"#print axioms {HELPER}\n#print axioms {NAME}\n")
    solution_body = solution.split(imports, 1)[1]
    generated_imports = snapshot_head + imports
    generated_snapshot_base = (generated_imports + "\n" + formal_statement + "\n"
        + solution_body + "\nopen Lean Meta\n\n" + core
        + "\nset_option pp.universes true\nset_option pp.fullNames true\nset_option pp.explicit true\n"
        + f"run_meta do\n  PiExponentInterfaceSnapshot.exportSnapshot #[`{HELPER}, `{NAME}, `solution] \"verification/ap5/p1/generated-type.json\"\n")
    refs_source = '''\nopen Lean Meta in\nrun_meta do\n  let names : Array Lean.Name := #[`OAI.PiExponent.exists_eta_preserving_exponent_gap, `solution]\n  let env ← Lean.getEnv\n  let mut rows : Array Lean.Json := #[]\n  for name in names do\n    let some idx := env.getModuleIdxFor? name | throwError "p1 proof reference is not an imported or owned CI: {name}"\n    let some ci := env.find? name | throwError "missing p1 proof reference {name}"\n    let value ← match ci with | .thmInfo t => pure t.value | _ => throwError "p1 reference is not a theorem {name}"\n    if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars || value.hasMVar || value.hasFVar || value.hasLooseBVars then throwError "open p1 proof reference {name}"\n    let some owner := env.header.moduleNames[idx.toNat]? | throwError "invalid p1 theorem owner {name}"\n    unless owner == env.mainModule do throwError "p1 theorem is not owned by generated snapshot module {name}"\n    let axioms ← Lean.collectAxioms name\n    unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do throwError "non-Std3 p1 proof reference {name}"\n    let refs := fun (e : Lean.Expr) => ((e.getUsedConstants.map Lean.Name.toString).qsort (fun a b => a < b)).eraseDups\n    rows := rows.push <| Lean.Json.mkObj [("name", Lean.toJson name.toString), ("kind", Lean.toJson "theorem"), ("levelParams", Lean.toJson (ci.levelParams.map Lean.Name.toString)), ("closedType", Lean.toJson true), ("closedValue", Lean.toJson true), ("typeRefs", Lean.toJson (refs ci.type)), ("valueRefs", Lean.toJson (refs value)), ("axioms", Lean.toJson ((axioms.map Lean.Name.toString).qsort (fun a b => a < b))), ("owner", Lean.Json.mkObj [("kind", Lean.toJson "OwnModule"), ("module", Lean.toJson owner.toString)])]\n  IO.FS.writeFile "verification/ap5/p1/proof-references.json" ((Lean.Json.mkObj [("schemaVersion", Lean.toJson 1), ("probeMainModule", Lean.toJson env.mainModule.toString), ("rows", Lean.Json.arr rows)]).pretty)\n'''
    old_owner_check = '''    let some idx := env.getModuleIdxFor? name | throwError "p1 proof reference is not an imported or owned CI: {name}"
    let some ci := env.find? name | throwError "missing p1 proof reference {name}"
    let value ← match ci with | .thmInfo t => pure t.value | _ => throwError "p1 reference is not a theorem {name}"
    if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars || value.hasMVar || value.hasFVar || value.hasLooseBVars then throwError "open p1 proof reference {name}"
    let some owner := env.header.moduleNames[idx.toNat]? | throwError "invalid p1 theorem owner {name}"
    unless owner == env.mainModule do throwError "p1 theorem is not owned by generated snapshot module {name}"'''
    new_owner_check = '''    if (env.getModuleIdxFor? name).isSome then throwError "p1 proof reference is not an OwnModule CI: {name}"
    let some ci := env.find? name | throwError "missing p1 proof reference {name}"
    let value ← match ci with | .thmInfo t => pure t.value | _ => throwError "p1 reference is not a theorem {name}"
    if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars || value.hasMVar || value.hasFVar || value.hasLooseBVars then throwError "open p1 proof reference {name}"
    let owner := env.mainModule'''
    if old_owner_check not in refs_source:
        raise ValueError("WithRefs owner block differs from its pinned expected exporter source")
    refs_source = refs_source.replace(old_owner_check, new_owner_check, 1)
    refs_source = refs_source.replace(".qsort (fun a b => a < b)).eraseDups", ".qsort (fun a b => a < b))", 1)
    generated_with_refs = generated_snapshot_base + refs_source
    metadata = {
        "tags": ["openai-pi-exponent-017", "number-theory", "rational-approximation"],
        "source_commit": COMMIT,
        "source_url": f"https://github.com/openai/math/blob/{COMMIT}/lean/OAI/NumberTheory/PiExponent/Approximation/Parameters.lean#L112-L118",
        "theorem_title": "Existence of parameters preserving the approximation exponent gap",
        "natural_language_statement": "For every real exponent ν greater than 2, there is a parameter record containing rational thresholds θ, A, B, C and a real η satisfying the published positivity, ordering, approximation-gap, and eta-adjusted gap conditions.",
        "explanation": "Choose θ, A, B, and C using the proved rational-parameter lemma. The strict gap inequality leaves positive slack; the source helper chooses a positive η below one small enough to preserve that inequality after replacing A by A(1−η). These witnesses form the published Parameters record.",
    }
    ast_witness = {
        "schema_version": 1, "artifact_kind": "source017-parameters-node-ast-scope-witness",
        "source_commit": COMMIT, "source_path": workspace_rel(SOURCE), "source_sha256": sha_bytes(sb),
        "port_path": workspace_rel(PORT), "port_sha256": sha_bytes(pb),
        "source_and_port_byte_identical": sb == pb,
        "commands": [
            {"name": HELPER, "range": hu, "scope": hs,
             "source_raw_command_sha256": sha_bytes(helper.encode()),
             "staged_command_sha256": sha_bytes(helper.encode()), "exact_source_command_bytes_preserved": True},
            {"name": NAME, "range": tu, "scope": ts,
             "source_raw_command_sha256": sha_bytes(target.encode()),
             "source_type_statement_sha256": sha_bytes((nl_target.split(" := by", 1)[0]).encode()),
             "platform_formal_statement_sha256": sha_bytes(formal_statement.encode()),
             "binding_adaptation": f"source scoped name exists_parameters is emitted as fully qualified {NAME}; proposition text is otherwise source-derived"},
        ],
        "ast_inventory_sha256": sha(AST), "scope_inventory_sha256": sha(SCOPE),
        "validated": False, "Lean_started": False,
    }
    outputs = {
        "Theorems/Thm_OAI_PiExponent_exists_parameters.lean": statement,
        "Solutions/Sol_OAI_PiExponent_exists_parameters.lean": solution,
        "SnapshotOriginal.lean": source_snapshot,
        "SnapshotGenerated.lean": generated_snapshot_base,
        "SnapshotGeneratedWithRefs.lean": generated_with_refs,
        "academic-metadata.json": json.dumps(metadata, ensure_ascii=False, indent=2) + "\n",
        "source-ast-witness.json": json.dumps(ast_witness, ensure_ascii=False, indent=2) + "\n",
    }
    external_inputs = [SOURCE, PORT, AST, SCOPE, CORE, RUNTIME, STRUCTURAL, PROVIDER_MANIFEST,
                       PROVIDER_SOURCE, PARAMS_OLEAN, CHILD_CERT, CHILD_SOURCE, CHILD_OLEAN,
                       CHILD_TYPE, CHILD_REFS, CONTEXT, PREFLIGHT, PRODUCER, CONSUMER]
    input_hashes = {rel(path): sha(path) for path in external_inputs}
    if input_hashes[rel(STRUCTURAL)] != STRUCTURAL_SHA:
        raise ValueError("Published Parameters structural certificate hash differs")
    if input_hashes[rel(PARAMS_OLEAN)] != PARAMS_OLEAN_SHA:
        raise ValueError("Parameters first-search OLean hash differs")
    if input_hashes[rel(CHILD_CERT)] != CHILD_CERT_SHA or input_hashes[rel(CHILD_OLEAN)] != CHILD_OLEAN_SHA:
        raise ValueError("c2 child validation/OLean bytes differ")
    child_doc, structural_doc = read(CHILD_CERT), read(STRUCTURAL)
    child_owner = child_doc.get("actual_module_owner", {})
    if (child_doc.get("validated") is not True or child_doc.get("Std3_only") is not True
            or child_doc.get("module") != CHILD_MODULE or child_owner.get("kind") != "ImportedModule"
            or child_owner.get("module") != CHILD_MODULE or child_doc.get("child_olean_sha256") != CHILD_OLEAN_SHA):
        raise ValueError("c2 actual child certificate is not the pinned Std3 imported theorem")
    if (structural_doc.get("validated") is not True or structural_doc.get("types_equal") is not True
            or structural_doc.get("definition_values_equal") is not True
            or structural_doc.get("axioms_equal_and_std3") is not True
            or structural_doc.get("platform_module") != DEF_MODULE
            or structural_doc.get("family_root") != DEF_NAME):
        raise ValueError("Published Parameters structural certificate is incomplete")
    compared_names = structural_doc.get("compared_names")
    if not isinstance(compared_names, list):
        raise ValueError("Parameters certificate lacks its exact compared CI name list")
    extracted_names = [x if isinstance(x, str) else x.get("name")
                       for x in compared_names if isinstance(x, (str, dict))]
    if not extracted_names or any(not isinstance(x, str) for x in extracted_names):
        raise ValueError("Parameters CI name inventory is malformed")
    params_ci_names = sorted(set(extracted_names))
    provider_data = structural_doc.get("provider_preflight", {})
    if (provider_data.get("actual_module_identity") != DEF_MODULE
            or Path(provider_data.get("output_olean", "")).as_posix() != rel(PARAMS_OLEAN)
            or provider_data.get("output_olean_sha256") != PARAMS_OLEAN_SHA
            or structural_doc.get("provider_source_sha256") != sha(PROVIDER_SOURCE)
            or structural_doc.get("provider_manifest_sha256") != sha(PROVIDER_MANIFEST)):
        raise ValueError("Parameters structural certificate does not bind its first-search provider OLean")
    runtime = read(RUNTIME)
    runtime_sha = sha(RUNTIME)
    if runtime_sha != "ab61393780988c65493c5969dccfce9a5e88b18a3866e6ed65e2c89ca36fc9ef":
        raise ValueError("Pinned Lean runtime changed")
    files = ["Theorems/Thm_OAI_PiExponent_exists_parameters.lean",
             "Solutions/Sol_OAI_PiExponent_exists_parameters.lean", "SnapshotOriginal.lean",
             "SnapshotGeneratedWithRefs.lean"]
    imports = [
        [DEF_MODULE, CHILD_MODULE, "Mathlib"],
        [DEF_MODULE, CHILD_MODULE, "Mathlib"],
        ["Lean", SOURCE_MODULE],
        ["Lean", DEF_MODULE, CHILD_MODULE, "Mathlib"],
    ]
    modes = ["modecheck", "modecheck", "modecheck", "modecheck"]
    manifest = {
        "schema_version": 1, "artifact_kind": "ap5-p1-source017-parameters-node-staging",
        "source_commit": COMMIT, "source_module": SOURCE_MODULE, "source_path": workspace_rel(SOURCE),
        "source_sha256": sha(SOURCE), "port_path": workspace_rel(PORT), "port_sha256": sha(PORT),
        "node": "OAI.NumberTheory.PiExponent.Approximation.Parameters:4839",
        "theorem_name": NAME, "module": MODULE,
        "preamble": preamble, "formal_statement": formal_statement,
        "compiled_statement_bytes_must_equal_preamble_plus_formal_statement": True,
        "definition_dependency": {"module": DEF_MODULE, "name": DEF_NAME,
            "platform_id": "fc417d07-f2ff-44a4-9f9b-c476904bc720",
            "structural_certificate": rel(STRUCTURAL), "structural_certificate_sha256": sha(STRUCTURAL),
            "first_search_olean": rel(PARAMS_OLEAN), "first_search_olean_sha256": sha(PARAMS_OLEAN)},
        "parameter_ci_names": params_ci_names,
        "allowed_project_proof_references": sorted(set(params_ci_names) | {CHILD, HELPER}),
        "proved_child_dependency": {"module": CHILD_MODULE, "name": CHILD,
            "actual_child_certificate": rel(CHILD_CERT), "actual_child_certificate_sha256": sha(CHILD_CERT),
            "olean": rel(CHILD_OLEAN), "olean_sha256": sha(CHILD_OLEAN),
            "child_type": rel(CHILD_TYPE), "child_type_sha256": sha(CHILD_TYPE),
            "child_proof_references": rel(CHILD_REFS), "child_proof_references_sha256": sha(CHILD_REFS)},
        "inline_helper": HELPER,
        "statement": workspace_rel(STAGE / "Theorems/Thm_OAI_PiExponent_exists_parameters.lean"),
        "statement_sha256": sha_bytes(statement.encode()),
        "solution": workspace_rel(STAGE / "Solutions/Sol_OAI_PiExponent_exists_parameters.lean"),
        "solution_sha256": sha_bytes(solution.encode()),
        "snapshot_original": workspace_rel(STAGE / "SnapshotOriginal.lean"),
        "snapshot_generated": workspace_rel(STAGE / "SnapshotGenerated.lean"),
        "snapshot_generated_with_refs": workspace_rel(STAGE / "SnapshotGeneratedWithRefs.lean"),
        "academic_metadata": workspace_rel(STAGE / "academic-metadata.json"),
        "academic_metadata_sha256": sha_bytes(outputs["academic-metadata.json"].encode()),
        "source_ast_witness": workspace_rel(STAGE / "source-ast-witness.json"),
        "source_ast_witness_sha256": sha_bytes(outputs["source-ast-witness.json"].encode()),
        "input_hashes": input_hashes,
        "runtime_sha256": runtime_sha,
        "imports": {file: imp for file, imp in zip(files, imports, strict=True)},
        "compiler_manifests": {f"c{i}.json": f"verification/ap5/p1/c{i}.json" for i in range(1, 5)},
        "timeout_seconds_per_file": 300,
        "validated": False, "submission_ready": False, "proposal_status": "Draft",
    }
    generated = {"manifest.json": json.dumps(manifest, ensure_ascii=False, indent=2) + "\n", **outputs}
    for i, (filename, import_list, mode) in enumerate(zip(files, imports, modes, strict=True), 1):
        path = STAGE / filename
        if filename.startswith("Theorems/") or filename.startswith("Solutions/"):
            out_bytes = generated[filename].encode("utf-8")
        else:
            out_bytes = generated[filename].encode("utf-8")
        cdoc = {
            "schema_version": 1, "artifact_kind": "ap5-p1-bounded-compiler-manifest",
            "output": workspace_rel(path), "output_sha256": sha_bytes(out_bytes), "imports": import_list,
            **({"source_components": [{"source_module": SOURCE_MODULE}],
                "snapshot_sha256": {"SnapshotOriginal.lean": sha_bytes(outputs["SnapshotOriginal.lean"].encode())}}
               if filename == "SnapshotOriginal.lean" else {}),
            "input_hashes": input_hashes, "node": manifest["node"], "theorem_name": NAME,
            "source_commit": COMMIT, "runtime_sha256": runtime_sha,
            "mode": mode, "timeout_seconds": 300, "Lean_started": False, "validated": False,
            "submission_ready": False,
        }
        generated[f"c{i}.json"] = json.dumps(cdoc, ensure_ascii=False, indent=2) + "\n"
    manifest["compiler_manifest_sha256"] = {
        f"c{i}.json": sha_bytes(generated[f"c{i}.json"].encode()) for i in range(1, 5)}
    generated["manifest.json"] = json.dumps(manifest, ensure_ascii=False, indent=2) + "\n"
    commands = {}
    for i, filename in enumerate(files, 1):
        relative = filename.replace("\\", "/")
        commands[filename] = ("python scripts/preflight_staged_module.py ap5/p1/" + relative
            + f" --root ap5/p1 --imports-manifest ap5/p1/c{i}.json --timeout-seconds 300")
    file_hashes = {name: sha_bytes(data.encode("utf-8")) for name, data in generated.items()}
    prep = {
        "schema_version": 1, "artifact_kind": "ap5-p1-repeatable-preparation",
        "stage": "verification/ap5/p1", "node": manifest["node"], "theorem_name": NAME,
        "producer": rel(PRODUCER), "producer_sha256": sha(PRODUCER),
        "strict_consumer": rel(CONSUMER), "strict_consumer_sha256": sha(CONSUMER),
        "manifest_sha256": file_hashes["manifest.json"], "input_hashes": input_hashes,
        "file_hashes": file_hashes,
        "compile_manifests": {filename: {"manifest": f"verification/ap5/p1/c{i}.json",
            "manifest_sha256": file_hashes[f"c{i}.json"], "timeout_seconds": 300}
            for i, filename in enumerate(files, 1)},
        "compile_commands": commands,
        "preamble": preamble, "formal_statement": formal_statement,
        "compiled_statement_assembly_sha256": sha_bytes((preamble + formal_statement).encode()),
        "exact_compiled_statement_bytes_guard": True,
        "single_compiler_sequential": True,
        "order": files, "single_compiler_sequential": True,
        "Lean_started": False, "API_used": False, "validated": False,
        "submission_ready": False, "proposal_status": "Draft",
    }
    generated["preparation.json"] = json.dumps(prep, ensure_ascii=False, indent=2) + "\n"
    return generated


def write_outputs(generated: dict) -> None:
    # Never replace evidence after compilation has started.
    evidence = list(STAGE.glob("*.preflight.json"))
    if evidence:
        raise ValueError("Preflight evidence already exists; preserve it and use --check-only")
    for name, text in generated.items():
        path = STAGE / name
        path.parent.mkdir(parents=True, exist_ok=True)
        data = text.encode("utf-8")
        if path.is_file() and path.read_bytes() == data:
            continue
        path.write_bytes(data)


def check_outputs(generated: dict) -> dict:
    mismatches = []
    for name, text in generated.items():
        path = STAGE / name
        if not path.is_file() or path.read_bytes() != text.encode("utf-8"):
            mismatches.append(name)
    if mismatches:
        raise ValueError("Staged files differ from deterministic reconstruction: " + ", ".join(mismatches))
    return {"checked_files": len(generated), "all_hashes_match": True,
            "Lean_started": False, "API_used": False, "validated": False}


def check_runner_manifests(generated: dict) -> dict:
    checked = {}
    for index, filename in enumerate((
            "Theorems/Thm_OAI_PiExponent_exists_parameters.lean",
            "Solutions/Sol_OAI_PiExponent_exists_parameters.lean",
            "SnapshotOriginal.lean", "SnapshotGeneratedWithRefs.lean"), 1):
        manifest = json.loads(generated[f"c{index}.json"])
        source = runner.source_path(f"ap5/p1/{filename}")
        runner.verify_manifest_inputs(manifest)
        source_certificate = runner.verify_source_certificate(source, manifest)
        imports = runner.certified_imports(source, manifest)
        checked[filename] = {
            "manifest_inputs_checked": True,
            "source_certificate": source_certificate,
            "certified_imports": imports,
        }
    return checked


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--prepare", action="store_true")
    group.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    generated = stage_files()
    if args.prepare:
        write_outputs(generated)
    result = check_outputs(generated)
    result["runner_manifest_checks"] = check_runner_manifests(generated)
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
