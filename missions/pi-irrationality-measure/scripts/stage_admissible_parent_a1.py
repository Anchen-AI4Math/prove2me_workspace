"""Repeatable pure-Python staging for the ap6/a1 source017 admissible parent.

This stages a modecheck-only target comparator and the source-derived, sorry-free
solution. It does not start Lean or contact the platform.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

import preflight_staged_module as runner

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
V = TASK / "verification"
STAGE = V / "ap6" / "a1" / "source017e"
NAME = "OAI.PiExponent.exists_admissible_parameters_source017"
SOURCE_NAME = "OAI.PiExponent.exists_admissible_parameters"
SOURCE_MODULE = "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters"
DIM_SOURCE_MODULE = "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension"
COMMIT = "adc7f1241b42e322a6451854ab7e4b4c146bf78a"
SOURCE = TASK / "port/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleParameters.lean"
DIM_SOURCE = TASK / "port/lean/OAI/NumberTheory/PiExponent/LocalAlgebra/Dimension.lean"
AST = V / "ast-unit-inventory.json"
SCOPE = V / "ast-scope-inventory.json"
GRAPH = V / "decl_graph.jsonl"
FRONTIER = V / "ap6/a1/frontier.json"
OVERRIDES = TASK / "platform/source-theorem-name-overrides.json"
CORE = V / "TypeOnlyTheoremSnapshotCore.inc"
PRODUCER = Path(__file__).resolve()
CONSUMER = TASK / "scripts/certify_admissible_parent_a1_existing.py"
PREFLIGHT = TASK / "scripts/preflight_staged_module.py"
CONTEXT = TASK / "scripts/validate_namespace_context_providers.py"

DEF_PARAMS = "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Parameters"
DEF_ADMISSIBLE = "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_AdmissibleParameters"
DEF_WEIGHT = "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_WeightSeparation"
DEF_DIMENSION = "Definitions.Def_OAI_NumberTheory_PiExponent_LocalAlgebra_Dimension"
WEIGHT_FULL_CERT = V / "ap2/complete-validation.json"
DIMENSION_KERNEL_CERT = V / "provider-nodes-preview/OAI_PiExponent_exists_dimension_margin/dimension-margin-publication-v2/validation.json"

CHILDREN = [
    {"role": "uniform_weight_error_margin", "module": "Theorems.Thm_OAI_PiExponent_exists_uniform_weight_error_margin",
     "name": "OAI.PiExponent.exists_uniform_weight_error_margin",
     "certificate": V / "ap6/c1/actual-child-validation.json",
     "olean": V / "staged-build/lib/lean/Theorems/Thm_OAI_PiExponent_exists_uniform_weight_error_margin.olean",
     "expected_certificate_sha256": "0bf16c94577a5ca3aff77a243b0e77e5ee5a0fa44db286f6d72d65b37dd1e880",
     "provided_names": ["OAI.PiExponent.exists_weight_error_margin",
                        "OAI.PiExponent.reciprocal_sum_le_common_bound"]},
    {"role": "minimum_weight", "module": "Theorems.Thm_OAI_PiExponent_exists_minimum_weight",
     "name": "OAI.PiExponent.exists_minimum_weight",
     "certificate": V / "ap6/c2/actual-child-validation.json",
     "olean": V / "staged-build/lib/lean/Theorems/Thm_OAI_PiExponent_exists_minimum_weight.olean",
     "expected_certificate_sha256": "5c6979735cbefff9fb4d81c4b71a139bb3ad56b557f01485ece66523100a85fd",
     "provided_names": []},
    {"role": "dimension_margin", "module": "Theorems.Thm_OAI_PiExponent_exists_dimension_margin",
     "name": "OAI.PiExponent.exists_dimension_margin",
     "certificate": V / "ap6/c3e/actual-child-validation.json",
     "olean": V / "staged-build/lib/lean/Theorems/Thm_OAI_PiExponent_exists_dimension_margin.olean",
     "expected_certificate_sha256": "fe5ca19cb7bbaa36af50b8373b22af32c020cea39a2a63044ae724d09bf6c908",
     "provided_names": ["OAI.PiExponent.tendsto_nat_add_one_div_pow",
                        "OAI.PiExponent.tendsto_pow_div_nat_add_one",
                        "OAI.PiExponent.dimensionK_div_W_le",
                        "OAI.PiExponent.dimensionV_geometric_lower",
                        "OAI.PiExponent.dimension_error_le",
                        "OAI.PiExponent.tendsto_dimension_error_majorant",
                        "OAI.PiExponent.tendsto_dimension_collision"]},
    {"role": "normalized_successive_approximations",
     "module": "Theorems.Thm_OAI_PiExponent_exists_normalized_successive_approximations",
     "name": "OAI.PiExponent.exists_normalized_successive_approximations",
     "certificate": V / "ap6/c4e/actual-child-validation.json",
     "olean": V / "staged-build/lib/lean/Theorems/Thm_OAI_PiExponent_exists_normalized_successive_approximations.olean",
     "expected_certificate_sha256": "e955c416478476a7da743c230351daef5c55fe3c09786ce0a11831c47f2fb0e1",
     "provided_names": []},
    {"role": "parameters", "module": "Theorems.Thm_OAI_PiExponent_exists_parameters",
     "name": "OAI.PiExponent.exists_parameters",
     "certificate": V / "ap6/c5/actual-child-validation.json",
     "olean": V / "staged-build/lib/lean/Theorems/Thm_OAI_PiExponent_exists_parameters.olean",
     "expected_certificate_sha256": "db62acc900000183455f7b2d28c8758f2f280bd8329efd6dde5db2663e160f31",
     "provided_names": ["OAI.PiExponent.exists_eta_preserving_exponent_gap"]},
    {"role": "small_rational_sigma", "module": "Theorems.Thm_OAI_PiExponent_exists_small_rational_sigma",
     "name": "OAI.PiExponent.exists_small_rational_sigma",
     "certificate": V / "ap4/c3/actual-child-validation.json",
     "olean": V / "staged-build/lib/lean/Theorems/Thm_OAI_PiExponent_exists_small_rational_sigma.olean",
     "expected_certificate_sha256": None,
     "provided_names": []},
]

DEF_INPUTS = [
    {"module": DEF_PARAMS,
     "manifest": V / "providers-complete-preview/all-shared-safe-leaves/Definitions/Def_OAI_NumberTheory_PiExponent_Approximation_Parameters.manifest.json",
     "certificate": V / "providers-complete-preview/all-shared-safe-leaves/snapshots/Def_OAI_NumberTheory_PiExponent_Approximation_Parameters/provider-validation-structural.json",
     "publication": V / "providers-complete-preview/all-shared-safe-leaves/validation/Def_OAI_NumberTheory_PiExponent_Approximation_Parameters/publication.json",
     "olean": V / "staged-build/lib/lean/Definitions/Def_OAI_NumberTheory_PiExponent_Approximation_Parameters.olean"},
    {"module": DEF_ADMISSIBLE,
     "manifest": V / "ap2/s/Definitions/Def_OAI_NumberTheory_PiExponent_Approximation_AdmissibleParameters.manifest.json",
     "certificate": V / "ap2/s/snapshots/Def_OAI_NumberTheory_PiExponent_Approximation_AdmissibleParameters/provider-validation-structural.json",
     "publication": V / "ap2/publication/Def_OAI_NumberTheory_PiExponent_Approximation_AdmissibleParameters/publication.json",
     "olean": V / "staged-build/lib/lean/Definitions/Def_OAI_NumberTheory_PiExponent_Approximation_AdmissibleParameters.olean"},
    {"module": DEF_WEIGHT,
     "manifest": V / "ap2/s/Definitions/Def_OAI_NumberTheory_PiExponent_Approximation_WeightSeparation.manifest.json",
     "certificate": WEIGHT_FULL_CERT,
     "publication": V / "ap2/publication/Def_OAI_NumberTheory_PiExponent_Approximation_WeightSeparation/publication.json",
     "olean": V / "staged-build/lib/lean/Definitions/Def_OAI_NumberTheory_PiExponent_Approximation_WeightSeparation.olean"},
    {"module": DEF_DIMENSION,
     "manifest": V / "providers-complete-preview/all-shared-safe-leaves/Definitions/Def_OAI_NumberTheory_PiExponent_LocalAlgebra_Dimension.manifest.json",
     "certificate": V / "providers-complete-preview/all-shared-safe-leaves/validation/Def_OAI_NumberTheory_PiExponent_LocalAlgebra_Dimension/provider-validation-fast.json",
     "publication": V / "providers-complete-preview/all-shared-safe-leaves/validation/Def_OAI_NumberTheory_PiExponent_LocalAlgebra_Dimension/publication.json",
     "kernel_certificate": DIMENSION_KERNEL_CERT,
     "olean": V / "staged-build/lib/lean/Definitions/Def_OAI_NumberTheory_PiExponent_LocalAlgebra_Dimension.olean"},
]

SOURCE_HELPERS = [
    "OAI.PiExponent.interpolationSeparationConstant_pos",
    "OAI.PiExponent.weightErrorCoefficient_nonneg",
    "OAI.PiExponent.exists_initial_scale",
    "OAI.PiExponent.dimensionK_one_le",
    "OAI.PiExponent.dimensionW_pos",
    "OAI.PiExponent.dimensionV_pos",
    "OAI.PiExponent.dimension_volume",
    "OAI.PiExponent.dimension_volume_lt_one",
    "OAI.PiExponent.dimension_collision_identity",
]
HELPER_NAMES = SOURCE_HELPERS
LOCAL_NAMES = [
    "OAI.PiExponent.dimensionK_one_le",
    "OAI.PiExponent.dimensionW_pos",
    "OAI.PiExponent.dimensionV_pos",
    "OAI.PiExponent.dimension_volume",
    "OAI.PiExponent.dimension_volume_lt_one",
    "OAI.PiExponent.dimension_collision_identity",
    "OAI.PiExponent.interpolationSeparationConstant_pos",
    "OAI.PiExponent.weightErrorCoefficient_nonneg",
    "OAI.PiExponent.exists_initial_scale",
]
CHILD_CALLS = [
    "exists_parameters", "exists_dimension_margin", "exists_small_rational_sigma",
    "exists_uniform_weight_error_margin", "exists_normalized_successive_approximations",
    "exists_minimum_weight",
]


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


def walk(node):
    if isinstance(node, dict):
        yield node
        for value in node.values():
            yield from walk(value)
    elif isinstance(node, list):
        for value in node:
            yield from walk(value)


def module_row(tree, module: str):
    rows = [row for row in tree["modules"] if row.get("module") == module]
    if len(rows) != 1:
        raise ValueError(f"Expected one AST module row for {module}; got {len(rows)}")
    return rows[0]


def unit_row(tree, module: str, name: str):
    rows = [row for row in module_row(tree, module)["units"] if row.get("nameText") == name]
    if len(rows) != 1:
        raise ValueError(f"Expected one AST command {module}.{name}; got {len(rows)}")
    return rows[0]


def scope_row(tree, verified_name: str):
    rows = [row for row in walk(tree) if row.get("verified_name") == verified_name]
    if len(rows) != 1:
        raise ValueError(f"Expected one scope row for {verified_name}; got {len(rows)}")
    return rows[0]


def extract(data: bytes, row: dict) -> bytes:
    a, b = row["start"]["offset"], row["end"]["offset"]
    result = data[a:b]
    if len(result) == 0:
        raise ValueError("Empty AST source command")
    return result


def declaration_commands():
    ast, scopes = read(AST), read(SCOPE)
    target_row = unit_row(ast, SOURCE_MODULE, "exists_admissible_parameters")
    if sha(SOURCE) != module_row(ast, SOURCE_MODULE)["source_sha256"]:
        raise ValueError("Pinned admissible source bytes differ from AST module source")
    if sha(DIM_SOURCE) != module_row(ast, DIM_SOURCE_MODULE)["source_sha256"]:
        raise ValueError("Pinned dimension source bytes differ from AST module source")
    target_raw = extract(SOURCE.read_bytes(), target_row)
    commands = {}
    witness = []
    for name in ("interpolationSeparationConstant_pos", "weightErrorCoefficient_nonneg",
                 "exists_initial_scale"):
        row = unit_row(ast, SOURCE_MODULE, name)
        scope = scope_row(scopes, "OAI.PiExponent." + name)
        if scope.get("namespace") != "OAI.PiExponent" or scope.get("context_commands") != []:
            raise ValueError(f"Unexpected source scope for {name}")
        if scope.get("range", {}).get("start") != row.get("start") or scope.get("range", {}).get("end") != row.get("end"):
            raise ValueError(f"Source AST/scope ranges differ for {name}")
        raw = extract(SOURCE.read_bytes(), row)
        commands["OAI.PiExponent." + name] = raw.decode("utf-8")
        witness.append({"name": "OAI.PiExponent." + name, "module": SOURCE_MODULE,
                        "ast_unit": row, "scope": scope, "source_command_sha256": sha_bytes(raw)})
    dimension_context = None
    for name in ("dimensionK_one_le", "dimensionW_pos", "dimensionV_pos", "dimension_volume",
                 "dimension_volume_lt_one", "dimension_collision_identity"):
        row = unit_row(ast, DIM_SOURCE_MODULE, name)
        scope = scope_row(scopes, "OAI.PiExponent." + name)
        context = scope.get("context_commands", [])
        if scope.get("namespace") != "OAI.PiExponent":
            raise ValueError(f"Unexpected Dimension source scope for {name}")
        if dimension_context is None:
            dimension_context = context
        elif context != dimension_context:
            raise ValueError("Dimension helper source context changed within the AST closure")
        if scope.get("range", {}).get("start") != row.get("start") or scope.get("range", {}).get("end") != row.get("end"):
            raise ValueError(f"Dimension AST/scope ranges differ for {name}")
        raw = extract(DIM_SOURCE.read_bytes(), row)
        commands["OAI.PiExponent." + name] = raw.decode("utf-8")
        witness.append({"name": "OAI.PiExponent." + name, "module": DIM_SOURCE_MODULE,
                        "ast_unit": row, "scope": scope, "source_command_sha256": sha_bytes(raw)})
    if not dimension_context or [x.get("syntaxKind") for x in dimension_context] != [
            "Lean.Parser.Command.open", "Lean.Parser.Command.open"]:
        raise ValueError("Expected only the two exact source open commands in Dimension helper context")
    target_scope = scope_row(scopes, SOURCE_NAME)
    if target_scope.get("namespace") != "OAI.PiExponent" or target_scope.get("context_commands") != []:
        raise ValueError("Target source scope is not the exact top-level namespace scope")
    if target_scope.get("range", {}).get("start") != target_row.get("start") or target_scope.get("range", {}).get("end") != target_row.get("end"):
        raise ValueError("Target AST/scope range differs")
    if b"sorry" in target_raw:
        raise ValueError("Pinned original target unexpectedly contains sorry")
    target_text = target_raw.decode("utf-8")
    if not target_text.startswith("theorem exists_admissible_parameters"):
        raise ValueError("AST-selected source target binding changed")
    return target_text, commands, target_row, target_scope, witness, dimension_context


def read_children():
    result = []
    for row in CHILDREN:
        cert_bytes = row["certificate"].read_bytes()
        if row["expected_certificate_sha256"] and sha_bytes(cert_bytes) != row["expected_certificate_sha256"]:
            raise ValueError("Actual child certificate changed: " + row["role"])
        cert = json.loads(cert_bytes)
        owner = (cert.get("actual_child_owner") or cert.get("actual_child_main_owner")
                 or cert.get("actual_module_owner") or cert.get("child_owner") or {})
        if not owner and isinstance(cert.get("child_actual_owners"), dict):
            owner = cert["child_actual_owners"].get(row["name"], {})
        if cert.get("validated") is not True or cert.get("Std3_only") is False:
            raise ValueError("Actual child is not validated Std3: " + row["role"])
        if cert.get("module") != row["module"] or cert.get("theorem_name") != row["name"]:
            raise ValueError("Actual child module/name binding differs: " + row["role"])
        if owner.get("kind") != "ImportedModule" or owner.get("module") != row["module"]:
            raise ValueError("Actual child ownership differs: " + row["role"])
        if not row["olean"].is_file() or sha(row["olean"]) != cert.get("child_olean_sha256"):
            raise ValueError("Actual child first-search OLean differs: " + row["role"])
        if "provided_names" in cert:
            provided = cert["provided_names"]
            helper_rows = cert.get("helper_certificates", [])
        elif "actual_helper_certificates" in cert:
            helper_rows = cert["actual_helper_certificates"]
            provided = [item.get("name") for item in helper_rows if isinstance(item, dict)]
        else:
            # Some child consumers certify only the main theorem and publish no
            # helper catalog. No helper from those children is used by this source.
            helper_rows, provided = [], []
        if not isinstance(provided, list) or not isinstance(helper_rows, list):
            raise ValueError("Actual child helper catalog has an unsupported schema: " + row["role"])
        for item in helper_rows:
            child_owner_row = item.get("child_owner") if "child_owner" in item else item.get("child_owner")
            if not isinstance(child_owner_row, dict) or child_owner_row.get("kind") != "ImportedModule" \
                    or child_owner_row.get("module") != row["module"]:
                raise ValueError("Actual child helper owner differs: " + row["role"])
        if row["provided_names"] and provided != row["provided_names"]:
            raise ValueError("Actual child provided-name catalog differs: " + row["role"])
        result.append({**{k: rel(v) for k, v in row.items() if isinstance(v, Path)},
                       "role": row["role"], "module": row["module"], "name": row["name"],
                       "certificate_sha256": sha_bytes(cert_bytes), "certificate": cert,
                       "olean_sha256": sha(row["olean"]), "provided_names": provided})
    return result


def read_definitions():
    result = []
    for row in DEF_INPUTS:
        manifest, cert, publication, olean = row["manifest"], row["certificate"], row["publication"], row["olean"]
        kernel_cert = row.get("kernel_certificate")
        if not (manifest.is_file() and cert.is_file() and publication.is_file() and olean.is_file()
                and (kernel_cert is None or kernel_cert.is_file())):
            raise ValueError("Published definition evidence/OLean is missing: " + row["module"])
        m, c, pub = read(manifest), read(cert), read(publication)
        if m.get("platform_module") != row["module"]:
            raise ValueError("Published definition manifest binding differs: " + row["module"])
        if pub.get("last_publish_verdict", {}).get("body", {}).get("status") != "PUBLISHED":
            raise ValueError("Definition publication record is not PUBLISHED: " + row["module"])
        if row["module"] in (DEF_PARAMS, DEF_ADMISSIBLE):
            if c.get("validated") is not True or c.get("types_equal") is not True:
                raise ValueError("Structural definition certificate is incomplete: " + row["module"])
        elif row["module"] == DEF_WEIGHT:
            source_record = c.get("provider_manifests", {}).get(
                "OAI.NumberTheory.PiExponent.Approximation.WeightSeparation", {})
            if (c.get("validated") is not True or c.get("types_equal") is not True
                    or c.get("full_definition_values_equal") is not True or c.get("Std3_only") is not True
                    or source_record.get("platform_module") != row["module"]
                    or (TASK / source_record.get("path", "")).resolve() != manifest.resolve()
                    or source_record.get("sha256") != sha(manifest)):
                raise ValueError("WeightSeparation full source/generated CI certificate is incomplete")
        else:
            if (c.get("validated") is not True or c.get("platform_module") != row["module"]
                    or c.get("snapshot_comparison", {}).get("types_equal") is not True
                    or c.get("snapshot_comparison", {}).get("values_equal") is not True
                    or c.get("snapshot_comparison", {}).get("axioms_equal_and_std3") is not True):
                raise ValueError("Dimension actual provider kernel certificate is incomplete")
            kc = read(kernel_cert)
            if (kc.get("validated") is not True or kc.get("kernel_types_equal") is not True
                    or kc.get("seven_public_inline_kernel_types_equal") is not True
                    or kc.get("Std3_only") is not True
                    or kc.get("definition", {}).get("platform_module") != row["module"]
                    or kc.get("definition", {}).get("output_olean_sha256") != sha(olean)):
                raise ValueError("Dimension proof-node kernel certificate is incomplete or mismatched")
        selected_ids = m.get("selected_units")
        source_mod = m.get("source_module")
        if not isinstance(selected_ids, list) or not isinstance(source_mod, str):
            raise ValueError("Published definition manifest has no selected source-unit catalog")
        source_ast_module = module_row(read(AST), source_mod)
        units_by_offset = {unit["start"]["offset"]: unit for unit in source_ast_module["units"]}
        declared_names = set()
        for selected_id in selected_ids:
            if not isinstance(selected_id, str) or ":" not in selected_id:
                raise ValueError("Published definition selected-unit identity is malformed")
            offset = int(selected_id.rsplit(":", 1)[1])
            unit = units_by_offset.get(offset)
            if unit is None:
                raise ValueError("Published selected source unit is absent from exact AST inventory")
            declared_names.update(unit.get("graph_names", []))
        if declared_names & set(SOURCE_HELPERS):
            raise ValueError("Published Definition and inlined source helper names collide")
        result.append({"module": row["module"], "manifest": rel(manifest), "manifest_sha256": sha(manifest),
                       "certificate": rel(cert), "certificate_sha256": sha(cert),
                       "publication": rel(publication), "publication_sha256": sha(publication),
                       **({"kernel_certificate": rel(kernel_cert), "kernel_certificate_sha256": sha(kernel_cert)}
                          if kernel_cert else {}),
                       "declared_names": sorted(declared_names),
                       "olean": rel(olean), "olean_sha256": sha(olean)})
    return result


def graph_row(name: str):
    found = []
    for line in GRAPH.read_text(encoding="utf-8").splitlines():
        row = json.loads(line)
        if row.get("name") == name:
            found.append(row)
    if len(found) != 1:
        raise ValueError(f"Expected one declaration graph row for {name}; got {len(found)}")
    return found[0]


def inline_helper_module(commands: dict) -> str:
    ordered = [
        "OAI.PiExponent.dimensionK_one_le",
        "OAI.PiExponent.dimensionW_pos",
        "OAI.PiExponent.dimensionV_pos",
        "OAI.PiExponent.dimension_volume",
        "OAI.PiExponent.dimension_volume_lt_one",
        "OAI.PiExponent.dimension_collision_identity",
        "OAI.PiExponent.interpolationSeparationConstant_pos",
        "OAI.PiExponent.weightErrorCoefficient_nonneg",
        "OAI.PiExponent.exists_initial_scale",
    ]
    dim_body = "\n\n".join(commands[name].rstrip() for name in ordered[:6])
    source_body = "\n\n".join(commands[name].rstrip() for name in ordered[6:])
    return ("namespace OAI\nnamespace PiExponent\n\nnoncomputable section\n"
            "open Filter\nopen scoped Topology\n\n" + dim_body
            + "\n\nend\n\n" + source_body + "\n\nend PiExponent\nend OAI\n")


def fully_qualified_solution(target_text: str) -> tuple[str, list[dict]]:
    solution = target_text.replace("theorem exists_admissible_parameters", "theorem solution", 1)
    rewrites = []
    pairs = [
        (":= exists_parameters nu hnu", ":= OAI.PiExponent.exists_parameters nu hnu"),
        (":= exists_dimension_margin", ":= OAI.PiExponent.exists_dimension_margin"),
        (":=\r\n    exists_small_rational_sigma", ":=\r\n    OAI.PiExponent.exists_small_rational_sigma"),
        (":= exists_uniform_weight_error_margin", ":= OAI.PiExponent.exists_uniform_weight_error_margin"),
        (":=\r\n    exists_normalized_successive_approximations", ":=\r\n    OAI.PiExponent.exists_normalized_successive_approximations"),
        (":=\r\n    exists_minimum_weight", ":=\r\n    OAI.PiExponent.exists_minimum_weight"),
    ]
    for before, after in pairs:
        count = solution.count(before)
        if count != 1:
            raise ValueError(f"Expected exactly one source child call to rewrite: {before!r}; got {count}")
        solution = solution.replace(before, after, 1)
        rewrites.append({"source_call": before.strip(), "qualified_call": after.strip(), "occurrences": count})
    return solution, rewrites


def stage_files():
    target_text, commands, target_row, target_scope, helper_witness, dimension_context = declaration_commands()
    frontier = read(FRONTIER)
    if (frontier.get("source_name") != SOURCE_NAME or frontier.get("public_name") != NAME
            or frontier.get("source_sha256") != sha(SOURCE)
            or frontier.get("source_commit") != COMMIT):
        raise ValueError("ap6/a1 frozen frontier does not match exact source/name binding")
    override_rows = read(OVERRIDES)["planned_overrides"]
    override = [row for row in override_rows if row.get("source_name") == SOURCE_NAME]
    if len(override) != 1 or override[0].get("public_name") != NAME:
        raise ValueError("Source017 name override differs from the frozen target")
    # Convert the source target to a statement-only comparator. It is never emitted.
    proof_pos = target_text.find(":= by")
    if proof_pos < 0:
        raise ValueError("Cannot locate exact source target proof boundary")
    target_head = target_text[:proof_pos].rstrip()
    formal_statement = target_head.replace("theorem exists_admissible_parameters",
                                           "theorem " + NAME, 1) + " := by\n  sorry\n"
    preamble = "".join(f"import {module}\n" for module in [DEF_ADMISSIBLE, "Mathlib"]) + "\n"
    target_file = preamble + formal_statement
    helper_module = inline_helper_module(commands)
    solution_text, call_rewrites = fully_qualified_solution(target_text)
    imports = [DEF_PARAMS, DEF_ADMISSIBLE, DEF_WEIGHT, DEF_DIMENSION,
               *(row["module"] for row in CHILDREN), "Mathlib"]
    solution_preamble = "".join(f"import {module}\n" for module in imports) + "\n"
    solution_file = (solution_preamble + helper_module + "\nopen OAI.PiExponent\n\n" + solution_text
                    + "\n\n#print axioms solution\n")
    source_snapshot = ("import Lean\nimport " + SOURCE_MODULE + "\n\n"
        + CORE.read_text(encoding="utf-8").rstrip() + "\n\nset_option pp.universes true\n"
        + "set_option pp.fullNames true\nset_option pp.explicit true\n"
        + "run_meta do\n  PiExponentInterfaceSnapshot.exportSnapshot #["
        + ", ".join(f"`{name}" for name in [*HELPER_NAMES, SOURCE_NAME])
        + "] \"missions/pi-irrationality-measure/verification/ap6/a1/source017e/source-type.json\"\n"
        + "\n".join(f"#print axioms {name}" for name in [*SOURCE_HELPERS, SOURCE_NAME]) + "\n")
    generated_base = ("import Lean\n" + solution_preamble + "\n" + helper_module
        + "\n" + formal_statement + "\nopen OAI.PiExponent\n\n" + solution_text
        + "\n\nopen Lean Meta\n\n" + CORE.read_text(encoding="utf-8").rstrip()
        + "\n\nset_option pp.universes true\nset_option pp.fullNames true\nset_option pp.explicit true\n"
        + "run_meta do\n  PiExponentInterfaceSnapshot.exportSnapshot #["
        + ", ".join(f"`{name}" for name in [*HELPER_NAMES, NAME, "solution"])
        + "] \"missions/pi-irrationality-measure/verification/ap6/a1/source017e/generated-type.json\"\n"
        + "\n".join(f"#print axioms {name}" for name in [*SOURCE_HELPERS, NAME, "solution"]) + "\n")
    ref_names = list(SOURCE_HELPERS)
    refs_source = (
        "\nopen Lean Meta in\nrun_meta do\n"
        "  let names : Array Lean.Name := #[" + ", ".join(f"`{name}" for name in [*ref_names, "solution"]) + "]\n"
        "  let env ← Lean.getEnv\n  let mut rows : Array Lean.Json := #[]\n"
        "  for name in names do\n"
        "    if (env.getModuleIdxFor? name).isSome then throwError \"a1 reference is not an OwnModule CI: {name}\"\n"
        "    let some ci := env.find? name | throwError \"missing a1 proof reference {name}\"\n"
        "    let value ← match ci with | .thmInfo t => pure t.value | _ => throwError \"a1 reference is not a theorem {name}\"\n"
        "    if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars || value.hasMVar || value.hasFVar || value.hasLooseBVars then throwError \"open a1 proof reference {name}\"\n"
        "    let axioms ← Lean.collectAxioms name\n"
        "    unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do throwError \"non-Std3 a1 proof reference {name}\"\n"
        "    let refs := fun (e : Lean.Expr) => (e.getUsedConstants.map Lean.Name.toString).qsort (fun a b => a < b)\n"
        "    rows := rows.push <| Lean.Json.mkObj [(\"name\", Lean.toJson name.toString), (\"kind\", Lean.toJson \"theorem\"), (\"levelParams\", Lean.toJson (ci.levelParams.map Lean.Name.toString)), (\"closedType\", Lean.toJson true), (\"closedValue\", Lean.toJson true), (\"typeRefs\", Lean.toJson (refs ci.type)), (\"valueRefs\", Lean.toJson (refs value)), (\"axioms\", Lean.toJson ((axioms.map Lean.Name.toString).qsort (fun a b => a < b))), (\"owner\", Lean.Json.mkObj [(\"kind\", Lean.toJson \"OwnModule\"), (\"module\", Lean.toJson env.mainModule.toString)])]\n"
        "  IO.FS.writeFile \"missions/pi-irrationality-measure/verification/ap6/a1/source017e/proof-references.json\" ((Lean.Json.mkObj [(\"schemaVersion\", Lean.toJson 1), (\"probeMainModule\", Lean.toJson env.mainModule.toString), (\"rows\", Lean.Json.arr rows)]).pretty)\n"
    )
    generated_with_refs = generated_base + refs_source
    source_children = read_children()
    definitions = read_definitions()
    graph_target = graph_row(SOURCE_NAME)
    if graph_target.get("kind") != "theorem" or graph_target.get("module") != SOURCE_MODULE:
        raise ValueError("Source declaration graph target ownership differs")
    expected_direct = sorted(graph_target.get("valueDeps", []))
    required_direct = sorted(frontier["direct_dimension_closure_from_source_ast"])
    if not set(required_direct).issubset(set(expected_direct)):
        raise ValueError("Frontier dimension closure is not included in the exact source target valueDeps")
    source_dependency_names = set(graph_target.get("typeDeps", [])) | set(graph_target.get("valueDeps", []))
    for helper in SOURCE_HELPERS:
        hrow = graph_row(helper)
        source_dependency_names.update(hrow.get("typeDeps", []))
        source_dependency_names.update(hrow.get("valueDeps", []))
    allowed_project_refs = sorted(source_dependency_names | set(SOURCE_HELPERS) | set(CHILD_CALLS))
    outputs = {
        "Theorems/Thm_OAI_PiExponent_exists_admissible_parameters_source017.lean": target_file,
        "Solutions/Sol_OAI_PiExponent_exists_admissible_parameters_source017.lean": solution_file,
        "SourceSnapshot.lean": source_snapshot,
        "SnapshotGeneratedWithRefs.lean": generated_with_refs,
        "academic-metadata.json": json.dumps({
            "tags": ["openai-pi-exponent-017", "number-theory", "rational-approximation"],
            "source_commit": COMMIT,
            "source_url": f"https://github.com/openai/math/blob/{COMMIT}/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleParameters.lean#L105-L220",
            "theorem_title": "Existence of admissible approximation parameters for pi",
            "natural_language_statement": "Given ν ∈ ℝ with ν > 2 and Λ,c ∈ ℝ with Λ > 0 and c > 0, suppose hbad: ∀ Q ∈ ℕ, ∃ p ∈ ℤ, ∃ q ∈ ℕ, Q ≤ q ∧ |π - p/q| ≤ q^(−ν). Then there exists a tuple in the published AdmissibleParameters structure, with ε > 0, m ≥ 1, normalized rational approximations, and the stated approximation, dimension, collision, and weight-error margins, including a positive minimum weight.\n\nDisplay formula: $$h_{\\mathrm{bad}} : \\forall Q \\in \\mathbb{N},\\; \\exists p \\in \\mathbb{Z}, q \\in \\mathbb{N},\\; Q \\le q \\land \\left|\\pi-\\frac{p}{q}\\right| \\le q^{-\\nu}.$$",
            "mathematical_role": "This theorem is the conditional construction step of the source argument. It turns the approximation hypothesis into witnesses for the published admissibility predicates; it does not assert that the hypothesis itself is true.",
            "explanation": "Choose the published Parameters using only ν > 2; the rational-approximation hypothesis hbad is used later to obtain the required approximation sequence. From the Parameters gap choose ε, then choose F0, a sufficiently large scale m, and a small rational σ. The dimension-margin and collision lemmas establish the geometric constraints, while the uniform error bound, normalized logarithmic approximations, threshold, and minimum-weight lemma supply the remaining witnesses in the published record.",
            "formalization_note": f"The source declaration {SOURCE_NAME} is exposed under the source017 name {NAME}.",
            "source_lines": [105, 220],
        }, ensure_ascii=False, indent=2) + "\n",
        "source-closure-witness.json": json.dumps({
            "schema_version": 1, "artifact_kind": "ap6-a1-source017-exact-ast-closure",
            "source_commit": COMMIT, "source_path": workspace_rel(SOURCE), "source_sha256": sha(SOURCE),
            "dimension_source_path": workspace_rel(DIM_SOURCE), "dimension_source_sha256": sha(DIM_SOURCE),
            "ast_unit_inventory_sha256": sha(AST), "ast_scope_inventory_sha256": sha(SCOPE),
            "decl_graph_sha256": sha(GRAPH), "frontier_sha256": sha(FRONTIER),
            "target": {"source_name": SOURCE_NAME, "public_name": NAME, "ast_unit": target_row,
                       "scope": target_scope, "raw_command_sha256": sha_bytes(target_text.encode())},
            "inline_source_helpers": helper_witness,
            "dimension_helpers_source_context": dimension_context,
            "direct_target_value_dependencies": expected_direct,
            "frontier_dimension_dependency_names": required_direct,
            "allowed_project_proof_references": allowed_project_refs,
            "target_call_renames": call_rewrites,
            "published_definitions": definitions,
            "actual_children": [{k: v for k, v in row.items() if k != "certificate"}
                                for row in source_children],
            "no_custom_parameter_definitions": True,
            "sorry_target_is_modecheck_only": True,
            "validated": False, "Lean_started": False, "API_used": False,
        }, ensure_ascii=False, indent=2) + "\n",
    }
    inputs = [SOURCE, DIM_SOURCE, AST, SCOPE, GRAPH, FRONTIER, OVERRIDES, CORE, PREFLIGHT, CONTEXT,
              PRODUCER, CONSUMER]
    for row in CHILDREN:
        inputs.extend([row["certificate"], row["olean"]])
        cert = read(row["certificate"])
        for relkey in ("child_type", "child_proof_references", "child_source"):
            value = cert.get(relkey)
            if isinstance(value, str):
                p = (ROOT / value).resolve()
                if p.is_file() and p.is_relative_to(TASK.resolve()):
                    inputs.append(p)
    for row in DEF_INPUTS:
        inputs.extend([row["manifest"], row["certificate"], row["publication"], row["olean"]])
        if row.get("kernel_certificate"):
            inputs.append(row["kernel_certificate"])
    inputs = list(dict.fromkeys(inputs))
    input_hashes = {rel(path): sha(path) for path in inputs}
    manifest = {
        "schema_version": 1, "artifact_kind": "ap6-a1-source017-admissible-parent-staging",
        "node": "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:4510",
        "source_commit": COMMIT, "source_module": SOURCE_MODULE, "source_name": SOURCE_NAME,
        "theorem_name": NAME, "module": "Theorems.Thm_OAI_PiExponent_exists_admissible_parameters_source017",
        "source_path": workspace_rel(SOURCE), "source_sha256": sha(SOURCE),
        "preamble": preamble, "formal_statement": formal_statement,
        "compiled_statement_bytes_must_equal_preamble_plus_formal_statement": True,
        "statement": workspace_rel(STAGE / "Theorems/Thm_OAI_PiExponent_exists_admissible_parameters_source017.lean"),
        "statement_sha256": sha_bytes(target_file.encode()),
        "solution": workspace_rel(STAGE / "Solutions/Sol_OAI_PiExponent_exists_admissible_parameters_source017.lean"),
        "solution_sha256": sha_bytes(solution_file.encode()),
        "definition_dependencies": definitions, "proved_child_dependencies": source_children,
        "allowed_project_proof_references": allowed_project_refs,
        "source_helpers_inlined": SOURCE_HELPERS,
        "target_comparator": {"sorry": True, "mode": "modecheck", "emit_olean": False,
                              "never_import_target_olean": True},
        "input_hashes": input_hashes,
        "runtime_sha256": sha(V / "lean-runtime.json"),
        "imports": {
            "Theorems/Thm_OAI_PiExponent_exists_admissible_parameters_source017.lean": [DEF_ADMISSIBLE, "Mathlib"],
            "Solutions/Sol_OAI_PiExponent_exists_admissible_parameters_source017.lean": imports,
            "SourceSnapshot.lean": ["Lean", SOURCE_MODULE],
            "SnapshotGeneratedWithRefs.lean": ["Lean", *imports],
        },
        "compiler_manifests": {f"c{i}.json": f"verification/ap6/a1/source017e/c{i}.json" for i in range(1, 5)},
        "timeout_seconds_per_file": 300, "proposal_status": "Draft",
        "validated": False, "submission_ready": False,
    }
    files = [
        "Theorems/Thm_OAI_PiExponent_exists_admissible_parameters_source017.lean",
        "Solutions/Sol_OAI_PiExponent_exists_admissible_parameters_source017.lean",
        "SourceSnapshot.lean", "SnapshotGeneratedWithRefs.lean",
    ]
    modes = ["modecheck"] * 4
    generated = {"manifest.json": json.dumps(manifest, ensure_ascii=False, indent=2) + "\n", **outputs}
    for i, filename in enumerate(files, 1):
        out = generated[filename].encode("utf-8")
        imports_for_file = manifest["imports"][filename]
        cdoc = {
            "schema_version": 1, "artifact_kind": "ap6-a1-bounded-compiler-manifest",
            "output": workspace_rel(STAGE / filename), "output_sha256": sha_bytes(out),
            "imports": imports_for_file, "input_hashes": input_hashes,
            "node": manifest["node"], "theorem_name": NAME, "source_commit": COMMIT,
            "runtime_sha256": manifest["runtime_sha256"], "mode": modes[i - 1],
            "timeout_seconds": 300, "Lean_started": False, "validated": False,
            "emit_olean": False, "submission_ready": False,
        }
        generated[f"c{i}.json"] = json.dumps(cdoc, ensure_ascii=False, indent=2) + "\n"
    manifest["compiler_manifest_sha256"] = {
        f"c{i}.json": sha_bytes(generated[f"c{i}.json"].encode()) for i in range(1, 5)}
    generated["manifest.json"] = json.dumps(manifest, ensure_ascii=False, indent=2) + "\n"
    stage_manifest = json.loads(generated["manifest.json"])
    stage_manifest_sha = sha_bytes(generated["manifest.json"].encode())
    commands = {}
    for i, filename in enumerate(files, 1):
        commands[filename] = ("python scripts/preflight_staged_module.py ap6/a1/source017e/" + filename
            + f" --root ap6/a1/source017e --imports-manifest ap6/a1/source017e/c{i}.json --timeout-seconds 300")
    generated["preparation.json"] = json.dumps({
        "schema_version": 1, "artifact_kind": "ap6-a1-source017-repeatable-preparation",
        "stage": rel(STAGE), "manifest_sha256": stage_manifest_sha,
        "producer": rel(PRODUCER), "producer_sha256": sha(PRODUCER),
        "strict_consumer": rel(CONSUMER), "strict_consumer_sha256": sha(CONSUMER),
        "input_hashes": input_hashes, "order": files, "compile_commands": commands,
        "preamble": preamble, "formal_statement": formal_statement,
        "compiled_statement_assembly_sha256": sha_bytes((preamble + formal_statement).encode()),
        "target_comparator_modecheck_only": True, "target_comparator_emits_olean": False,
        "single_compiler_sequential": True, "Lean_started": False, "API_used": False,
        "validated": False, "submission_ready": False, "proposal_status": "Draft",
    }, ensure_ascii=False, indent=2) + "\n"
    raw_json_outputs = {
        "SourceSnapshot.lean": "missions/pi-irrationality-measure/verification/ap6/a1/source017e/source-type.json",
        "SnapshotGeneratedWithRefs.lean": "missions/pi-irrationality-measure/verification/ap6/a1/source017e/generated-type.json",
    }
    for lean_file, literal in raw_json_outputs.items():
        resolved = (ROOT / literal).resolve()
        expected = (STAGE / ("source-type.json" if lean_file == "SourceSnapshot.lean" else "generated-type.json")).resolve()
        if resolved != expected or not resolved.is_relative_to(ROOT.resolve()):
            raise ValueError("Raw Lean JSON export path escapes or differs from its planned output")
        if literal not in generated[lean_file]:
            raise ValueError("Raw Lean JSON exporter does not name its planned output")
    refs_path = "missions/pi-irrationality-measure/verification/ap6/a1/source017e/proof-references.json"
    if refs_path not in generated["SnapshotGeneratedWithRefs.lean"]:
        raise ValueError("Proof-reference exporter path differs from planned output")
    return generated


def check_outputs(generated):
    mismatches = []
    for name, text in generated.items():
        path = STAGE / name
        if not path.is_file() or path.read_bytes() != text.encode("utf-8"):
            mismatches.append(name)
    if mismatches:
        raise ValueError("Staged ap6/a1 files differ from deterministic reconstruction: " + ", ".join(mismatches))
    return {"checked_files": len(generated), "all_hashes_match": True,
            "Lean_started": False, "API_used": False, "validated": False}


def check_runner_manifests(generated):
    rows = {}
    files = [
        "Theorems/Thm_OAI_PiExponent_exists_admissible_parameters_source017.lean",
        "Solutions/Sol_OAI_PiExponent_exists_admissible_parameters_source017.lean",
        "SourceSnapshot.lean", "SnapshotGeneratedWithRefs.lean",
    ]
    for i, filename in enumerate(files, 1):
        doc = json.loads(generated[f"c{i}.json"])
        source = runner.source_path(f"ap6/a1/source017e/{filename}")
        runner.verify_manifest_inputs(doc)
        source_cert = runner.verify_source_certificate(source, doc)
        imports = runner.certified_imports(source, doc)
        rows[filename] = {"source_certificate": source_cert, "certified_imports": imports}
    return rows


def write_outputs(generated):
    if any(STAGE.glob("*.preflight.json")):
        raise ValueError("Existing preflight evidence prevents staging overwrite; use --check-only")
    for name, text in generated.items():
        path = STAGE / name
        path.parent.mkdir(parents=True, exist_ok=True)
        data = text.encode("utf-8")
        if path.exists() and path.read_bytes() != data:
            raise ValueError("Existing ap6/a1 evidence would be overwritten: " + rel(path))
        if not path.exists():
            path.write_bytes(data)


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
    result["runner_manifest_checks"] = check_runner_manifests(generated)
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
