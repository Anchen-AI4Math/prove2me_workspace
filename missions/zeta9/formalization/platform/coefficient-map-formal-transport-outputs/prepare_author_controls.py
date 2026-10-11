"""Generate complete fresh-context checks from original headers/SOURCE templates."""
import ast
import json
from pathlib import Path
import re
import sys

import initialize_author as p


def literal(path, name):
    tree = ast.parse(path.read_text(encoding="utf-8"))
    for node in tree.body:
        if isinstance(node, ast.Assign) and any(isinstance(t, ast.Name) and t.id == name for t in node.targets):
            return ast.literal_eval(node.value)
    raise KeyError(name)


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    prep = p.load(p.OUT / "author-context-preparation.json")
    plan = p.load(p.OUT / "target-plan.json")
    generic = p.TASK / "verification/formalization-coefficient-map-parameter-summation-independent-2026-10-07/prepare_controls.py"
    META = literal(generic, "META").replace("import ParameterSummationIndependentAssertionsV1", "import OutputsPlatformAssertions")
    META = META.replace("import IndependentExprDagV3", "import OutputsPlatformExprDagV1").replace("independent_", "platform_author_")
    GENERATED = literal(generic, "GENERATED").replace("independent_", "platform_author_")
    contract = p.TASK / "verification/formalization-coefficient-map-formal-transport-outputs-independent-2026-10-07/prepare_controls.py"
    boundaries = literal(contract, "BOUNDARIES").replace("OutputsIndependentBoundary", "OutputsPlatformBoundary")
    boundary_names = literal(contract, "BOUNDARY_NAMES")
    assert len(boundary_names) == 9
    definitions = plan["all18_definition_controls_required"] + plan["additional_whole_definition_controls_required"]
    assert len(definitions) == len(set(definitions)) == 20
    headers = plan["native_all16_exact_headers"]
    assert len(headers) == 16
    PREFIX = """set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000
noncomputable section
open scoped BigOperators Matrix
open Finset Polynomial ZetaNine
open ZetaNine.CoefficientMap ZetaNine.CoefficientMapJet ZetaNine.CoefficientMapInjectivity
open ZetaNine.CoefficientMapPartialFractions ZetaNine.CoefficientMapFiniteSum
open ZetaNine.CoefficientMapConnection ZetaNine.CoefficientMapFormalTransportData
open ZetaNine.CoefficientMapAggregate ZetaNine.CoefficientMapMatrix
"""
    contexts = []
    for context in prep["contexts"]:
        tag = context["tag"]
        if tag not in ["d", "c", "f", "m"]:
            continue
        ctx = p.PROJECT / tag
        isproof = tag != "d"
        imports = "import Definitions.Def_ZetaNine_CoefficientMapFormalTransportOutputs\nimport Oracle.CoefficientMapFormalTransportOutputs\n"
        solution = next((row for row in context["math_sources"] if row["kind"].startswith("complete_solution")), None)
        if isproof:
            imports += "import " + solution["module"] + "\n"
        assertion = imports + PREFIX
        if isproof:
            assertion += "open ZetaNine.CoefficientMapFormalTransportOutputs\n"
        assertion += "namespace OutputsPlatformWhole\n"
        whole_names = []
        for i, name in enumerate(definitions):
            expected = name.replace("ZetaNine.", "OutputsPlatformOracle.", 1)
            local = "whole_" + str(i).zfill(2) + "_" + name.rsplit(".", 1)[-1]
            whole_names.append("OutputsPlatformWhole." + local)
            assertion += "theorem " + local + " : " + name + " = " + expected + " := by rfl\n"
        assertion += "end OutputsPlatformWhole\n"
        if isproof:
            assertion += boundaries
        p.write(ctx / "OutputsPlatformAssertions.lean", assertion)
        semantic = META + "run_meta do\n"
        if isproof:
            for row in headers:
                actual = row["name"]
                expected = actual.replace("ZetaNine.", "OutputsPlatformOracle.", 1)
                semantic += "  full `" + actual + ' "platform_author_actual_original_forall"\n'
                semantic += "  full `" + expected + ' "platform_author_fresh_native_original_forall"\n'
                semantic += "  wholeType `" + actual + " `" + expected + "\n"
            target = plan["targets"][["c", "f", "m"].index(tag)]["theorem_name"]
            semantic += '  full `solution "platform_author_actual_complete_solution"\n'
            semantic += "  wholeType `solution `" + target + "\n"
        for name, whole in zip(definitions, whole_names):
            expected = name.replace("ZetaNine.", "OutputsPlatformOracle.", 1)
            semantic += "  full `" + name + ' "platform_author_actual_whole_definition"\n'
            semantic += "  full `" + expected + ' "platform_author_fresh_native_whole_definition"\n'
            semantic += "  definitionKernel `" + name + " `" + expected + "\n"
            semantic += "  full `" + whole + ' "platform_author_whole_function_rfl"\n'
        if isproof:
            for name in boundary_names:
                semantic += "  full `OutputsPlatformBoundary." + name + ' "platform_author_actual_typed_boundary"\n'
        p.write(ctx / "OutputsPlatformSemantic.lean", semantic)
        modules = [row["module"] for row in context["math_sources"] if row["kind"] != "generic_lossless_recorder_SOURCE_no_math_object_reuse"] + ["OutputsPlatformAssertions"]
        generated = META + GENERATED + "run_meta do\n  completeActualModuleInventory [" + ", ".join("`" + name for name in modules) + "]\n"
        p.write(ctx / "OutputsPlatformGenerated.lean", generated)
        own = [row["module"] for row in context["math_sources"]] + ["OutputsPlatformAssertions", "OutputsPlatformSemantic", "OutputsPlatformGenerated"]
        resolver = "import OutputsPlatformGenerated\nimport OutputsPlatformSemantic\nimport OutputsPlatformExprDagValidationV1\nimport Lean\nopen Lean Meta\nset_option maxHeartbeats 0\nrun_meta do\n"
        resolver += "  let env ← getEnv\n  for name in env.header.moduleNames do\n    let file ← findOLean name\n    let real ← IO.FS.realPath file\n    IO.println (Json.mkObj [(\"kind\",Json.str \"actual_import_origin\"),(\"module\",Json.str name.toString),(\"chosen\",Json.str file.toString),(\"realPath\",Json.str real.toString)]).compress\n"
        for module in own:
            expected = str((ctx / "b/lib/lean" / (module.replace(".", "/") + ".olean")).resolve())
            resolver += "  let file ← findOLean `" + module + "\n  let real ← IO.FS.realPath file\n"
            resolver += "  let expected ← IO.FS.realPath (System.FilePath.mk " + json.dumps(expected) + ")\n"
            resolver += '  unless real == expected do throwError "Own actual object origin mismatch: ' + module + '"\n'
            resolver += '  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "' + module + '"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress\n'
        p.write(ctx / "OutputsPlatformResolver.lean", resolver)
        rows = [{"module": "OutputsPlatform" + name, "path": "OutputsPlatform" + name + ".lean", "binding": p.bind(ctx / ("OutputsPlatform" + name + ".lean"))} for name in ["Assertions", "Semantic", "Generated", "Resolver"]]
        contexts.append({"tag": tag, "proof_context": isproof, "rows": rows, "all16_original_forall_pairs": 16 if isproof else 0,
                         "wrapper_complete_type_pairs": 1 if isproof else 0, "whole_definition_pairs": 20, "whole_function_rfl": 20,
                         "typed_boundaries": 9 if isproof else 0, "all_actual_math_modules": modules, "actual_own_modules": own})
    p.dump(p.OUT / "author-control-preparation.json", {"contexts": contexts, "whole_definitions": definitions, "original16_fullheaders": headers,
         "boundaries": boundary_names, "generic_recorder_SOURCE": p.bind(generic), "native_verified_boundary_SOURCE": p.bind(contract),
         "mathematical_proof_objects_reused": False, "raw_Expr_alias_differences_never_erased": True, "complete_generated_helper_values_and_inferType_required": True,
         "every_actual_module_declaration_Std3_required": True, "Lean_calls": 0, "API_calls": 0, "author_PASS_claimed": False})
    print("Four isolated controls prepared: 20 whole native definition comparisons/rfl; each proof16 original forall+wrapper/9bounds/all actual helpers and import origins.")


if __name__ == "__main__":
    main()
