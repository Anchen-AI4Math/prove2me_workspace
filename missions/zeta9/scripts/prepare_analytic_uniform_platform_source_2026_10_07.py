"""SOURCE-only platform transplant of complete actual weighted analytic proofs.

No Lean, API, credentials, shared modules, author freeze, or scope mutations.
Every payload is uncompiled until future granted native transplant verification.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import re

TASK = Path(__file__).resolve().parents[1]
WORKSPACE = TASK.parents[1]
AUTHOR = TASK / "verification/formalization-analytic-factorial-preparation-2026-10-07"
OUT = TASK / "formalization/platform/analytic-uniform-weighted"
STAGED = OUT / "staged"
DEFINITION = "ZetaNine_AnalyticUniformWeighted"
NEW_DEF_MODULE = "Definitions.Def_" + DEFINITION
AUTHOR_SHA = "fa1b455c1de84c664c89d169a39538e77e229a6c16961abbebe5b84951020c81"
CANONICAL = {"ZetaNine.CoefficientMap": "Definitions/Def_ZetaNine_CoefficientMap.lean",
             "ZetaNine.AnalyticPhase": "Definitions/Def_ZetaNine_AnalyticPhase.lean"}
TARGETS = (
    ("ZetaNine.AnalyticUniformMomentBound.actualMoment_uniform_bound", "moment", "n r hn hr"),
    ("ZetaNine.AnalyticWeightedBound.changing_quartics_uniform_bound", "changing", "W hW"),
    ("ZetaNine.AnalyticWeightedBound.actual_weighted_uniform_o_one", "uniform", ""),
)
COMMON = '''set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 200000
noncomputable section
open scoped BigOperators Topology
open Set Finset Filter Polynomial
open ZetaNine
open ZetaNine.AnalyticMomentBounds ZetaNine.AnalyticUniformMomentBound
open ZetaNine.AnalyticWeightedBound
'''


def binding(p):
    data = p.read_bytes()
    base = TASK if p.is_relative_to(TASK) else WORKSPACE
    return {"task_relative" if base == TASK else "root_relative": p.relative_to(base).as_posix(),
            "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}


def path_of(b):
    return (TASK if "task_relative" in b else WORKSPACE) / b.get("task_relative", b.get("root_relative"))


def verify(b):
    assert binding(path_of(b)) == b, b


def write(p, text):
    p.parent.mkdir(parents=True, exist_ok=True)
    if p.exists():
        assert p.read_text(encoding="utf-8") == text, "Existing SOURCE preparation differs: " + str(p)
        return
    p.write_text(text, encoding="utf-8")


def dump(p, value):
    write(p, json.dumps(value, ensure_ascii=False, indent=2) + "\n")


def def_spans(text):
    return list(re.finditer(r"(?ms)^def (\w+)\b.*?(?=\n\n)", text))


def def_blocks(text):
    return {m.group(1): m.group(0).strip() for m in def_spans(text)}


def headers(text):
    return {m.group(1): text[m.start():text.index(":=", m.end()) + 2]
            for m in re.finditer(r"(?m)^theorem (\w+)", text)}


def arguments(prefix, name):
    text = prefix[len("theorem " + name):]
    args, pos = [], 0
    while True:
        while text[pos].isspace():
            pos += 1
        if text[pos] == ":":
            return " ".join(args)
        opener = text[pos]
        assert opener in "({", (name, text[pos:])
        closer = ")" if opener == "(" else "}"
        depth, end = 1, pos + 1
        while depth:
            depth += (text[end] == opener) - (text[end] == closer)
            end += 1
        args += text[pos + 1:end - 1].split(":", 1)[0].split()
        pos = end


def strip_comments(text):
    return re.sub(r"--[^\n]*", "", re.sub(r"/-.*?-/", "", text, flags=re.S))


def strip_imports_and_defs(text):
    for m in reversed(def_spans(text)):
        text = text[:m.start()] + text[m.end():]
    return re.sub(r"(?m)^import [^\n]*\n", "", text)


def module_name(path):
    return path[:-5].replace("/", ".")


def main():
    assert not (OUT / "source-preparation-v1.json").exists(), "Do not modify a prior frozen platform preparation."
    audit_path = AUTHOR / "author-complete-audit.json"
    assert binding(audit_path)["sha256"] == AUTHOR_SHA
    audit = json.loads(audit_path.read_text(encoding="utf-8"))
    assert audit["status"] == "AUTHOR_FULL_SOURCE_AND_CONTROLS_PASS_INDEPENDENT_REVIEW_PENDING"
    assert audit["new_complete_theorems"] == 70 and audit["new_complete_definitions"] == 13
    source_rows = []
    source_infos = []
    decls = []
    definitions = []
    inline_chunks = []
    for row in audit["all_complete_exports"]:
        verify(row["complete_source_export"])
        if row["module"] in ("AFTypes", "AFKernel", "AFBoundary", "AFResolver", "AFExprDag", "AFExprDagValidation"):
            continue
        source = path_of(row["complete_source_export"])
        text = source.read_text(encoding="utf-8")
        namespace = re.search(r"(?m)^namespace (\S+)", text).group(1)
        source_rows.append(row)
        for name, prefix in headers(text).items():
            decls.append({"name": name, "namespace": namespace, "full_name": namespace + "." + name,
                          "prefix": prefix, "source_module": row["module"]})
        for name, body in def_blocks(text).items():
            definitions.append({"name": name, "namespace": namespace, "full_name": namespace + "." + name,
                                "body": body, "source_module": row["module"]})
        archived = OUT / "native-source-closure" / (row["module"].replace(".", "/") + ".lean")
        archived.parent.mkdir(parents=True, exist_ok=True)
        if archived.exists():
            assert archived.read_bytes() == source.read_bytes()
        else:
            archived.write_bytes(source.read_bytes())
        assert binding(archived)["sha256"] == row["complete_source_export"]["sha256"]
        source_infos.append({"module": row["module"], "author_success_call": row["actual_success_call"],
                             "author_export": row["complete_source_export"], "unchanged_source_copy": binding(archived),
                             "original_complete_theorem_count": len(headers(text)),
                             "original_whole_definition_count": len(def_blocks(text))})
        inline = strip_imports_and_defs(text)
        assert headers(inline) == headers(text)
        assert not def_blocks(inline)
        inline_chunks.append("\n/- SOURCE module: " + row["module"] + "; complete theorem bodies retained. -/\n" + inline)
    assert len(source_rows) == 11 and len(decls) == 122 and len(definitions) == 29
    assert len({r["full_name"] for r in decls}) == 122
    new_defs = [d for d in definitions if d["namespace"] not in CANONICAL]
    old_defs = [d for d in definitions if d["namespace"] in CANONICAL]
    assert len(new_defs) == 13 and len(old_defs) == 16
    canonical_rows = []
    for namespace, relative in CANONICAL.items():
        real_source = WORKSPACE / relative
        text = real_source.read_text(encoding="utf-8")
        native_values = {d["name"]: d["body"] for d in old_defs if d["namespace"] == namespace}
        assert def_blocks(text) == native_values
        assert not headers(text)
        assert not re.search(r"\b(sorry|admit|axiom|unsafe)\b", strip_comments(text))
        mirror = STAGED / relative
        mirror.parent.mkdir(parents=True, exist_ok=True)
        if mirror.exists():
            assert mirror.read_bytes() == real_source.read_bytes()
        else:
            mirror.write_bytes(real_source.read_bytes())
        canonical_rows.append({"definition_id": Path(relative).stem[4:], "module": module_name(relative),
                               "actual_shared_canonical_source": binding(real_source), "staged_exact_copy": binding(mirror),
                               "original_whole_values_exact": True, "definition_count": len(native_values)})
    imports = "import Mathlib\n" + "".join("import " + r["module"] + "\n" for r in canonical_rows)
    definition_text = imports + COMMON
    for namespace in dict.fromkeys(d["namespace"] for d in new_defs):
        definition_text += "\nnamespace " + namespace + "\n"
        if namespace == "ZetaNine.AnalyticUniformMomentBound":
            definition_text += "open AnalyticMomentBounds\n"
        if namespace == "ZetaNine.AnalyticWeightedBound":
            definition_text += "open AnalyticMomentBounds AnalyticUniformMomentBound\n"
        definition_text += "\n" + "\n\n".join(d["body"] for d in new_defs if d["namespace"] == namespace) + "\n\n"
        definition_text += "end " + namespace + "\n"
    # Generic COMMON opens refer to namespaces created by this definition. Only use
    # the ordinary language/scope opens before declaring the three namespaces.
    definition_text = definition_text.replace("open ZetaNine.AnalyticMomentBounds ZetaNine.AnalyticUniformMomentBound\n", "")
    definition_text = definition_text.replace("open ZetaNine.AnalyticWeightedBound\n", "")
    assert def_blocks(definition_text) == {d["name"]: d["body"] for d in new_defs}
    assert not headers(definition_text)
    def_path = "Definitions/Def_" + DEFINITION + ".lean"
    write(STAGED / def_path, definition_text)
    solution_base = "import " + NEW_DEF_MODULE + "\nimport Mathlib\n" + "\n".join(inline_chunks)
    assert len(headers(solution_base)) == 122
    assert not re.search(r"\b(sorry|admit|axiom|native_decide|unsafe|partial)\b", strip_comments(solution_base))
    assert not re.search(r"(?m)^import (Theorems|Solutions|missions)\.", solution_base)
    targets = []
    catalog = "import " + NEW_DEF_MODULE + "\n" + COMMON
    for wanted, key, args in TARGETS:
        d = next(x for x in decls if x["full_name"] == wanted)
        assert arguments(d["prefix"], d["name"]) == args
        identifier = wanted.replace(".", "_")
        reference_path = "Theorems/Thm_" + identifier + ".lean"
        solution_path = "Solutions/Sol_" + identifier + ".lean"
        statement = "import " + NEW_DEF_MODULE + "\n" + COMMON
        statement += "\nnamespace " + d["namespace"] + "\n" + d["prefix"] + " by sorry\nend " + d["namespace"] + "\n"
        assert list(headers(statement).values()) == [d["prefix"]]
        write(STAGED / reference_path, statement)
        catalog += "\nnamespace " + d["namespace"] + "\n" + d["prefix"] + " by sorry\nend " + d["namespace"] + "\n"
        wrapper_prefix = d["prefix"].replace("theorem " + d["name"], "theorem solution", 1)
        wrapper = "\n" + COMMON + "\n" + wrapper_prefix + " by\n  exact @" + wanted + (" " + args if args else "") + "\n\n#print axioms solution\n"
        solution = solution_base + wrapper
        assert len(headers(solution)) == 123
        assert all(headers(solution)[x["name"]] == x["prefix"] for x in decls)
        write(STAGED / solution_path, solution)
        targets.append({"key": key, "theorem_name": wanted, "theorem_id": identifier,
                        "local_reference": reference_path, "local_solution": solution_path,
                        "wrapper_arguments": args, "exact_original_header": d["prefix"][:-2].rstrip(),
                        "original_prefix": d["prefix"], "reference_binding": binding(STAGED / reference_path),
                        "solution_binding": binding(STAGED / solution_path),
                        "statement_catalog_only_by_sorry": True,
                        "solution_all_122_original_proof_bodies_inline": True, "UNCOMPILED_TRANSPLANT": True})
    write(OUT / "catalog/AnalyticUniformWeightedTypeCatalog.lean", catalog)
    assert len(headers(catalog)) == 3
    # Full future controls are copied as SOURCE only, then expanded to all 122
    # original theorem types. Every type/proof record remains lossless DAG +
    # strict reconstruction + inferType + Std3. Each solution is audited in a
    # separate project/environment because the 122 native names are shared.
    dag_source = AUTHOR / "native-author-export/controls/AFExprDag.lean"
    dag_fixture = AUTHOR / "native-author-export/controls/AFExprDagValidation.lean"
    write(OUT / "controls/common/AUPlatformExprDag.lean", dag_source.read_text(encoding="utf-8"))
    fixtures = dag_fixture.read_text(encoding="utf-8").replace("import AFExprDag", "import AUPlatformExprDag")
    fixtures = fixtures.replace("import AnalyticPhaseUpperBound", "import Definitions.Def_ZetaNine_AnalyticPhase")
    write(OUT / "controls/common/AUPlatformExprDagValidation.lean", fixtures)
    controls = []
    expected = "namespace AFExpected\n\n" + "\n\n".join(
        d["prefix"] + " by\n  exact @" + d["full_name"] + " " + arguments(d["prefix"], d["name"])
        for d in decls) + "\n\nend AFExpected"
    for target in targets:
        solution_module = module_name(target["local_solution"])
        own_modules = [r["module"] for r in canonical_rows] + [NEW_DEF_MODULE, solution_module]
        for module in ("AFTypes", "AFKernel", "AFBoundary", "AFResolver"):
            source = AUTHOR / "native-author-export/controls" / (module + ".lean")
            text = source.read_text(encoding="utf-8")
            text = text.replace("import AFExprDag", "import AUPlatformExprDag")
            text = text.replace("import AnalyticWeightedBound", "import " + solution_module)
            if module == "AFTypes":
                start = text.index('  afRecord "theorem"')
                end = text.index("  let env ← getEnv", start)
                text = text[:start] + "".join('  afRecord "theorem" ``' + d["full_name"] + "\n" for d in decls) + text[end:]
                text = re.sub(r"if #\[.*?\]\.contains m then", "if #[" + ", ".join("`" + n for n in own_modules) + "].contains m then", text)
            if module == "AFKernel":
                start = text.index("namespace AFExpected")
                end = text.index("end AFExpected", start) + len("end AFExpected")
                text = text[:start] + expected + text[end:]
                start = text.index('  afCompare "theorem_compare"')
                text = text[:start] + "".join('  afCompare "theorem_compare" ``' + d["full_name"] + ' ``AFExpected.' + d["name"] + ' false\n  afRecord "expected_theorem_value" ``AFExpected.' + d["name"] + "\n" for d in decls)
                text += '  afCompare "selected_wrapper_compare" ``solution ``AFExpected.' + target["theorem_name"].split(".")[-1] + ' false\n  afRecord "selected_wrapper_proof" ``solution\n'
            name = "AUP" + module[2:] + "_" + target["key"]
            dest = OUT / "controls" / target["key"] / (name + ".lean")
            write(dest, text)
            controls.append({"target": target["theorem_name"], "module": name,
                             "original_actual_author_control_source": binding(source), "source_only_transplant": binding(dest),
                             "planned_complete_expected_types": 122 if module == "AFKernel" else None,
                             "planned_complete_whole_definition_values": 29 if module == "AFKernel" else None,
                             "planned_typed_boundaries": 15 if module == "AFBoundary" else None})
    fidelity = {"stage": "UNCOMPILED_TRANSPLANT_SOURCE_ONLY", "actual_lean_calls": 0,
                "API_calls": 0, "credential_reads": 0, "shared_module_writes": 0,
                "native_independent_review_pass": False, "platform_author_pass": False,
                "platform_independent_pass": False, "uploaded": False,
                "author_native_audit": binding(audit_path), "all_11_native_source_copies": source_infos,
                "native_theorems": 122, "coefficient_map_theorems": 18, "phase_theorems": 34, "new_A_theorems": 70,
                "all_original_complete_theorem_prefixes": [{"full_name": d["full_name"], "prefix": d["prefix"],
                    "sha256_utf8": hashlib.sha256(d["prefix"].encode()).hexdigest()} for d in decls],
                "all_29_original_whole_definition_bodies": definitions,
                "all_13_new_definition_bodies_exact": True, "all_16_old_canonical_definition_bodies_exact": True,
                "all_122_original_proofs_retained_in_each_of_three_solutions": True,
                "no_import_of_Theorems_statement_placeholders": True,
                "old_public_definition_dependencies": canonical_rows,
                "whole_definition_comparison_plan": "All 29 complete original type/value controls + whole-function rfl, retaining raw Expr.equal diagnostics and strict full-field proof-helper pairing",
                "generated_helper_inventory_plan": "Every actual module declaration and extraConstName in all 4 mathematical transplant modules, including all private/compiler proposition helpers; missing environment declarations explicitly inventoried",
                "proof_value_plan": "Full lossless DAG payload of original type/value, strict persisted reconstruction Expr.equal, isDefEq and inferType, every complete field retained",
                "axiom_plan": "Only propext/Classical.choice/Quot.sound for all 122 proofs, 29 definitions, aliases, wrappers and actual kernel helpers",
                "serializer_fixture_plan": "Fresh own source compile + all20 constructor/metadata/payload fixtures +3 small-source raw-tree reconstructions",
                "actual_path_plan": "Fresh own proof objects only; all actual Lean.findOLean canonical paths and file bindings; pinned Mathlib and intrinsic runtime only",
                "selected_original_domains": "Moment n>=1,r<=4; changing family all natDegree<=4, every n>=1; final existential coefficient-independent epsilon tending0 for every n>=1 and every Wdegree<=4",
                "no_new_summability_HasSum_momentbound_coefficient_growth_or_parity_input": True,
                "control_SOURCE_only_copies": controls,
                "independent_native_and_transplant_reviews_still_required": True,
                "irrationality_integer_preimage_height_J_and_exact_fstar_remain_open": True,
                "preparation_script": binding(Path(__file__))}
    payloads = [{"kind": "definition_new13_functions", "path": def_path, "binding": binding(STAGED / def_path)}]
    for target in targets:
        payloads.extend([{"kind": "statement_type_catalog_only", "path": target["local_reference"], "binding": target["reference_binding"]},
                         {"kind": "complete_solution_122_original_proofs_plus_wrapper", "path": target["local_solution"], "binding": target["solution_binding"]}])
    dump(OUT / "target-plan.json", {"stage": fidelity["stage"], "definition": DEFINITION,
         "local_definition": def_path, "targets": targets, "canonical_dependencies": canonical_rows,
         "payloads": payloads, "Mathlib_ENV": "0df444a360eaa60ab8c11dca51a86af692955474",
         "references_catalog_only_never_proof": True, "native_independent_review_pass": False,
         "transplant_author_independent_pass": False, "uploaded": False})
    dump(OUT / "source-preparation-v1.json", fidelity)
    print(json.dumps({"stage": fidelity["stage"], "source_preparation": binding(OUT / "source-preparation-v1.json"),
                      "target_plan": binding(OUT / "target-plan.json"), "proofs_each_solution": 122,
                      "new_definition_functions": 13, "complete_whole_values": 29, "targets": 3,
                      "actual_Lean_or_API_calls": 0}))


if __name__ == "__main__":
    main()
