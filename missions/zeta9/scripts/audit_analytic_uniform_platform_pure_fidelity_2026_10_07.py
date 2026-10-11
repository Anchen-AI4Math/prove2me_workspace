"""Independent deterministic lexical/byte checks of the SOURCE-only batch.

This is an offline preparation audit, not a Lean/kernel or independent proof PASS.
"""
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

TASK = Path(__file__).resolve().parents[1]
WORKSPACE = TASK.parents[1]
OUT = TASK / "formalization/platform/analytic-uniform-weighted"
STAGED = OUT / "staged"
PREP_SHA = "337d0d62bc56d6e28351bff5a598f3c71c64a9b3b86c95b96f7101c3bced039e"
PLAN_SHA = "680c948ce299c30f48c07bb24b4d677f44a22bb33a0a14684cb080bcf2128297"


def load(p):
    return json.loads(p.read_text(encoding="utf-8"))


def binding(p):
    data = p.read_bytes()
    base = TASK if p.is_relative_to(TASK) else WORKSPACE
    return {"task_relative" if base == TASK else "root_relative": p.relative_to(base).as_posix(),
            "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}


def path_of(b):
    return (TASK if "task_relative" in b else WORKSPACE) / b.get("task_relative", b.get("root_relative"))


def verify_bindings(value, count):
    if isinstance(value, dict):
        if {"bytes", "sha256"} <= set(value) and ("task_relative" in value or "root_relative" in value):
            assert binding(path_of(value)) == value, value
            count[0] += 1
        else:
            for v in value.values():
                verify_bindings(v, count)
    elif isinstance(value, list):
        for v in value:
            verify_bindings(v, count)


def headers(text):
    return {m.group(1): text[m.start():text.index(":=", m.end()) + 2]
            for m in re.finditer(r"(?m)^theorem (\w+)", text)}


def definitions(text):
    return {m.group(1): m.group(0).strip() for m in re.finditer(r"(?ms)^def (\w+)\b.*?(?=\n\n)", text)}


def full_proof_declarations(text):
    starts = list(re.finditer(r"(?m)^theorem (\w+)", text))
    result = {}
    for match in starts:
        end = re.search(r"(?m)^(?:theorem |def |end |#print )", text[match.end():])
        stop = len(text) if end is None else match.end() + end.start()
        result[match.group(1)] = text[match.start():stop].strip()
    return result


def strip_comments(text):
    return re.sub(r"--[^\n]*", "", re.sub(r"/-.*?-/", "", text, flags=re.S))


def main():
    assert binding(OUT / "source-preparation-v1.json")["sha256"] == PREP_SHA
    assert binding(OUT / "target-plan.json")["sha256"] == PLAN_SHA
    prep = load(OUT / "source-preparation-v1.json")
    plan = load(OUT / "target-plan.json")
    count = [0]
    verify_bindings(prep, count)
    verify_bindings(plan, count)
    original_headers = {x["full_name"]: x["prefix"] for x in prep["all_original_complete_theorem_prefixes"]}
    assert len(original_headers) == 122
    all_proofs = []
    for row in prep["all_11_native_source_copies"]:
        original = path_of(row["unchanged_source_copy"]).read_text(encoding="utf-8")
        ns = re.search(r"(?m)^namespace (\S+)", original).group(1)
        for name, proof in full_proof_declarations(original).items():
            all_proofs.append({"full_name": ns + "." + name, "name": name, "text": proof,
                               "source_module": row["module"], "sha256_utf8": hashlib.sha256(proof.encode()).hexdigest(),
                               "utf8_bytes": len(proof.encode())})
    assert len(all_proofs) == 122
    counts_by_ns = Counter(x["full_name"].rsplit(".", 1)[0] for x in all_proofs)
    assert counts_by_ns["ZetaNine.CoefficientMap"] == 18 and counts_by_ns["ZetaNine.AnalyticPhase"] == 34
    assert sum(counts_by_ns.values()) - 18 - 34 == 70
    checks = []
    for target in plan["targets"]:
        source = (STAGED / target["local_solution"]).read_text(encoding="utf-8")
        h = headers(source)
        assert len(h) == 123
        for row in all_proofs:
            assert source.count(row["text"]) == 1, row["full_name"]
            assert h[row["name"]] == original_headers[row["full_name"]]
        code = strip_comments(source)
        assert not re.search(r"\b(sorry|admit|axiom|native_decide|unsafe|partial)\b", code)
        assert not re.search(r"(?m)^import (Theorems|Solutions|missions)\.", code)
        wrapper = target["original_prefix"].replace("theorem " + target["theorem_name"].split(".")[-1], "theorem solution", 1)
        assert h["solution"] == wrapper
        assert "exact @" + target["theorem_name"] in source
        reference = (STAGED / target["local_reference"]).read_text(encoding="utf-8")
        assert list(headers(reference).values()) == [target["original_prefix"]]
        assert len(re.findall(r"\bsorry\b", strip_comments(reference))) == 1
        key = target["key"]
        controls = [r for r in prep["control_SOURCE_only_copies"] if r["target"] == target["theorem_name"]]
        assert len(controls) == 4
        for control in controls:
            text = path_of(control["source_only_transplant"]).read_text(encoding="utf-8")
            assert "import Solutions." in text and "import Theorems." not in text
            if control["module"].startswith("AUPTypes"):
                assert text.count('afRecord "theorem"') == 122
                assert text.count('afRecord "definition"') == 29
                for row in all_proofs:
                    assert 'afRecord "theorem" ``' + row["full_name"] in text
            if control["module"].startswith("AUPKernel"):
                expected = text.split("namespace AFExpected", 1)[1].split("end AFExpected", 1)[0]
                eh = headers(expected)
                assert len(eh) == 122
                for row in all_proofs:
                    assert eh[row["name"]] == original_headers[row["full_name"]]
                assert text.count('afCompare "theorem_compare"') == 122
                assert text.count('afCompare "definition_compare"') == 29
                assert text.count('afRecord "definition_rfl"') == 29
                assert 'afCompare "selected_wrapper_compare" ``solution' in text
                assert 'afRecord "selected_wrapper_proof" ``solution' in text
                assert "Only unfold all paired proposition-valued own compiler _proof_ helpers" in text
            if control["module"].startswith("AUPBoundary"):
                assert text.count('afRecord "typed_boundary"') == 15
        checks.append({"target": target["theorem_name"], "all_122_complete_native_proof_declarations_byte_text_exact": True,
                       "all_122_full_original_headers_exact": True, "original_wrapper_header_exact": True,
                       "statement_has_one_sorry_and_never_imported_as_proof": True,
                       "planned_complete_expected_types": 122, "planned_complete_whole_definition_values_and_rfl": 29,
                       "planned_selected_wrapper_type_and_full_proof_record": True, "planned_typed_boundaries": 15,
                       "actual_transplant_Lean_calls": 0, "UNCOMPILED_TRANSPLANT": True})
    native_defs = prep["all_29_original_whole_definition_bodies"]
    new = (STAGED / plan["local_definition"]).read_text(encoding="utf-8")
    assert len(definitions(new)) == 13
    for row in native_defs:
        if row["namespace"] in ("ZetaNine.CoefficientMap", "ZetaNine.AnalyticPhase"):
            canonical = next(c for c in plan["canonical_dependencies"] if c["definition_id"] == row["namespace"].replace(".", "_"))
            text = path_of(canonical["staged_exact_copy"]).read_text(encoding="utf-8")
        else:
            text = new
        assert definitions(text)[row["name"]] == row["body"]
    catalog_path = OUT / "catalog/AnalyticUniformWeightedTypeCatalog.lean"
    catalog = catalog_path.read_text(encoding="utf-8")
    assert len(headers(catalog)) == 3 and len(re.findall(r"\bsorry\b", strip_comments(catalog))) == 3
    core = OUT / "controls/common/AUPlatformExprDag.lean"
    fixture = OUT / "controls/common/AUPlatformExprDagValidation.lean"
    core_text = core.read_text(encoding="utf-8")
    assert "def persistedRoundTrip" in core_text and "Expr.equal t rt && Expr.equal v rv" in core_text
    assert "metadataJ m" in core_text and "syntaxJ v" in core_text and "binderJ i" in core_text
    record = {"status": "PURE_FIDELITY_PASS_UNCOMPILED_TRANSPLANT", "actual_Lean_calls": 0,
              "actual_API_calls": 0, "actual_credential_reads": 0, "native_independent_review_pass": False,
              "platform_author_independent_pass": False, "uploaded": False,
              "rehash_binding_count": count[0], "all_11_native_SOURCE_copies_exact": True,
              "all_original_complete_proof_declarations": [{k: v for k, v in p.items() if k != "text"} for p in all_proofs],
              "all_122_headers_exact_in_each_solution": True, "all_122_proof_body_source_declarations_exact_in_each_solution": True,
              "all_29_whole_definition_source_types_and_bodies_exact": True,
              "selected_targets_and_controls": checks,
              "catalog_type_only": binding(catalog_path), "lossless_DAG_source": binding(core),
              "lossless_DAG_validation_SOURCE": binding(fixture), "preparer_failure_01_retained": binding(OUT / "preparation-failure-01.json"),
              "source_preparation": binding(OUT / "source-preparation-v1.json"), "target_plan": binding(OUT / "target-plan.json"),
              "audit_script": binding(Path(__file__)), "native_author_freeze_not_modified": True}
    path = OUT / "pure-fidelity-v1.json"
    assert not path.exists()
    path.write_text(json.dumps(record, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": record["status"], "audit": binding(path), "rehashed_bindings": count[0],
                      "proof_declarations_each_solution": 122, "whole_definition_values": 29, "actual_Lean_API_calls": 0}))


if __name__ == "__main__":
    main()
