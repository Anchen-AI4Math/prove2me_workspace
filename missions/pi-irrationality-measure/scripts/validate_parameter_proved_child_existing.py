"""Bounded c1 adapter for the legacy TypedSnapshotCore source certificate.

The frozen c1 consumer expects type-only theorem rows.  Its source certificate
is older and carries the full theorem proof Expr in ``original-type.json``.
This adapter validates and pins that full Expr, then applies exactly one
in-memory consumer predicate edit: the old source row is allowed to retain its
full proof value. The fresh source and imported child rows remain type-only.
No Lean compiler, API, or parent artifact is written by this script.
"""
from __future__ import annotations

import hashlib
import inspect
import json
from pathlib import Path
import re
import shutil

import stage_parameter_proved_children as producer

TASK = producer.TASK
ROOT = producer.ROOT
STAGE = producer.V / "ap4/c1"
ADAPTER = Path(__file__).resolve()
BASE_CERT = STAGE / "actual-child-validation.base.json"
FINAL_CERT = STAGE / "actual-child-validation.json"
THEOREM = "OAI.PiExponent.exists_large_log_approximation"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fail(condition: bool, message: str):
    if condition:
        raise ValueError(message)


def validate_level(value, parameters):
    fail(not isinstance(value, list) or not value or not isinstance(value[0], str), "Malformed source value universe expression")
    tag = value[0]
    if tag == "zero":
        fail(len(value) != 1, "Malformed zero universe")
    elif tag in {"succ", "param"}:
        fail(len(value) != 2, "Malformed unary universe")
        if tag == "param":
            fail(not isinstance(value[1], str) or value[1] not in parameters, "Unbound source value universe parameter")
        else:
            validate_level(value[1], parameters)
    elif tag in {"max", "imax"}:
        fail(len(value) != 3, "Malformed binary universe")
        validate_level(value[1], parameters)
        validate_level(value[2], parameters)
    else:
        raise ValueError("Unsupported or nonclosed source value universe tag: " + tag)


def validate_expr(value, depth, parameters):
    fail(not isinstance(value, list) or not value or not isinstance(value[0], str), "Malformed source proof Expr")
    tag = value[0]
    if tag == "bvar":
        fail(len(value) != 2 or type(value[1]) is not int or not 0 <= value[1] < depth, "Source proof has a loose de Bruijn index")
    elif tag in {"fvar", "mvar"}:
        raise ValueError("Source proof Expr contains a free or metavariable")
    elif tag == "sort":
        fail(len(value) != 2, "Malformed sort expression")
        validate_level(value[1], parameters)
    elif tag == "const":
        fail(len(value) != 3 or not isinstance(value[1], str) or not isinstance(value[2], list), "Malformed constant expression")
        for level in value[2]:
            validate_level(level, parameters)
    elif tag == "app":
        fail(len(value) != 3, "Malformed application expression")
        validate_expr(value[1], depth, parameters)
        validate_expr(value[2], depth, parameters)
    elif tag in {"lambda", "forall"}:
        fail(len(value) != 4 or value[1] not in {"explicit", "implicit", "strictImplicit", "instance"}, "Malformed binder expression")
        validate_expr(value[2], depth, parameters)
        validate_expr(value[3], depth + 1, parameters)
    elif tag == "let":
        fail(len(value) != 5 or type(value[4]) is not bool, "Malformed let expression")
        validate_expr(value[1], depth, parameters)
        validate_expr(value[2], depth, parameters)
        validate_expr(value[3], depth + 1, parameters)
    elif tag == "natLiteral":
        fail(len(value) != 2 or type(value[1]) is not int or value[1] < 0, "Malformed natural literal")
    elif tag == "stringLiteral":
        fail(len(value) != 2 or not isinstance(value[1], str), "Malformed string literal")
    elif tag == "projection":
        fail(len(value) != 4 or not isinstance(value[1], str) or type(value[2]) is not int or value[2] < 0, "Malformed projection expression")
        validate_expr(value[3], depth, parameters)
    else:
        raise ValueError("Unsupported source proof Expr tag: " + tag)


def full_expr_pin(c):
    validation = producer.read(c["parent_validation"])
    original_path = c["parent"] / "original-type.json"
    generated_path = c["parent"] / "generated-type.json"
    fail(validation.get("validated") is not True or validation.get("kernel_types_equal") is not True,
         "Frozen parent type certificate is not validated")
    fail(sha(original_path) != validation.get("original_type_sha256"), "Historical fullExpr source certificate hash changed")
    fail(sha(generated_path) != validation.get("generated_type_sha256"), "Historical generated type certificate hash changed")
    rows = producer.read(original_path)
    fail(not isinstance(rows, list) or len(rows) != 1, "Historical source type certificate has an unexpected row domain")
    row = rows[0]
    fail(set(row) != {"levelParams", "name", "prettyType", "type", "value"}
         or row.get("name") != THEOREM or row.get("value") is None,
         "Historical source row is not the exact TypedSnapshotCore fullExpr theorem row")
    params = row["levelParams"]
    fail(not isinstance(params, list) or any(not isinstance(x, str) for x in params) or len(params) != len(set(params)),
         "Historical fullExpr universe parameter list is malformed")
    validate_expr(row["type"], 0, set(params))
    validate_expr(row["value"], 0, set(params))
    canonical_value = json.dumps(row["value"], ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    return {
        "path": producer.task_rel(original_path),
        "file_sha256": sha(original_path),
        "row_sha256": hashlib.sha256(json.dumps(row, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode("utf-8")).hexdigest(),
        "type_full_expr_sha256": hashlib.sha256(json.dumps(row["type"], ensure_ascii=False, separators=(",", ":")).encode("utf-8")).hexdigest(),
        "value_full_expr_sha256": hashlib.sha256(canonical_value).hexdigest(),
        "value_full_expr_valid": True,
        "source_proof_value_present": True,
        "source_proof_expr_node_count": count_expr(row["value"]),
        "universe_parameters": params,
        "schema": "TypedSnapshotCore.Expr.v1",
    }


def count_expr(value):
    if not isinstance(value, list) or not value:
        return 0
    if value[0] in {"app"}:
        return 1 + count_expr(value[1]) + count_expr(value[2])
    if value[0] in {"lambda", "forall"}:
        return 1 + count_expr(value[2]) + count_expr(value[3])
    if value[0] == "let":
        return 1 + count_expr(value[1]) + count_expr(value[2]) + count_expr(value[3])
    if value[0] == "projection":
        return 1 + count_expr(value[3])
    return 1


def main():
    c = producer.configure(("c1", "exists_large_log_approximation", "independent"))
    fail(FINAL_CERT.exists() or BASE_CERT.exists(), "Refusing to replace existing c1 consumer evidence")
    producer.check_only(c)
    legacy_pin = full_expr_pin(c)

    # Compile an in-memory copy of the frozen consumer after removing exactly
    # the legacy source-value null predicate. All child and fresh-source
    # type-only null checks, imported-CI checks, context.record replays, and
    # source/proof axiom audits remain byte-for-byte identical.
    consumer_source = inspect.getsource(producer.validate_existing)
    old = ' or original_t["value"] is not None'
    fail(consumer_source.count(old) != 1, "Frozen consumer legacy predicate anchor changed")
    adapted_source = consumer_source.replace(old, "", 1)
    namespace = dict(producer.__dict__)
    # The frozen consumer retained a legacy reference to `generated_pf` while
    # moving its parent checks onto the embedded record. Supply that one
    # historical timing value from the already pinned validation row.
    parent_validation = producer.read(c["parent_validation"])
    generated_seconds = parent_validation["preflights"]["SnapshotGenerated.lean"]["seconds"]
    namespace["generated_pf"] = {"data": {"seconds": generated_seconds}}
    exec(compile(adapted_source, inspect.getsourcefile(producer.validate_existing), "exec"), namespace)
    base = namespace["validate_existing"](c)
    fail(base.get("validated") is not True or base.get("module") != c["module"], "Adapted existing-node consumer returned an unexpected base certificate")
    producer.dump(BASE_CERT, base)

    cert = dict(base)
    cert["consumer_adapter"] = {
        "path": producer.task_rel(ADAPTER),
        "sha256": sha(ADAPTER),
        "frozen_producer": producer.task_rel(Path(producer.__file__)),
        "frozen_producer_sha256": sha(Path(producer.__file__)),
        "bounded_change": "removed only original_t.value null predicate from in-memory source/child type-only guard",
        "fresh_source_value_null_guard_retained": True,
        "child_value_null_guard_retained": True,
        "legacy_generated_preflight_seconds_binding": generated_seconds,
        "legacy_generated_preflight_seconds_source": "pinned parent validation preflights.SnapshotGenerated.lean.seconds",
        "lean_started": False,
        "api_used": False,
    }
    cert["historical_full_expr_source_certificate"] = legacy_pin
    cert["historical_source_certificate_sha256"] = sha(c["parent"] / "original-type.json")
    producer.dump(FINAL_CERT, cert)
    print(json.dumps({"validated": True, "certificate": producer.task_rel(FINAL_CERT),
        "certificate_sha256": sha(FINAL_CERT), "base_certificate": producer.task_rel(BASE_CERT),
        "adapter_sha256": sha(ADAPTER), "historical_full_expr_sha256": legacy_pin["value_full_expr_sha256"],
        "module": c["module"], "theorem": c["theorem"], "Std3_only": cert["Std3_only"],
        "kernel_type_equal_to_source_and_proved_solution": cert["kernel_type_equal_to_source_and_proved_solution"],
        "actual_module_owner": cert["actual_module_owner"], "max_file_seconds": cert["max_file_seconds"],
        "Lean_started": False, "api_used": False}, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
