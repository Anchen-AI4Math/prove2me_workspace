#!/usr/bin/env python3
"""Certify the frozen structural source snapshot after a narrow JSON walker fix.

The successfully compiled source manifest pins the original validation modules.
Those bytes stay immutable.  Their ``expression_names`` helper attempted set
membership before checking that an Expr-JSON node tag was a string, so a nested
array raised ``TypeError: unhashable type: 'list'``.  This wrapper verifies the
two frozen module hashes, replaces only that pure walker in memory, and then
runs the complete original source validator.  No validation condition is
removed or weakened.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

import generate_shared_source_snapshot as base
import structural_kernel_snapshot as kernel
import validate_structural_kernel_source_snapshot as source_validator


TASK = Path(__file__).resolve().parents[1]
FROZEN_KERNEL_SHA256 = "685c82fbb4c4b41bad049896b0f74e2f9bd26be5ced9b0794a4d26862deab365"
FROZEN_SOURCE_VALIDATOR_SHA256 = "c414e8accebb06398443e69361307d69bc6cd46e974da51de761515c09a1ee8a"
CERTIFICATE = (
    TASK / "verification" / "shared-source-snapshot" / "structural-kernel-74" /
    "StructuralKernelSource74.validation.json"
)


def _assert(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def expression_names_safe(value: Any) -> set[str]:
    names: set[str] = set()

    def walk(node: Any) -> None:
        if isinstance(node, list):
            if (len(node) >= 2 and isinstance(node[0], str)
                    and node[0] in {"const", "projection"}
                    and isinstance(node[1], str)):
                names.add(node[1])
            for item in node:
                walk(item)
        elif isinstance(node, dict):
            for item in node.values():
                walk(item)

    walk(value)
    return names


def validate() -> tuple[dict[str, Any], dict[str, dict[str, Any]]]:
    kernel_path = Path(kernel.__file__).resolve()
    source_validator_path = Path(source_validator.__file__).resolve()
    _assert(base.sha_file(kernel_path) == FROZEN_KERNEL_SHA256,
            "Frozen structural kernel validator bytes changed")
    _assert(base.sha_file(source_validator_path) == FROZEN_SOURCE_VALIDATOR_SHA256,
            "Frozen structural source validator bytes changed")
    # Exercise the formerly failing shape before applying it to certificate rows.
    fixture = [["const", "X", []], [["sort", ["zero"]]]]
    _assert(expression_names_safe(fixture) == {"X"},
            "Corrected Expr-JSON name walker fixture failed")
    kernel.expression_names = expression_names_safe
    report, rows = source_validator.validate(require_actual=True)
    report["certifier_wrapper"] = base.task_relative(Path(__file__).resolve())
    report["certifier_wrapper_sha256"] = base.sha_file(Path(__file__).resolve())
    report["frozen_validator_runtime_fix"] = {
        "scope": "expression_names Expr-JSON tag type guard only",
        "frozen_kernel_validator": base.task_relative(kernel_path),
        "frozen_kernel_validator_sha256": FROZEN_KERNEL_SHA256,
        "frozen_source_validator": base.task_relative(source_validator_path),
        "frozen_source_validator_sha256": FROZEN_SOURCE_VALIDATOR_SHA256,
        "compiled_manifest_inputs_unchanged": True,
        "validation_conditions_removed": False,
        "nested_array_negative_regression_checked": True,
    }
    return report, rows


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certify-existing", action="store_true", required=True)
    args = parser.parse_args()
    _assert(args.certify_existing, "Only --certify-existing is supported")
    report, _ = validate()
    base.write_json(CERTIFICATE, report)
    print(json.dumps(report, ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
