"""Freeze actual SOURCE inputs for an independent afb1 compiler lane; no execution."""
from __future__ import annotations

import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path

TASK = Path(__file__).resolve().parents[1]
WORKSPACE = TASK.parents[1]
OUT = TASK / "verification/formalization-analytic-factorial-preparation-2026-10-07"
PROJECT = OUT / ".rt/afb1"
FROZEN_PREP_SHA = "bddc5450aa8298945697cff6c298726943e7919eeaaf9cbe36ddf1621934f853"


def binding(path: Path) -> dict:
    data = path.read_bytes()
    base = TASK if path.is_relative_to(TASK) else WORKSPACE
    return {"task_relative" if base == TASK else "root_relative": path.relative_to(base).as_posix(),
            "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}


def dump(path: Path, value: dict) -> None:
    assert not path.exists(), "Do not overwrite frozen preparation files."
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def main() -> None:
    frozen = OUT / "preparation-audit.json"
    assert binding(frozen)["sha256"] == FROZEN_PREP_SHA
    previous = json.loads(frozen.read_text(encoding="utf-8"))
    for row in previous["sources"]:
        actual = binding(TASK / row["task_relative"])
        assert all(actual[key] == row[key] for key in ("bytes", "sha256"))
    source_names = [row["task_relative"] for row in previous["sources"]]
    source_names.append("formalization/AnalyticPSeriesTail.lean")
    source_bindings = []
    theorem_count = 0
    for rel in source_names:
        path = TASK / rel
        text = path.read_text(encoding="utf-8")
        assert not re.search(r"\b(?:sorry|admit|native_decide)\b", text)
        assert not re.search(r"(?m)^\s*axiom\b", text)
        names = re.findall(r"(?m)^theorem\s+(\w+)", text)
        theorem_count += len(names)
        source_bindings.append({**binding(path), "complete_theorem_bodies": names})
    assert theorem_count == 32

    native = "verification/formalization-analytic-phase-upper-bound-2026-10-07/native-export/"
    originals = [
        "formalization/CoefficientMap.lean",
        "formalization/AnalyticFactorialBounds.lean",
        "formalization/AnalyticRationalFactorial.lean",
        native + "AnalyticPhase.lean",
        native + "AnalyticPhaseUpperBound.lean",
        "formalization/AnalyticRationalLogBound.lean",
        "formalization/AnalyticRationalTail.lean",
        "formalization/AnalyticPSeriesTail.lean",
    ]
    phase_pins = {row["task_relative"]: row["sha256"] for row in
                  previous["required_verified_native_phase_dependencies"]}
    assert not PROJECT.exists(), "Fresh SOURCE project must not have prior objects."
    (PROJECT / "src").mkdir(parents=True)
    (PROJECT / "b/lib/lean").mkdir(parents=True)
    copies = []
    for rel in originals:
        source = TASK / rel
        if rel in phase_pins:
            assert binding(source)["sha256"] == phase_pins[rel]
        target = PROJECT / "src" / source.name
        target.write_bytes(source.read_bytes())
        source_row = binding(source)
        copy_row = binding(target)
        assert source_row["bytes"] == copy_row["bytes"] and source_row["sha256"] == copy_row["sha256"]
        copies.append({"source": source_row, "private_source_copy": copy_row,
                       "module_name": source.stem, "copied_objects": 0})

    toolchain_source = WORKSPACE / "lean-toolchain"
    toolchain_copy = PROJECT / "lean-toolchain"
    toolchain_copy.write_bytes(toolchain_source.read_bytes())
    assert b"leanprover/lean4:v4.33.1" in toolchain_copy.read_bytes()
    policy = {
        "status": "SOURCE_INPUTS_ONLY_NO_COMPILATION",
        "own_object_directory": (PROJECT / "b/lib/lean").relative_to(TASK).as_posix(),
        "own_modules": [row["module_name"] for row in copies],
        "permitted_external_objects": "Only the pinned Mathlib package runtime and its declared packages.",
        "forbidden_objects": ["Root Definitions/Theorems/Solutions", "aph1", "api1", "any prior author/reviewer proof cache"],
        "copy_count": len(copies), "copied_olean_files": 0,
        "execution_policy": "Root must grant a compiler lane before any Lean/lake/runtime invocation.",
        "required_actual_author_checks": [
            "Compile every copied SOURCE dependency into afb1's own object directory in topological order.",
            "Verify complete expected forall types and actual kernel expressions for all 32 new endpoints.",
            "Verify complete definition types/values at each reachable own boundary.",
            "Check proof DAG has only standard axioms and no sorryAx/native decide/new axioms.",
            "Resolve every own import to afb1's actual own objects; preserve every actual failed attempt.",
            "Independent review must compile its own fresh SOURCE closure after author PASS.",
        ],
    }
    policy_path = PROJECT / "own-object-policy.json"
    dump(policy_path, policy)

    mathlib = WORKSPACE / ".lake/packages/mathlib/Mathlib"
    signature_inputs = []
    for rel, needles in (
        ("Analysis/SpecialFunctions/ImproperIntegrals.lean", (
            "theorem integrableOn_Ioi_rpow_of_lt", "theorem integral_Ioi_rpow_of_lt")),
        ("Analysis/SpecialFunctions/Pow/Real.lean", (
            "theorem antitoneOn_rpow_Ioi_of_exponent_nonpos", "theorem rpow_neg", "theorem rpow_natCast")),
        ("Topology/Algebra/InfiniteSum/NatInt.lean", (
            "protected theorem Multipliable.prod_mul_tprod_nat_add",)),
        ("Analysis/PSeries.lean", ("theorem summable_one_div_nat_pow",)),
    ):
        path = mathlib / rel
        text = path.read_text(encoding="utf-8")
        assert all(needle in text for needle in needles)
        signature_inputs.append({**binding(path), "observed_signature_sources": list(needles)})
    assert not list(PROJECT.rglob("*.olean"))
    plan = {"schema_version": 1, "prepared_at_utc": datetime.now(timezone.utc).isoformat(),
            "status": "PURE_SOURCE_INPUT_BINDINGS_ONLY", "new_theorem_bodies": theorem_count,
            "source_project": PROJECT.relative_to(TASK).as_posix(),
            "actual_lean_calls": 0, "actual_kernel_checks": 0, "actual_api_calls": 0,
            "credential_reads": 0, "first_four_source_frozen_audit": binding(frozen),
            "new_sources": source_bindings, "source_copies": copies,
            "toolchain_source": binding(toolchain_source), "toolchain_copy": binding(toolchain_copy),
            "own_object_policy": binding(policy_path), "mathlib_pseries_signatures": signature_inputs,
            "mathematical_handoff": binding(TASK / "research/analytic-moment-explicit-bound-2026-10-07.md"),
            "copied_olean_files": 0, "source_files_rehashed": len(copies)}
    plan_path = OUT / "native-inputs-preparation-audit.json"
    dump(plan_path, plan)
    print(json.dumps({"status": plan["status"], "new_theorems": theorem_count,
                      "copied_source_modules": len(copies), "copied_olean_files": 0,
                      "audit": binding(plan_path)}, ensure_ascii=False))


if __name__ == "__main__":
    main()
