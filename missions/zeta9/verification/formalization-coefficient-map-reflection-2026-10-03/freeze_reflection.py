"""Freeze observed actual reflection/cancellation proofs, never rebuild frozen parents."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re, sys

sys.stdout.reconfigure(encoding="utf-8")
OUT = Path(__file__).resolve().parent
TASK = OUT.parents[1]
ROOT = TASK.parents[1]
SOURCE = TASK / "formalization/CoefficientMapReflection.lean"
OBJECT = SOURCE.with_suffix(".olean")
LOG = SOURCE.with_suffix(".compile.log")
EXIT = SOURCE.with_suffix(".compile-exit.txt")
AUDIT = OUT / "type-audit.lean"
AUDIT_LOG = OUT / "type-audit.log"
AUDIT_EXIT = OUT / "type-audit-exit.txt"
NOTE = TASK / "research/coefficient-map-reflection-2026-10-03.md"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

for path in [EXIT, AUDIT_EXIT]:
    assert int(path.read_text(encoding="utf-8-sig").strip()) == 0
source_text = SOURCE.read_text(encoding="utf-8-sig")
source_log = LOG.read_text(encoding="utf-8-sig")
audit_log = AUDIT_LOG.read_text(encoding="utf-8-sig")
for log in [source_log, audit_log]:
    assert ": error:" not in log and "sorryAx" not in log
assert source_log.count("depends on axioms") == 11
assert OBJECT.stat().st_mtime >= SOURCE.stat().st_mtime
records = [json.loads(line) for line in audit_log.splitlines() if line.startswith("{")]
source_declarations = re.findall(r"^(?:def|theorem) (\w+)", source_text, re.M)
checked = {"checked_original_Eq_three", "checked_regular_actual_reflection",
    "checked_rho_one_with_explicit_stronger_degree", "checked_n_zero_X_four_rho_one",
    "checked_n_zero_X_four_proper_not_strong", "checked_n_zero_X_four_exact_rational"}
expected = {"ZetaNine.CoefficientMapReflection." + x for x in source_declarations} | checked
assert len(source_declarations) == 34 and len(records) == 40
assert {r["declaration"] for r in records} == expected
assert all(set(r["axioms"]) <= STANDARD for r in records)
assert sum(r["definitionValue"] is not None for r in records) == 4
(OUT / "type-report.json").write_text(json.dumps(records, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
parents, parent_files = [], []
for name, directory in [
    ("CoefficientMap", "formalization-coefficient-map-2026-10-03"),
    ("CoefficientMapJet", "formalization-coefficient-map-jet-2026-10-03"),
    ("CoefficientMapInjectivity", "formalization-coefficient-map-injectivity-2026-10-03"),
    ("CoefficientMapPartialFractions", "formalization-coefficient-map-partial-fractions-2026-10-03")]:
    parent_source = TASK / f"formalization/{name}.lean"
    parent_object = parent_source.with_suffix(".olean")
    parent_receipt = TASK / f"verification/{directory}/compile-receipt.json"
    saved = json.loads(parent_receipt.read_text(encoding="utf-8"))
    assert sha(parent_source) == saved["source_sha256"]
    assert sha(parent_object) == saved["source_compile"]["object_sha256"]
    parents.append({"source": str(parent_source), "source_sha256": sha(parent_source),
        "object": str(parent_object), "object_sha256": sha(parent_object),
        "receipt": str(parent_receipt), "receipt_sha256": sha(parent_receipt)})
    parent_files.extend([parent_source, parent_object, parent_receipt])
    if name == "CoefficientMap":
        environment = saved["environment"]
manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
mathlib_revision = next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib")
assert mathlib_revision == "0df444a360eaa60ab8c11dca51a86af692955474"
assert (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip() == "leanprover/lean4:v4.33.1"
source_command = ["lake", "env", "pwsh", "-NoProfile", "-Command",
    f'$env:LEAN_PATH = "{ROOT.as_posix()};" + $env:LEAN_PATH; lean -o "{OBJECT.as_posix()}" "{SOURCE.as_posix()}"; exit $LASTEXITCODE']
audit_command = ["lake", "env", "pwsh", "-NoProfile", "-Command",
    f'$env:LEAN_PATH = "{ROOT.as_posix()};" + $env:LEAN_PATH; lean "{AUDIT.as_posix()}"; exit $LASTEXITCODE']
receipt = {
    "verdict": "PASS_ACTUAL_P9_REFLECTION_AND_EQ3_COEFFICIENT_CANCELLATION",
    "date_utc": datetime.now(timezone.utc).isoformat(),
    "source": str(SOURCE), "source_sha256": sha(SOURCE),
    "imports": re.findall(r"^import (.+)$", source_text, re.M),
    "source_compile": {"working_directory": str(ROOT), "command": source_command,
        "exit_code": 0, "status": "observed",
        "observed_exit_file": str(EXIT), "observed_exit_file_sha256": sha(EXIT),
        "log": str(LOG), "log_sha256": sha(LOG), "object": str(OBJECT),
        "object_sha256": sha(OBJECT), "printed_targets": 11, "only_standard_three_axioms": True,
        "observed_exec_session_id": 89055, "observed_completion_chunk_id": "7b505a"},
    "imported_statement_audit": {"working_directory": str(ROOT), "command": audit_command,
        "exit_code": 0, "status": "observed", "source": str(AUDIT), "source_sha256": sha(AUDIT),
        "observed_exit_file": str(AUDIT_EXIT), "observed_exit_file_sha256": sha(AUDIT_EXIT),
        "log": str(AUDIT_LOG), "log_sha256": sha(AUDIT_LOG),
        "records": len(records), "source_definitions": 4, "source_theorems": 30,
        "additional_exact_statements": 6, "actual_definition_values": 4,
        "all_source_declarations_covered": True, "only_standard_three_axioms": True,
        "report": "type-report.json", "report_sha256": sha(OUT / "type-report.json"),
        "observed_exec_session_id": 2321, "observed_completion_chunk_id": "14185a"},
    "environment": environment,
    "current_toolchain_manifest_checked": {"lean_toolchain": "leanprover/lean4:v4.33.1",
        "mathlib_manifest_revision": mathlib_revision},
    "unchanged_frozen_dependencies": parents,
    "scope_note": {"path": str(NOTE), "sha256": sha(NOTE)},
    "mathematical_checks": {
        "actual_finite_base_numerator_and_inner_quadratic_reflection": True,
        "actual_pole_product_reversal_sign": True,
        "actual_erased_pole_product_reversal_sign": True,
        "actual_weightedR_anti_reflection_for_even_n_all_W": True,
        "actual_regular_point_domain_preserved_by_reflection": True,
        "actual_local_series_rescale_neg_one_identity_for_even_n": True,
        "actual_unit_denominator_identity_and_nonzero_cancellation_used": True,
        "all_j_le_n_s_one_to_nine_actual_local_coefficient_reflection": True,
        "actual_rho_is_finite_sum_of_all_actual_local_coefficients": True,
        "even_order_rho_zero_for_even_n_without_proper_assumption": True,
        "actual_partial_numerator_coeff_nine_n_plus_eight_equals_rho_one": True,
        "stronger_degree_bound_forces_actual_weighted_numerator_coefficient_zero": True,
        "rho_one_zero_under_stronger_bound_without_even_assumption": True,
        "original_even_n_ge_two_integer_quartic_stronger_bound_wrapper": True,
        "complete_original_p9_q1_mn_integer_quartic_Eq3_checked": True,
        "n_zero_W_X_pow_four_actual_rho_one_is_one": True,
        "n_zero_W_X_pow_four_actual_weightedR_equals_one_over_t": True,
        "n_zero_W_X_pow_four_proper_but_not_stronger_bound": True,
        "new_reflection_coefficient_or_cancellation_assumptions": []},
    "stronger_degree_domain": "2*n + 2*W.natDegree <= 9*(n+1)-2",
    "actual_p9_q1_m_equals_n_Eq3_specialization_closed": True,
    "general_p_or_multilayer_Eq3_closed": False,
    "rho_one_zero_from_strict_proper_alone": False,
    "Eq4_infinite_sum_L_closed": False,
    "original_five_dimensional_aggregated_F_injectivity_closed": False,
    "remaining_Z9_F_obligations": [
        "Eq(4): exact infinite sum/convergence and finite-sum-to-limit treatment of s=1.",
        "Denominator integrality and original five-dimensional aggregated coefficient map invertibility.",
        "Exact prescribed integer-output inverse image and exact L."],
    "full_Z9_F_closed": False, "irrationality_closed": False,
    "root_shared_scope_API_credentials_writes": False}
(OUT / "compile-receipt.json").write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
files = [SOURCE, OBJECT, LOG, EXIT, AUDIT, AUDIT_LOG, AUDIT_EXIT, OUT / "type-report.json",
    OUT / "compile-receipt.json", Path(__file__).resolve(), NOTE, *parent_files]
(OUT / "SHA256SUMS.txt").write_text("\n".join(sha(p) + "  " + p.relative_to(TASK).as_posix() for p in files) + "\n", encoding="utf-8")
for line in (OUT / "SHA256SUMS.txt").read_text(encoding="utf-8").splitlines():
    digest, rel = line.split("  ", 1)
    assert sha(TASK / rel) == digest
print(json.dumps({"verdict": receipt["verdict"], "source_sha256": sha(SOURCE),
    "records": len(records), "frozen_files": len(files), "full_Z9_F_closed": False}))
