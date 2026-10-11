"""Freeze observed full-source and imported type evidence without rebuilding parents."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re, sys

sys.stdout.reconfigure(encoding="utf-8")
OUT = Path(__file__).resolve().parent
TASK = OUT.parents[1]
ROOT = TASK.parents[1]
SOURCE = TASK / "formalization/CoefficientMapInjectivity.lean"
OBJECT = SOURCE.with_suffix(".olean")
LOG = SOURCE.with_suffix(".compile.log")
EXIT = SOURCE.with_suffix(".compile-exit.txt")
AUDIT = OUT / "type-audit.lean"
AUDIT_LOG = OUT / "type-audit.log"
AUDIT_EXIT = OUT / "type-audit-exit.txt"
NOTE = TASK / "research/coefficient-map-injectivity-2026-10-03.md"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

for exit_file in [EXIT, AUDIT_EXIT]:
    assert int(exit_file.read_text(encoding="utf-8-sig").strip()) == 0
source_text = SOURCE.read_text(encoding="utf-8-sig")
source_log = LOG.read_text(encoding="utf-8-sig")
audit_log = AUDIT_LOG.read_text(encoding="utf-8-sig")
assert ": error:" not in source_log and ": error:" not in audit_log
assert "sorryAx" not in source_log and "sorryAx" not in audit_log
assert source_log.count("depends on axioms") == 9
assert OBJECT.stat().st_mtime >= SOURCE.stat().st_mtime
records = [json.loads(line) for line in audit_log.splitlines() if line.startswith("{")]
source_declarations = re.findall(r"^(?:def|theorem) (\w+)", source_text, re.M)
expected = {"ZetaNine.CoefficientMapInjectivity." + x for x in source_declarations} | {
    "checked_complete_local_array", "checked_quartic_local_array",
    "checked_original_integer_quartic", "checked_n_zero",
    "checked_actual_weighted_rational_representation"}
assert len(source_declarations) == 25 and len(records) == 30
assert {r["declaration"] for r in records} == expected
assert all(set(r["axioms"]) <= STANDARD for r in records)
assert sum(r["definitionValue"] is not None for r in records) == 7
(OUT / "type-report.json").write_text(json.dumps(records, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
parents = []
parent_files = []
for name, directory in [
    ("CoefficientMap", "formalization-coefficient-map-2026-10-03"),
    ("CoefficientMapJet", "formalization-coefficient-map-jet-2026-10-03")]:
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
source_command = ["lake", "env", "pwsh", "-NoProfile", "-Command",
    f'$env:LEAN_PATH = "{ROOT.as_posix()};" + $env:LEAN_PATH; lean -o "{OBJECT.as_posix()}" "{SOURCE.as_posix()}"; exit $LASTEXITCODE']
audit_command = ["lake", "env", "pwsh", "-NoProfile", "-Command",
    f'$env:LEAN_PATH = "{ROOT.as_posix()};" + $env:LEAN_PATH; lean "{AUDIT.as_posix()}"; exit $LASTEXITCODE']
receipt = {
    "verdict": "PASS_ACTUAL_COMPLETE_LOCAL_COEFFICIENT_ARRAY_INJECTIVITY",
    "date_utc": datetime.now(timezone.utc).isoformat(),
    "source": str(SOURCE), "source_sha256": sha(SOURCE),
    "imports": re.findall(r"^import (.+)$", source_text, re.M),
    "source_compile": {"working_directory": str(ROOT), "command": source_command,
        "exit_code": 0, "status": "observed",
        "observed_exit_file": str(EXIT), "observed_exit_file_sha256": sha(EXIT),
        "log": str(LOG), "log_sha256": sha(LOG), "object": str(OBJECT),
        "object_sha256": sha(OBJECT), "printed_targets": 9,
        "only_standard_three_axioms": True,
        "observed_exec_session_id": 71133, "observed_completion_chunk_id": "00c38c"},
    "imported_statement_audit": {"working_directory": str(ROOT), "command": audit_command,
        "exit_code": 0, "status": "observed", "source": str(AUDIT), "source_sha256": sha(AUDIT),
        "observed_exit_file": str(AUDIT_EXIT), "observed_exit_file_sha256": sha(AUDIT_EXIT),
        "log": str(AUDIT_LOG), "log_sha256": sha(AUDIT_LOG),
        "records": len(records), "source_definitions": 7, "source_theorems": 18,
        "additional_exact_statements": 5, "actual_definition_values": 7,
        "all_source_declarations_covered": True, "only_standard_three_axioms": True,
        "report": "type-report.json", "report_sha256": sha(OUT / "type-report.json")},
    "environment": environment,
    "unchanged_frozen_dependencies": parents,
    "scope_note": {"path": str(NOTE), "sha256": sha(NOTE)},
    "mathematical_checks": {
        "actual_finite_weighted_rational_numerator_evaluation": True,
        "all_j_le_n_all_s_one_to_nine_actual_jet_coefficients": True,
        "zero_actual_jets_imply_shifted_numerator_X_pow_nine_divisibility": True,
        "unshifted_actual_pole_factor_pow_nine_divisibility": True,
        "pairwise_coprime_actual_distinct_linear_factors": True,
        "full_pole_polynomial_pow_nine_divides_actual_weighted_numerator": True,
        "actual_denominator_degree_nine_times_n_plus_one": True,
        "actual_weighted_numerator_degree_upper_bound_two_n_plus_two_deg_W": True,
        "actual_base_numerator_nonzero_including_n_zero": True,
        "actual_quadratic_composition_cancellation": True,
        "proper_domain_complete_array_zero_kernel": True,
        "proper_domain_complete_Fin_n_plus_one_by_Fin_nine_array_injectivity": True,
        "quartic_domain_valid_for_every_n_including_zero": True,
        "original_even_n_ge_two_integer_quartic_statement_checked": True,
        "new_coefficient_or_injectivity_assumptions": []},
    "proper_domain": "2*n + 2*W.natDegree < 9*(n+1)",
    "complete_local_array_injectivity_closed": True,
    "original_five_dimensional_aggregated_F_injectivity_closed": False,
    "remaining_Z9_F_obligations": [
        "Global partial-fraction identity and actual infinite-sum identity.",
        "Reflection/vanishing/cancellation and denominator integrality.",
        "Original five-dimensional aggregated zeta/constant coefficient map injectivity/invertibility.",
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
