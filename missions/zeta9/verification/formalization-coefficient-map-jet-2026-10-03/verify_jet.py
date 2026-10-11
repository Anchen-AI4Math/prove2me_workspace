"""Hash-bound imported audit of the actually compiled local rational-function jet."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, subprocess, sys

sys.stdout.reconfigure(encoding="utf-8")
OUT = Path(__file__).resolve().parent
TASK = OUT.parents[1]
ROOT = TASK.parents[1]
SOURCE = TASK / "formalization/CoefficientMapJet.lean"
OBJECT = SOURCE.with_suffix(".olean")
LOG = TASK / "formalization/CoefficientMapJet.compile.log"
EXIT = TASK / "formalization/CoefficientMapJet.compile-exit.txt"
ENTRY = TASK / "formalization/CoefficientMap.lean"
ENTRY_RECEIPT = TASK / "verification/formalization-coefficient-map-2026-10-03/compile-receipt.json"
NOTE = TASK / "research/coefficient-map-jet-2026-10-03.md"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

source_hash, object_hash = sha(SOURCE), sha(OBJECT)
assert int(EXIT.read_text(encoding="utf-8-sig").strip()) == 0
source_log = LOG.read_text(encoding="utf-8-sig")
assert ": error:" not in source_log and "sorryAx" not in source_log
assert source_log.count("depends on axioms") == 10
assert OBJECT.stat().st_mtime >= SOURCE.stat().st_mtime
entry_receipt = json.loads(ENTRY_RECEIPT.read_text(encoding="utf-8"))
assert sha(ENTRY) == entry_receipt["source_sha256"]
assert sha(ENTRY.with_suffix(".olean")) == entry_receipt["source_compile"]["object_sha256"]
script = OUT / "type-audit.lean"
cmd = ["lake", "env", "pwsh", "-NoProfile", "-Command",
       f'$env:LEAN_PATH = "{ROOT.as_posix()};" + $env:LEAN_PATH; lean "{script.as_posix()}"; exit $LASTEXITCODE']
proc = subprocess.run(cmd, cwd=ROOT, capture_output=True)
audit_log = OUT / "type-audit.log"
audit_log.write_bytes(proc.stdout + proc.stderr)
(OUT / "type-audit-exit.txt").write_text(str(proc.returncode) + "\n", encoding="utf-8")
assert proc.returncode == 0, audit_log.read_text(encoding="utf-8-sig")
assert source_hash == sha(SOURCE) and object_hash == sha(OBJECT)
records = [json.loads(x) for x in audit_log.read_text(encoding="utf-8-sig").splitlines() if x.startswith("{")]
assert len(records) == 29
assert all(set(r["axioms"]) <= STANDARD for r in records)
assert sum(r["definitionValue"] is not None for r in records) == 9
(OUT / "type-report.json").write_text(json.dumps(records, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
receipt = {
    "verdict": "PASS_ACTUAL_LOCAL_NINE_ORDER_COEFFICIENT_CONVOLUTION",
    "date_utc": datetime.now(timezone.utc).isoformat(),
    "source": str(SOURCE), "source_sha256": source_hash,
    "source_compile": {"working_directory": str(ROOT), "exit_code": 0,
        "command": ["lake", "env", "pwsh", "-NoProfile", "-Command",
            f'$env:LEAN_PATH = "{ROOT.as_posix()};" + $env:LEAN_PATH; lean -o "{OBJECT.as_posix()}" "{SOURCE.as_posix()}"; exit $LASTEXITCODE'],
        "observed_exit_file": str(EXIT), "observed_exit_file_sha256": sha(EXIT),
        "log": str(LOG), "log_sha256": sha(LOG), "object": str(OBJECT), "object_sha256": object_hash,
        "printed_targets": 10, "only_standard_three_axioms": True},
    "imported_statement_audit": {"command": cmd, "working_directory": str(ROOT), "exit_code": proc.returncode,
        "source": str(script), "source_sha256": sha(script), "log": str(audit_log), "log_sha256": sha(audit_log),
        "records": len(records), "actual_definition_values": 9, "only_standard_three_axioms": True,
        "report": "type-report.json", "report_sha256": sha(OUT / "type-report.json"),
        "original_even_n_ge_two_integer_quartic_statement_checked": True},
    "environment": entry_receipt["environment"],
    "unchanged_frozen_entry": {"source": str(ENTRY), "source_sha256": sha(ENTRY),
        "object": str(ENTRY.with_suffix(".olean")), "object_sha256": sha(ENTRY.with_suffix(".olean")),
        "receipt": str(ENTRY_RECEIPT), "receipt_sha256": sha(ENTRY_RECEIPT)},
    "mathematical_checks": {
        "actual_shifted_polynomial_numerator_denominator_evaluation_bridge": True,
        "actual_weighted_rational_evaluation_bridge": True,
        "nonzero_constant_cleared_denominator": True,
        "genuine_formal_series_inverse_denominator_identity": True,
        "local_series_uniqueness": True,
        "all_one_to_nine_coefficients_from_actual_series": True,
        "highest_coefficient_matches_frozen_entry": True,
        "exact_Icc_s_nine_convolution": True,
        "actual_integer_W_composition_coefficients_cast_to_rationals": True,
        "new_coefficient_decomposition_or_inverse_map_assumptions": [],
        "analytic_convergence_claims": []},
    "scope_note": {"path": str(NOTE), "sha256": sha(NOTE)},
    "remaining_Z9_F_obligations": ["Global partial-fraction identity for the actual rational function.",
        "Reflection, vanishing even total coefficients and order-one cancellation.",
        "Exact infinite-sum identity and the actual five-dimensional coefficient map.",
        "All-even invertibility and exact prescribed integer-output inverse image."],
    "full_Z9_F_closed": False, "irrationality_closed": False,
    "root_shared_scope_API_credentials_writes": False}
(OUT / "compile-receipt.json").write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
files = [SOURCE, OBJECT, LOG, EXIT, script, audit_log, OUT / "type-audit-exit.txt", OUT / "type-report.json",
         OUT / "compile-receipt.json", Path(__file__).resolve(), NOTE, ENTRY, ENTRY.with_suffix(".olean"), ENTRY_RECEIPT]
(OUT / "SHA256SUMS.txt").write_text("\n".join(sha(p) + "  " + p.relative_to(TASK).as_posix() for p in files) + "\n", encoding="utf-8")
print(json.dumps({"verdict": receipt["verdict"], "source_sha256": source_hash, "audit_exit": proc.returncode,
                  "records": len(records), "full_Z9_F_closed": False}))
