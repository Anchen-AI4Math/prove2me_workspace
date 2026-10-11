"""Import and audit the observed full-source build without rebuilding it."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, subprocess, sys

sys.stdout.reconfigure(encoding="utf-8")
OUT = Path(__file__).resolve().parent
TASK = OUT.parents[1]
ROOT = TASK.parents[1]
SOURCE = TASK / "formalization/CoefficientMap.lean"
OBJECT = SOURCE.with_suffix(".olean")
SOURCE_LOG = TASK / "formalization/CoefficientMap.compile.log"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

source_hash = sha(SOURCE)
object_hash = sha(OBJECT)
source_log = SOURCE_LOG.read_text(encoding="utf-8-sig")
assert ": error:" not in source_log and "sorryAx" not in source_log
assert source_log.count("depends on axioms") == 8
version = subprocess.run(["lake", "env", "lean", "--version"], cwd=ROOT, capture_output=True)
assert version.returncode == 0
manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8-sig"))
mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
script = OUT / "type-audit.lean"
cmd = ["lake", "env", "pwsh", "-NoProfile", "-Command",
       f'$env:LEAN_PATH = "{ROOT.as_posix()};" + $env:LEAN_PATH; lean "{script.as_posix()}"; exit $LASTEXITCODE']
proc = subprocess.run(cmd, cwd=ROOT, capture_output=True)
log = OUT / "type-audit.log"
log.write_bytes(proc.stdout + proc.stderr)
(OUT / "type-audit-exit.txt").write_text(str(proc.returncode) + "\n", encoding="utf-8")
assert proc.returncode == 0, log.read_text(encoding="utf-8-sig")
assert source_hash == sha(SOURCE) and object_hash == sha(OBJECT)
reports = [json.loads(x) for x in log.read_text(encoding="utf-8-sig").splitlines() if x.startswith("{")]
assert len(reports) == 28
assert all(set(r["axioms"]) <= STANDARD for r in reports)
(OUT / "type-report.json").write_text(json.dumps(reports, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
receipt = {
    "verdict": "PASS_ACTUAL_FINITE_LEADING_POLE_BRIDGE",
    "date_utc": datetime.now(timezone.utc).isoformat(),
    "scope": "Finite p=9, q=1, m=n actual rational expression only; not the complete Z9.F theorem.",
    "source": str(SOURCE), "source_sha256": source_hash,
    "environment": {"lean_version": version.stdout.decode("utf-8").strip(),
                    "lean_toolchain": (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip(),
                    "mathlib_manifest_revision": mathlib["rev"],
                    "shared_toolchain_changes": False},
    "written_source_reference": {"path": "round5/research/arithmetic.md", "sections": "1-2; equations (1), (5), (6)",
                                 "sha256": sha(TASK / "round5/research/arithmetic.md")},
    "scope_note": {"path": "research/coefficient-map-finite-entry-2026-10-03.md",
                   "sha256": sha(TASK / "research/coefficient-map-finite-entry-2026-10-03.md")},
    "source_compile": {
        "command": "lake env lean -o missions/zeta9/formalization/CoefficientMap.olean missions/zeta9/formalization/CoefficientMap.lean *> missions/zeta9/formalization/CoefficientMap.compile.log; exit $LASTEXITCODE",
        "working_directory": str(ROOT), "exit_code": 0,
        "exit_code_provenance": "Observed actual unified-exec completion: session 16499, final chunk f4ce64, exit_code 0. The full source was not edited after that successful compile.",
        "log": str(SOURCE_LOG), "log_sha256": sha(SOURCE_LOG),
        "object": str(OBJECT), "object_sha256": object_hash,
        "printed_endpoints": 8, "only_standard_three_axioms": True,
    },
    "imported_statement_audit": {
        "command": cmd, "working_directory": str(ROOT), "exit_code": proc.returncode,
        "source": str(script), "source_sha256": sha(script),
        "log": str(log), "log_sha256": sha(log),
        "report": "type-report.json", "report_sha256": sha(OUT / "type-report.json"),
        "records": len(reports), "only_standard_three_axioms": True,
        "complete_explicit_original_endpoint_checked": True,
    },
    "mathematical_checks": {
        "actual_numerator_and_pole_product_defined": True,
        "regular_point_pole_clearing_proved": True,
        "cleared_denominator_at_pole_nonzero_proved": True,
        "factorial_products_prove_closed_binomial_formula": True,
        "actual_leading_coefficient_nonzero_and_integer": True,
        "even_sign_exactly_minus_one_to_j": True,
        "arbitrary_rational_polynomial_multiplier_evaluation": True,
        "actual_local_coordinate_identity": True,
        "binomial_formula_not_used_as_coefficient_definition": True,
        "new_assumptions_or_sorry": [],
    },
    "remaining_Z9_F_obligations": [
        "Lower-order partial-fraction coefficients and full decomposition of the actual rational function.",
        "Reflection, vanishing even coefficient sums, and the order-one cancellation.",
        "Exact infinite-sum identity L(W)=B(W)+A3*zeta(3)+A5*zeta(5)+A7*zeta(7)+A9*zeta(9).",
        "Actual five-dimensional formal coefficient map and all-even invertibility.",
        "Actual inverse-image construction with the exact prescribed output (b,a).",
    ],
    "root_shared_or_scope_writes": False, "API_or_credentials_access": False,
}
(OUT / "compile-receipt.json").write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
files = [SOURCE, OBJECT, SOURCE_LOG, script, log, OUT / "type-audit-exit.txt", OUT / "type-report.json",
         OUT / "compile-receipt.json", Path(__file__).resolve(),
         TASK / "research/coefficient-map-finite-entry-2026-10-03.md"]
(OUT / "SHA256SUMS.txt").write_text("\n".join(sha(p) + "  " + p.relative_to(TASK).as_posix() for p in files) + "\n", encoding="utf-8")
print(json.dumps({"verdict": receipt["verdict"], "source_sha256": source_hash, "audit_exit": proc.returncode,
                  "records": len(reports), "root_Z9_F_closed": False}, ensure_ascii=False))
