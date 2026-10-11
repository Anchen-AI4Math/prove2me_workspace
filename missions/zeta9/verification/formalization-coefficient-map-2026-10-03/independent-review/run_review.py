"""Independent isolated compile and exact arithmetic audit of frozen CoefficientMap."""
from pathlib import Path
from fractions import Fraction
from math import comb, factorial, prod
import hashlib
import json
import os
import re
import subprocess

OUT = Path(__file__).resolve().parent
PROJECT = OUT / "project"
TASK = OUT.parents[2]
ROOT = TASK.parents[1]
EXPECTED = "e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03"
PIN = "0df444a360eaa60ab8c11dca51a86af692955474"
source = TASK / "formalization/CoefficientMap.lean"
data = source.read_bytes()
assert hashlib.sha256(data).hexdigest() == EXPECTED
PROJECT.mkdir(exist_ok=True)
(PROJECT / "CoefficientMap.lean").write_bytes(data)
(PROJECT / "lean-toolchain").write_text("leanprover/lean4:v4.33.1\n")
lock = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8-sig"))
assert next(row for row in lock["packages"] if row["name"] == "mathlib")["rev"] == PIN
lock["name"] = "zeta9CoefficientMapIndependentReview"
(PROJECT / "lake-manifest.json").write_text(json.dumps(lock, indent=2) + "\n")
(PROJECT / "lakefile.lean").write_text('''import Lake
open Lake DSL
package zeta9CoefficientMapIndependentReview
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "0df444a360eaa60ab8c11dca51a86af692955474"
lean_lib CoefficientMap where
  roots := #[`CoefficientMap]
  globs := #[.one `CoefficientMap]
''')
(PROJECT / ".lake").mkdir(exist_ok=True)
link = PROJECT / ".lake/packages"
target = ROOT / ".lake/packages"
if not link.exists():
    subprocess.run(["cmd", "/c", "mklink", "/J", str(link), str(target)], capture_output=True, check=True)
assert link.resolve() == target.resolve()
environment = os.environ.copy()
environment.pop("LEAN_PATH", None)
steps, chunks = [], []
for command in [["lake", "--no-cache", "build", "CoefficientMap"], ["lake", "env", "lean", "ReviewAudit.lean"]]:
    result = subprocess.run(command, cwd=PROJECT, env=environment, capture_output=True)
    chunks.append(("\nCOMMAND: " + " ".join(command) + "\n").encode())
    chunks.append(result.stdout + result.stderr)
    steps.append({"command": command, "exit_code": result.returncode})
    print(json.dumps(steps[-1]), flush=True)
    if result.returncode:
        break
log = b"".join(chunks)
(OUT / "independent-compile.log").write_bytes(log)
reports = {}
for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log.decode("utf-8-sig")):
    reports.setdefault(name, []).append(sorted(x.strip() for x in axioms.split(",") if x.strip()))
allowed = {"propext", "Classical.choice", "Quot.sound"}
bad = {name:values for name,values in reports.items() if any(set(xs) - allowed for xs in values)}
required_original = [
    "clear_highest_pole", "clearedPoleProduct_ne_zero", "leadingPoleCoefficient_eq",
    "leadingPoleCoefficient_ne_zero", "leadingPoleCoefficient_is_integer",
    "signed_leadingPoleCoefficient_pos_even", "clearedWeightedR_local_coordinate",
    "weightedLeadingPoleCoefficient_eq_even",
]
missing = ["ZetaNine.CoefficientMap." + name for name in required_original
           if "ZetaNine.CoefficientMap." + name not in reports]

regular_points, local_values, weighted_values = 0, 0, 0
for n in range(13):
    for j in range(n + 1):
        def numerator(t):
            return factorial(n) ** 7 * prod(t - (i + 1) for i in range(n)) * prod(t + n + (i + 1) for i in range(n))
        deleted = prod(Fraction(k - j) for k in range(n + 1) if k != j)
        assert deleted != 0
        assert deleted == (-1) ** j * factorial(j) * factorial(n - j)
        actual = Fraction(numerator(Fraction(-j)), deleted ** 9)
        expected = (-1) ** (n + j) * comb(n, j) ** 9 * comb(n + j, n) * comb(2 * n - j, n)
        assert actual == expected and actual.denominator == 1 and actual != 0
        if n % 2 == 0:
            assert (-1) ** j * actual > 0
        local_values += 1
        for t in [Fraction(1, 2), Fraction(n + 1), Fraction(-n - 1), Fraction(7, 3)]:
            full = prod(t + k for k in range(n + 1))
            assert full != 0
            cleared = prod(t + k for k in range(n + 1) if k != j)
            assert Fraction(numerator(t), full ** 9) * (t + j) ** 9 == Fraction(numerator(t), cleared ** 9)
            regular_points += 1
        node = Fraction(-j * (n - j))
        for coefficients in [[1], [0, 1], [1, 1], [3, -2, 5], [Fraction(2, 3), Fraction(-7, 5), 1]]:
            eval_w = sum(c * node ** degree for degree,c in enumerate(coefficients))
            assert Fraction(numerator(Fraction(-j)), deleted ** 9) * eval_w == expected * eval_w
            weighted_values += 1
assert Fraction(factorial(0) ** 7, 1) == 1
arithmetic = {"status": "PASS", "parameter_range": "0 <= n <= 12; 0 <= j <= n",
              "local_coefficients_checked": local_values, "regular_point_clearings_checked": regular_points,
              "weighted_coefficients_checked": weighted_values,
              "checks_are_finite_regressions_not_the_universal_proof": True}
(OUT / "exact-arithmetic.json").write_text(json.dumps(arithmetic, indent=2) + "\n")
compiler = subprocess.run(["lean", "--version"], cwd=PROJECT, capture_output=True, text=True, check=True).stdout.strip()
passed = len(steps) == 2 and all(row["exit_code"] == 0 for row in steps) and not bad and not missing and "version 4.33.1," in compiler
receipt = {"status": "PASS" if passed else "FAIL", "source_sha256": EXPECTED,
           "original_source_unchanged_after_review": hashlib.sha256(source.read_bytes()).hexdigest() == EXPECTED,
           "independent_copy_exact_bytes": (PROJECT / "CoefficientMap.lean").read_bytes() == data,
           "compiler": compiler, "mathlib_revision": PIN, "steps": steps,
           "log_sha256": hashlib.sha256(log).hexdigest(), "axiom_reports": reports,
           "missing_original_reports": missing, "unexpected_axioms": bad,
           "finite_arithmetic": arithmetic,
           "PNT_or_task_binary_cache_reused": False, "dependency_reuse": "Exact pinned Mathlib package source/build cache only",
           "mathematical_source_edits": [], "scope_or_shared_root_edits": [],
           "frozen_advanced_package_edits": [], "network_API_credential_operations": False}
(OUT / "independent-compile-receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
print(json.dumps({"status": receipt["status"], "source_sha256": EXPECTED, "unexpected_axioms": bad,
                  "local_values": local_values, "regular_points": regular_points, "weighted_values": weighted_values}))
raise SystemExit(0 if passed else 1)
