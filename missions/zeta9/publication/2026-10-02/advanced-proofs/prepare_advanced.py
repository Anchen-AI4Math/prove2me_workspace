"""Explicit allow-list preparation of the standalone advanced proof project.

No network, API, credentials, binary artifacts, or broad workspace traversal.
All imported upstream mathematical sources retain their exact original bytes.
"""
from pathlib import Path
import hashlib
import json

OUT = Path(__file__).resolve().parent
TASK = OUT.parents[2]
ROOT = TASK.parents[1]
PROJECT = OUT / "project"
PNT = TASK / "verification/formalization-pnt-dependency-2026-10-02"
COEFF = TASK / "formalization/platform/coefficient"
PIN = "0df444a360eaa60ab8c11dca51a86af692955474"

def load(path):
    return json.loads(path.read_text(encoding="utf-8-sig"))

def sha(data):
    return hashlib.sha256(data).hexdigest()

sources = []

def copy(source, target, role, expected=None, commit=None):
    data = source.read_bytes()
    if expected is not None:
        assert sha(data) == expected, str(source)
    path = PROJECT / target
    path.parent.mkdir(parents=True, exist_ok=True)
    assert not path.exists() or path.read_bytes() == data, "Prepared source drift: " + target
    path.write_bytes(data)
    sources.append({"path": target, "workspace_source": source.relative_to(ROOT).as_posix(),
                    "role": role, "sha256": sha(data), "bytes": len(data),
                    "source_commit": commit, "source_bytes_preserved": True})

def write(target, text):
    path = PROJECT / target
    path.parent.mkdir(parents=True, exist_ok=True)
    data = text.encode("utf-8")
    assert not path.exists() or path.read_bytes() == data, "Prepared auxiliary drift: " + target
    path.write_bytes(data)

coefficient_audit = load(COEFF / "integration-audit.json")
coefficient_review = load(COEFF / "independent-integration-review.json")
assert coefficient_audit["status"] == "PASS" and coefficient_review["verdict"] == "PASS"
assert int((COEFF / "task-build-exit.txt").read_text()) == 0
first_review = load(TASK / "formalization/platform/independent-statement-review.json")
kernel_receipt = load(PNT / "kernel-replay-receipt.json")
assert kernel_receipt["verdict"] == "PASS"
transfer_receipt = load(TASK / "verification/formalization-2026-10-02/pnt-transfer-final-receipt.json")
assert transfer_receipt["actual_exit_code"] == 0
assert transfer_receipt["source_sha256"] == "6c56d052ae48b44e76d40e7a08fcfd6ca8d232b5bc7882430bfbf48b85bb2c8b"

shared = [
    "Definitions/Def_ZetaNine_ShortZeroCoefficient.lean",
    "Solutions/Sol_ZetaNine_ShortZeroCoefficient_A_even_signed_lower.lean",
    "Solutions/Sol_ZetaNine_ShortZeroCoefficient_A_ne_zero_of_even.lean",
    "Theorems/Thm_ZetaNine_ShortZeroCoefficient_A_even_signed_lower.lean",
    "Theorems/Thm_ZetaNine_ShortZeroCoefficient_A_ne_zero_of_even.lean",
]
for path in shared:
    copy(ROOT / path, path, "independently reviewed C3 shared module", coefficient_audit["sha256"][path])
for path in ["Definitions/Def_ZetaNine_HarmonicStability.lean",
             "Solutions/Sol_ZetaNine_HarmonicStability_harmonic_den_dvd_lcm_power.lean"]:
    copy(ROOT / path, path, "actual harmonic import dependency from frozen first batch", first_review["sha256"][path])

native = [
    ("ShortZeroCoefficient.lean", "9bf18387c4a51dd6dca03ecf197fc1cd85337fabf5b1d3421e2302e452347dbc", "actual all-parameter C3 native proof"),
    ("PNTTransfer.lean", transfer_receipt["source_sha256"], "actual unconditional PNT transfer and three harmonic endpoints"),
    ("HarmonicAsymptotic.lean", transfer_receipt["dependent_task_source_sha256"], "original conditional bridge; its PNT inputs are discharged by actual PNTTransfer"),
    ("HarmonicPrimeValuation.lean", "bb7df45433a3441520c343356548ac2cd279e05a4b10ff59b8dd3a13d13a99fb", "actual harmonic finite prime and exception-product proof"),
]
for name, expected, role in native:
    path = "missions/zeta9/formalization/" + name
    copy(ROOT / path, path, role, expected)

kernel_manifest = load(PNT / "kernel-source-manifest.json")
assert len(kernel_manifest["sources"]) == 23
for row in kernel_manifest["sources"]:
    origin = "external" if row["module"].startswith("PrimeNumberTheoremAnd") else "architect"
    copy(PNT / origin / row["path"], row["path"], "fixed upstream genuine PNT/Architect import closure",
         row["sha256"], row["source_commit"])
for origin, name in [("external", "PrimeNumberTheoremAnd-APACHE-2.0.txt"),
                     ("architect", "LeanArchitect-APACHE-2.0.txt")]:
    copy(PNT / origin / "LICENSE", "licenses/" + name, "unaltered upstream Apache-2.0 license",
         "c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4")
copy(PNT / "project/PNTKernelAudit.lean", "Audit/Kernel.lean", "explicit closed statement audit of genuine MediumPNT")

for source, target in [
    (TASK / "research/short-zero-coefficient-nonvanishing.md", "research/short-zero-coefficient-nonvanishing.md"),
    (TASK / "research/harmonic-denominator-stability-2026-10-01.md", "research/harmonic-denominator-stability-2026-10-01.md"),
    (COEFF / "integration-audit.json", "audit/coefficient/integration-audit.json"),
    (COEFF / "independent-integration-review.json", "audit/coefficient/independent-integration-review.json"),
    (COEFF / "integration-provenance.json", "audit/coefficient/integration-provenance.json"),
    (COEFF / "staged-build.log", "audit/coefficient/staged-build.log"),
    (COEFF / "staged-build-exit.txt", "audit/coefficient/staged-build-exit.txt"),
    (COEFF / "task-build.log", "audit/coefficient/task-build.log"),
    (COEFF / "task-build-exit.txt", "audit/coefficient/task-build-exit.txt"),
    (PNT / "kernel-replay-receipt.json", "audit/upstream-pnt/kernel-replay-receipt.json"),
    (PNT / "kernel-source-manifest.json", "audit/upstream-pnt/kernel-source-manifest.json"),
    (PNT / "kernel-build.log", "audit/upstream-pnt/kernel-build.log"),
    (PNT / "kernel-axiom-audit.log", "audit/upstream-pnt/kernel-axiom-audit.log"),
    (PNT / "external/import-closure.json", "audit/upstream-pnt/pnt-import-closure.json"),
    (PNT / "architect/import-closure.json", "audit/upstream-pnt/architect-import-closure.json"),
    (TASK / "verification/formalization-2026-10-02/pnt-transfer-final-receipt.json", "audit/native-pnt/pnt-transfer-final-receipt.json"),
    (TASK / "verification/formalization-2026-10-02/pnt-transfer-final-lean.log", "audit/native-pnt/pnt-transfer-final-lean.log"),
]:
    copy(source, target, "offline mathematical source or verification record; no platform/API receipt")
for tag in ["original", "definition", "0_reference", "0_solution", "1_reference", "1_solution"]:
    copy(COEFF / ("types-" + tag + ".jsonl"), "audit/coefficient/types-" + tag + ".jsonl",
         "actual original/staged elaborated type and definition value report")

write("lean-toolchain", "leanprover/lean4:v4.33.1\n")
lock = load(ROOT / "lake-manifest.json")
assert next(row for row in lock["packages"] if row["name"] == "mathlib")["rev"] == PIN
lock["name"] = "zeta9AdvancedProofs"
write("lake-manifest.json", json.dumps(lock, indent=2) + "\n")
write("lakefile.lean", '''import Lake
open Lake DSL

package zeta9AdvancedProofs

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "0df444a360eaa60ab8c11dca51a86af692955474"

lean_lib Architect where
  roots := #[`Architect]
  globs := #[.one `Architect, .submodules `Architect]

lean_lib PrimeNumberTheoremAnd where
  roots := #[`PrimeNumberTheoremAnd.MediumPNT]
  globs := #[.submodules `PrimeNumberTheoremAnd]

lean_lib Definitions where
  roots := #[]
  globs := #[.submodules `Definitions]

lean_lib Theorems where
  roots := #[]
  globs := #[.submodules `Theorems]

lean_lib Solutions where
  roots := #[]
  globs := #[.submodules `Solutions]

lean_lib Native where
  roots := #[]
  globs := #[.submodules `missions.zeta9.formalization]

@[default_target]
lean_lib Audit where
  roots := #[]
  globs := #[.submodules `Audit]
''')
write("Audit/C3Signed.lean", '''import Solutions.Sol_ZetaNine_ShortZeroCoefficient_A_even_signed_lower

set_option autoImplicit false
open ZetaNine.ShortZeroCoefficient

namespace ZetaNine.AdvancedAudit
theorem checked_c3_signed_lower (d m : ℕ) :
    (28 : ℤ) * ((2 * d).choose d : ℤ) * ((3 * d).choose d : ℤ) *
      ((d + m).choose m : ℤ) ^ 14 ≤ (-1 : ℤ) ^ (m + d) * A (2 * d) m :=
  solution d m
#print axioms solution
#print axioms checked_c3_signed_lower
end ZetaNine.AdvancedAudit
''')
write("Audit/C3Nonzero.lean", '''import Solutions.Sol_ZetaNine_ShortZeroCoefficient_A_ne_zero_of_even

set_option autoImplicit false
open ZetaNine.ShortZeroCoefficient

namespace ZetaNine.AdvancedAudit
theorem checked_c3_nonzero (n m : ℕ) (hn : Even n) : A n m ≠ 0 :=
  solution n m hn
#print axioms solution
#print axioms checked_c3_nonzero
end ZetaNine.AdvancedAudit
''')
write("Audit/NativeC3.lean", '''import missions.zeta9.formalization.ShortZeroCoefficient

#print axioms ZetaNine.ShortZeroCoefficient.A_even_signed_lower
#print axioms ZetaNine.ShortZeroCoefficient.A_ne_zero_of_even
''')
write("Audit/PNT.lean", '''import missions.zeta9.formalization.PNTTransfer

set_option autoImplicit false
open Filter ZetaNine.HarmonicStability

namespace ZetaNine.AdvancedAudit
theorem checked_psi_rate :
    Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (nhds 1) := psi_pnt_rate

theorem checked_harmonic_rate (s : ℕ) (hs : 0 < s) :
    Tendsto (fun N : ℕ => logDen (harmonicPower s N) / (N : ℝ))
      atTop (nhds (s : ℝ)) := harmonic_log_den_rate s hs

theorem checked_perturbed_harmonic_rate (s : ℕ) (hs : 0 < s) (r : ℕ → ℚ)
    (hr : Tendsto (fun N => logDen (r N) / (N : ℝ)) atTop (nhds 0)) :
    Tendsto (fun N : ℕ => logDen (harmonicPower s N + r N) / (N : ℝ))
      atTop (nhds (s : ℝ)) := harmonic_perturbed_log_den_rate s hs r hr

theorem checked_nine_double_harmonic_rate :
    Tendsto (fun M : ℕ => logDen (harmonicPower 9 (2 * M)) / (M : ℝ))
      atTop (nhds 18) := harmonic_nine_double_log_den_rate

#print axioms MediumPNT
#print axioms psi_pnt_rate
#print axioms theta_pnt
#print axioms lcm_pnt
#print axioms harmonic_log_den_rate
#print axioms harmonic_perturbed_log_den_rate
#print axioms harmonic_nine_double_log_den_rate
#print axioms checked_psi_rate
#print axioms checked_harmonic_rate
#print axioms checked_perturbed_harmonic_rate
#print axioms checked_nine_double_harmonic_rate
end ZetaNine.AdvancedAudit
''')

upstream = {
    "PrimeNumberTheoremAnd": {"repository": "https://github.com/AlexKontorovich/PrimeNumberTheoremAnd",
        "commit": kernel_manifest["pnt_commit"], "source_modules": 14, "license": "Apache-2.0"},
    "LeanArchitect": {"repository": "https://github.com/hanwenzhu/LeanArchitect",
        "commit": kernel_manifest["architect_commit"], "source_modules": 9, "license": "Apache-2.0",
        "upstream_toolchain": "v4.33.0", "actual_replay_toolchain": "v4.33.1"},
    "mathematical_source_changes": [], "blueprint_comments_and_attributes_preserved": True,
}
write("UPSTREAM.json", json.dumps(upstream, indent=2) + "\n")
(OUT / "prepared-source-manifest.json").write_text(json.dumps({"sources": sources}, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"project": str(PROJECT), "source_and_audit_files": len(sources), "upstream_modules": 23,
                  "native_PNTTransfer_sha256": transfer_receipt["source_sha256"], "platform_acceptance_claimed": False}))
