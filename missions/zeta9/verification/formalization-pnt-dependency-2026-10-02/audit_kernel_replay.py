"""Credential-free evidence audit of the actual fixed-source PNT replay."""
from pathlib import Path
import hashlib
import json

BASE = Path(__file__).resolve().parent
PROJECT = BASE / "project"

def load(path):
    return json.loads(path.read_text(encoding="utf-8-sig"))

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

assert (BASE / "kernel-build-exit.txt").read_text(encoding="utf-8-sig").strip() == "0"
assert (BASE / "kernel-axiom-audit-exit.txt").read_text(encoding="utf-8-sig").strip() == "0"
build_log = (BASE / "kernel-build.log").read_text(encoding="utf-8-sig")
axiom_log = (BASE / "kernel-axiom-audit.log").read_text(encoding="utf-8-sig")
assert "Build completed successfully" in build_log
assert "'MediumPNT' depends on axioms: [propext, Classical.choice, Quot.sound]" in build_log
assert "'MediumPNT' depends on axioms: [propext, Classical.choice, Quot.sound]" in axiom_log
assert "'ZetaNine.ExternalPNT.checked_medium_pnt' depends on axioms: [propext, Classical.choice, Quot.sound]" in axiom_log
assert "sorryAx" not in build_log and "sorryAx" not in axiom_log

manifest = load(BASE / "kernel-source-manifest.json")
assert len(manifest["sources"]) == 23
for row in manifest["sources"]:
    assert sha(PROJECT / row["path"]) == row["sha256"], row["path"]
    origin = "architect" if row["module"].startswith("Architect") else "external"
    assert (PROJECT / row["path"]).read_bytes() == (BASE / origin / row["path"]).read_bytes()
    assert row["compatibility_changes"] == []

hashes = {}
for name in ["project/lakefile.lean", "project/lake-manifest.json", "project/lean-toolchain",
             "project/PNTKernelAudit.lean", "kernel-build.log", "kernel-build-exit.txt",
             "kernel-axiom-audit.log", "kernel-axiom-audit-exit.txt", "kernel-source-manifest.json",
             "external/import-closure.json", "architect/import-closure.json",
             "external/LICENSE", "architect/LICENSE", "project/licenses/external-LICENSE",
             "project/licenses/architect-LICENSE", "project/licenses/README.md"]:
    if name == "project/licenses/README.md" and not (BASE / name).exists():
        continue
    hashes[name] = sha(BASE / name)
artifact = "project/.lake/build/lib/lean/PrimeNumberTheoremAnd/MediumPNT.olean"
hashes[artifact] = sha(BASE / artifact)

receipt = {
    "verdict": "PASS",
    "date": "2026-10-02",
    "lean_version": "4.33.1",
    "mathlib_revision": "0df444a360eaa60ab8c11dca51a86af692955474",
    "pnt_commit": "55270df807213fc3584523d09e0311d7dc073ff5",
    "architect_commit": "0f5bc0209ae02a7fb0cfe7d113d4094542cee221",
    "build_command": "lake --no-cache build PrimeNumberTheoremAnd.MediumPNT",
    "build_exit": 0,
    "build_jobs": 3621,
    "explicit_statement_audit_command": "lake env lean PNTKernelAudit.lean",
    "explicit_statement_audit_exit": 0,
    "pnt_source_modules": 14,
    "architect_source_modules": 9,
    "all_23_source_bytes_equal_fixed_upstream_snapshots": True,
    "blueprint_attributes_and_comments_preserved": True,
    "mathematical_source_edits": [],
    "configuration_adjustments": [{
        "change": "Declare .one Architect in the isolated Architect library glob, in addition to .submodules Architect.",
        "reason": "Initial isolated configuration omitted the root module from library membership; lake query Architect:modules listed only eight submodules. The corrected configuration replayed all original Architect sources unchanged.",
        "first_attempt_log": "kernel-build-attempt1.log",
    }],
    "architect_toolchain_compatibility": {
        "upstream": "leanprover/lean4:v4.33.0",
        "actual_replay": "leanprover/lean4:v4.33.1",
        "all_nine_original_sources_compiled": True,
    },
    "actual_upstream_target": "MediumPNT",
    "explicit_closed_statement": "exists c : Real, 0 < c and IsBigO atTop (fun x => Chebyshev.psi x - x) (fun x => x * exp (-c * (log x)^(1/10)))",
    "extra_assumptions_in_explicit_checked_statement": [],
    "axioms": ["propext", "Classical.choice", "Quot.sound"],
    "axiom_reports": ["MediumPNT in its original source build", "MediumPNT in separate imported statement audit", "ZetaNine.ExternalPNT.checked_medium_pnt"],
    "sorryAx_found": False,
    "warnings": "Upstream deprecated Mathlib lemma names only; preserved without source migration.",
    "dependency_reuse": "Existing exact pinned Mathlib package sources/build cache through a checked directory junction; cache downloading disabled.",
    "network_or_platform_calls": False,
    "shared_environment_upgrade": False,
    "root_zeta_irrationality_closed": False,
    "hashes": hashes,
    "licenses_copied_exactly": {
        "pnt": (BASE / "external/LICENSE").read_bytes() == (PROJECT / "licenses/external-LICENSE").read_bytes(),
        "architect": (BASE / "architect/LICENSE").read_bytes() == (PROJECT / "licenses/architect-LICENSE").read_bytes(),
    },
}
assert all(receipt["licenses_copied_exactly"].values())
(BASE / "kernel-replay-receipt.json").write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"verdict": receipt["verdict"], "original_sources_checked": 23,
                  "source_changes": 0, "axioms": receipt["axioms"], "receipt": "kernel-replay-receipt.json"}))
