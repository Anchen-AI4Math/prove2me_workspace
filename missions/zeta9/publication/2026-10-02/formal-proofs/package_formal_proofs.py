"""Explicit, credential-free packaging of nine reviewed formal solutions.

No network, platform, gh, recursive workspace scan, or dependency archive.
The pre-existing research ZIP is never opened for writing.
"""
from pathlib import Path
import hashlib
import json
import re
import zipfile

OUT = Path(__file__).resolve().parent
TASK = OUT.parents[2]
ROOT = TASK.parents[1]
PROJECT = OUT / "project"
PIN = "0df444a360eaa60ab8c11dca51a86af692955474"
ZIP = OUT / "zeta9-formal-proofs-2026-10-02.zip"
RESEARCH_ZIP = OUT.parent / "zeta9-research-2026-10-02.zip"
RESEARCH_SHA = "68a821653ae08e4f0b2917c770215dfbe60af2670ea3cb6a87521f75b665f2a0"
FIRST = TASK / "formalization/platform"
SECOND = FIRST / "prime-valuation"

def sha_bytes(data):
    return hashlib.sha256(data).hexdigest()

def read_json(path):
    return json.loads(path.read_text(encoding="utf-8-sig"))

first_review = read_json(FIRST / "independent-statement-review.json")
first_build = read_json(FIRST / "local-build-audit.json")
second_review = read_json(SECOND / "independent-integration-review.json")
first_problems = read_json(FIRST / "problems-request.json")["problems"]
second_problems = read_json(SECOND / "problems-request.json")["problems"]
definitions = read_json(FIRST / "definitions-request.json") + read_json(SECOND / "definitions-request.json")
assert first_review["overall_status"] == "PASS"
assert second_review["verdict"] == "PASS"
assert first_build["task_build_exit"] == 0 and first_build["no_sorryAx"] is True
assert len(first_problems) == 6 and len(second_problems) == 3 and len(definitions) == 4

PROJECT.mkdir(parents=True, exist_ok=True)
members = {}

def copy(source, member, role, reviewed_sha=None):
    member = str(member).replace("\\", "/")
    assert not member.startswith("/") and ".." not in Path(member).parts
    data = source.read_bytes()
    if reviewed_sha:
        assert sha_bytes(data) == reviewed_sha, (member, "reviewed source drift")
    target = PROJECT / member
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(data)
    members[member] = {"path": member, "bytes": len(data), "sha256": sha_bytes(data),
                       "role": role, "workspace_source": source.relative_to(ROOT).as_posix(),
                       "matches_frozen_review_sha": bool(reviewed_sha)}

def generate(member, text, role):
    data = text.encode("utf-8")
    target = PROJECT / member
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(data)
    members[member] = {"path": member, "bytes": len(data), "sha256": sha_bytes(data),
                       "role": role, "workspace_source": None,
                       "matches_frozen_review_sha": False}

for d in definitions:
    member = d["local_path"]
    digest = first_review["sha256"].get(member) or second_review["sha256"][member]
    copy(ROOT / member, member, "reviewed shared definition", digest)
for p in first_problems + second_problems:
    member = p["local_solution"]
    digest = first_review["sha256"].get(member) or second_review["sha256"][member]
    assert re.search(r"(?m)^theorem solution\b", (ROOT / member).read_text(encoding="utf-8"))
    copy(ROOT / member, member, "reviewed complete solution", digest)
    if p in first_problems:
        assert digest == first_build["solution_sha256"][p["theorem_name"]]

assert sum(m["role"] == "reviewed shared definition" for m in members.values()) == 4
assert sum(m["role"] == "reviewed complete solution" for m in members.values()) == 9

evidence = [
    (FIRST / "independent-statement-review.json", "audit/first-batch/independent-statement-review.json"),
    (FIRST / "local-build-audit.json", "audit/first-batch/local-build-audit.json"),
    (FIRST / "definitions-build.log", "audit/first-batch/definitions-build.log"),
    (FIRST / "task-build.log", "audit/first-batch/task-build.log"),
    (FIRST / "task-build-exit.txt", "audit/first-batch/task-build-exit.txt"),
    (FIRST / "prime-valuation-review.json", "audit/prime-valuation/source-statement-review.json"),
    (SECOND / "independent-integration-review.json", "audit/prime-valuation/independent-integration-review.json"),
    (SECOND / "integration-provenance.json", "audit/prime-valuation/integration-provenance.json"),
    (SECOND / "task-build.log", "audit/prime-valuation/task-build.log"),
    (SECOND / "task-build-exit.txt", "audit/prime-valuation/task-build-exit.txt"),
]
for source, member in evidence:
    copy(source, member, "current independent review or actual build evidence")

for name in ["direction-arithmetic-next-2026-10-02.md", "new-linear-form-route-repair-2026-10-02.md",
             "harmonic-denominator-stability-2026-10-01.md"]:
    copy(TASK / "research" / name, "research/" + name, "original mathematical source",
         first_review["sha256"]["research/" + name])

copy(ROOT / "lean-toolchain", "lean-toolchain", "fixed Lean toolchain")
assert (PROJECT / "lean-toolchain").read_text(encoding="utf-8").strip() == "leanprover/lean4:v4.33.1"
lock = read_json(ROOT / "lake-manifest.json")
assert next(p for p in lock["packages"] if p["name"] == "mathlib")["rev"] == PIN
lock["name"] = "zeta9FormalProofs"
generate("lake-manifest.json", json.dumps(lock, ensure_ascii=False, indent=2) + "\n",
         "minimal-project exact dependency lock; all original pinned package revisions retained")
generate("lakefile.lean", '''import Lake
open Lake DSL

package zeta9FormalProofs where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "0df444a360eaa60ab8c11dca51a86af692955474"

lean_lib Definitions where
  roots := #[]
  globs := #[.submodules `Definitions]

@[default_target]
lean_lib Solutions where
  roots := #[]
  globs := #[.submodules `Solutions]
''', "minimal project configuration: only four definitions and nine complete solutions")

appendix_audit = read_json(TASK / "verification/formalization-harmonic-asymptotic-2026-10-02/mathlib-pnt-audit.json")
for name in ["HarmonicAsymptotic.lean", "HarmonicPrimeValuation.lean"]:
    member = "missions/zeta9/formalization/" + name
    copy(TASK / "formalization" / name, member,
         "additional research source; conditional PNT transfer is not one of the nine solution targets",
         appendix_audit["sha256"][member])
for name in ["README.md", "lean-check.log", "mathlib-pnt-audit.json"]:
    copy(TASK / "verification/formalization-harmonic-asymptotic-2026-10-02" / name,
         "audit/conditional-harmonic-transfer/" + name,
         "conditional appendix documentation or compilation evidence")

names = "\n".join("- `" + p["theorem_name"] + "`" for p in first_problems + second_problems)
readme = '''# Zeta(9): nine reviewed complete Lean proofs

Snapshot date: 2026-10-02. This attachment supplements the immutable research
release; it does not replace or modify `zeta9-research-2026-10-02.zip`.

There are exactly **four shared Definitions files and nine complete Solutions
files**. Their bytes equal the frozen independently reviewed and task-built
workspace sources, with SHA-256 recorded in `source-manifest.json`. Every
top-level `solution` has an actual Lean 4.33.1 axiom report containing only
`propext`, `Classical.choice`, and `Quot.sound`. No reference theorem stubs
are included or imported by these solution modules.

Platform state at this handoff: submitted definitions are **Pending** and the
main `ZetaNine.irrational_zeta_nine` goal remains **Open**. Local compilation
does not assert platform acceptance, published theorem proof status, a full
formalization of all research, or a proof of irrationality.

## Nine locally verified target solutions

''' + names + '''

The six first-batch and three prime-valuation targets retain every original
parameter and hypothesis. The arbitrary-filter stability theorem retains its
explicit unperturbed-rate input; the finite prime theorems retain their real
prefix numerator-unit and fixed exceptional-product conditions. No denominator
estimate or asymptotic claim is hidden in a definition.

## Rebuild

Install Lean using the included `lean-toolchain` (version 4.33.1). Mathlib is
fixed at `0df444a360eaa60ab8c11dca51a86af692955474`; every transitive package
revision is pinned in `lake-manifest.json`.

From this extracted directory:

```text
lake exe cache get
lake build Solutions
python verify_package.py
```

Dependency acquisition requires network access when the pinned dependencies
and their cache are not already installed. No Lean toolchain, Mathlib source,
dependency cache, `.olean`, `.git`, credentials or account receipts are bundled.
This minimal `Solutions` target contains exactly the nine proofs above and
their four actual definition dependencies; it is unrelated to any aggregate
target of the original multi-mission workspace.

The two original scoped build logs contain warning lines from deliberately
registered target stubs elsewhere in the original zeta9 task. Those stubs are
absent from this package. The relevant nine Solutions axiom lines are all
standard only. A pre-existing linter warning in the frozen center-denominator
proof is preserved rather than modifying its reviewed source bytes.

The fresh isolated rebuild of this exact minimal project is recorded under
`audit/package-rebuild`. It rebuilt all thirteen shared modules, with nine
standard-only solution axiom reports and no target theorem stubs. It used
already installed exact pinned dependencies outside the archive and disabled
network build-cache downloads. No dependency source or cache is bundled.

## Conditional harmonic appendix

`missions/zeta9/formalization/HarmonicAsymptotic.lean` is additional checked
research source, **not a tenth registered solution**. It derives the actual
full harmonic denominator rate and its perturbation transfer, including the
order-nine `N=2M` rate 18, from exactly two explicit PNT inputs:

- `Chebyshev.theta x / x → 1` as real `x → ∞`;
- `log (Nat.lcmUpto N) / N → 1` as natural `N → ∞`.

These are theorem arguments. There is no assumed harmonic baseline, custom
PNT axiom or claim to have proved PNT. The fixed Mathlib PNT theorem search
and actual compilation evidence are under `audit/conditional-harmonic-transfer`.
The original finite-prime source is included solely as its actual import
dependency, without cached binary files. After the main rebuild, compile
the appendix from this directory in PowerShell:

```powershell
lake env lean -o missions/zeta9/formalization/HarmonicPrimeValuation.olean missions/zeta9/formalization/HarmonicPrimeValuation.lean
$env:LEAN_PATH = (Get-Location).Path
lake env lean missions/zeta9/formalization/HarmonicAsymptotic.lean
```

## Evidence and integrity

The `audit` directory contains only the current independent mathematical
reviews, exact source-match audits and actual build logs. Original mathematical
notes are under `research`; their wider research links refer to the separate
dated research release rather than promising those linked files in this small
proof attachment. Documentation and audits distinguish written mathematics,
local Lean verification, outstanding PNT dependencies and platform acceptance.

`source-manifest.json` lists each package member's exact size, SHA-256 and
provenance. It excludes itself to avoid a self-referential digest. The archive's
SHA-256 and packaging verification report are provided alongside the ZIP.
'''
generate("README.md", readme, "reviewable proof package handoff and reproducibility instructions")
generate("verify_package.py", '''from pathlib import Path
import hashlib, json
root = Path(__file__).resolve().parent
manifest = json.loads((root / "source-manifest.json").read_text(encoding="utf-8"))
for row in manifest["files"]:
    data = (root / row["path"]).read_bytes()
    assert len(data) == row["bytes"], row["path"]
    assert hashlib.sha256(data).hexdigest() == row["sha256"], row["path"]
print("PASS: every manifested source and evidence member has its original bytes")
''', "standalone standard-library member verification")

# An offline isolated rebuild log can be added after creating this staging project.
for generated_log in ["minimal-project-build.log", "minimal-project-build-exit.txt"]:
    path = OUT / generated_log
    if path.exists():
        copy(path, "audit/package-rebuild/" + generated_log,
             "actual fresh isolated package build using external existing pinned dependencies")

fresh_build_verified = False
if (OUT / "minimal-project-build.log").exists():
    fresh_exit = (OUT / "minimal-project-build-exit.txt").read_text(encoding="utf-8-sig").strip()
    fresh_log = (OUT / "minimal-project-build.log").read_text(encoding="utf-8-sig")
    assert fresh_exit == "0" and "Build completed successfully" in fresh_log
    for p in first_problems + second_problems:
        line = next(line for line in fresh_log.splitlines()
                    if p["local_solution"] in line and "depends on axioms" in line)
        assert "[propext, Classical.choice, Quot.sound]" in line and "sorryAx" not in line
    assert "Theorems.Thm_" not in fresh_log
    fresh_build_verified = True

manifest = {
    "schema_version": 1,
    "date": "2026-10-02",
    "lean_version": "4.33.1",
    "mathlib_revision": PIN,
    "shared_definitions": 4,
    "complete_solutions": 9,
    "platform_definition_state": "Pending",
    "main_goal_state": "Open",
    "platform_acceptance_claimed": False,
    "conditional_appendix_is_registered_solution": False,
    "self_hash_exclusion": "source-manifest.json excludes itself; its ZIP member bytes are identical to the standalone manifest.",
    "files": [members[name] for name in sorted(members)],
}
manifest_bytes = (json.dumps(manifest, ensure_ascii=False, indent=2) + "\n").encode("utf-8")
(PROJECT / "source-manifest.json").write_bytes(manifest_bytes)
(OUT / "source-manifest.json").write_bytes(manifest_bytes)
(OUT / "README.md").write_text(readme, encoding="utf-8")

deny_parts = {".git", ".lake", "__pycache__", "node_modules", "credentials", "credentials.json"}
for name in members:
    assert not (set(Path(name).parts) & deny_parts), name
    assert Path(name).suffix not in {".olean", ".ilean", ".dll", ".exe", ".key", ".pem"}, name
    data = (PROJECT / name).read_bytes()
    assert not re.search(rb"eyJ[A-Za-z0-9_-]{12,}\.[A-Za-z0-9_-]{15,}\.[A-Za-z0-9_-]{15,}", data), name
    assert not re.search(rb"gh[opusr]_[A-Za-z0-9]{20,}|github_pat_[A-Za-z0-9_]{20,}|-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----", data), name

with zipfile.ZipFile(ZIP, "w", zipfile.ZIP_DEFLATED, compresslevel=9) as z:
    for name in sorted(members):
        z.writestr(name, (PROJECT / name).read_bytes())
    z.writestr("source-manifest.json", manifest_bytes)

with zipfile.ZipFile(ZIP) as z:
    assert z.testzip() is None
    assert set(z.namelist()) == set(members) | {"source-manifest.json"}
    assert len(z.namelist()) == len(members) + 1
    for name, row in members.items():
        data = z.read(name)
        assert len(data) == row["bytes"] and sha_bytes(data) == row["sha256"]
        if row["workspace_source"]:
            assert data == (ROOT / row["workspace_source"]).read_bytes(), name
    assert z.read("source-manifest.json") == manifest_bytes

zip_sha = sha_bytes(ZIP.read_bytes())
assert sha_bytes(RESEARCH_ZIP.read_bytes()) == RESEARCH_SHA, "Immutable original research archive hash drift"
(OUT / "SHA256SUMS.txt").write_text(f"{zip_sha}  {ZIP.name}\n{sha_bytes(manifest_bytes)}  source-manifest.json\n", encoding="utf-8")
report = {
    "verdict": "PASS", "zip": ZIP.name, "zip_bytes": ZIP.stat().st_size,
    "zip_sha256": zip_sha, "zip_members": len(members) + 1,
    "all_zip_members_match_manifest": True,
    "all_copied_members_match_current_workspace_bytes": True,
    "all_13_shared_sources_match_frozen_independent_review_sha": True,
    "shared_source_count": 13, "complete_solution_count": 9,
    "sensitive_paths_or_token_patterns_found": False,
    "caches_and_binary_files_included": False,
    "existing_research_zip_modified": False,
    "immutable_research_zip_sha256": RESEARCH_SHA,
    "network_or_platform_operations": False,
    "fresh_package_build_record_included": fresh_build_verified,
    "fresh_package_build_exit": 0 if fresh_build_verified else None,
    "fresh_package_build_solution_axiom_reports": 9 if fresh_build_verified else 0,
}
(OUT / "package-validation.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
print(json.dumps(report, ensure_ascii=True))
