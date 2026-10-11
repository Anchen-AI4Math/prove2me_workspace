"""Prepare the exact PNT and Architect import closure for offline replay.

Only recorded source files are copied. No network operation or shared
environment update occurs. The isolated package reuses installed Mathlib.
"""
from pathlib import Path
import hashlib
import json

BASE = Path(__file__).resolve().parent
TASK = BASE.parents[1]
WORKSPACE = TASK.parents[1]
PROJECT = BASE / "project"
PIN = "0df444a360eaa60ab8c11dca51a86af692955474"

def load(path):
    return json.loads(path.read_text(encoding="utf-8-sig"))

def digest(data):
    return hashlib.sha256(data).hexdigest()

pnt = load(BASE / "external/import-closure.json")
architect = load(BASE / "architect/import-closure.json")
assert pnt["commit"] == "55270df807213fc3584523d09e0311d7dc073ff5"
assert architect["commit"] == "0f5bc0209ae02a7fb0cfe7d113d4094542cee221"
assert len(pnt["modules"]) == 14 and len(architect["modules"]) == 9
sources = []
for origin, closure in [("external", pnt), ("architect", architect)]:
    for module, info in closure["modules"].items():
        data = (BASE / origin / info["path"]).read_bytes()
        assert digest(data) == info["sha256"], (origin, module)
        target = PROJECT / info["path"]
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        sources.append({"module": module, "path": info["path"],
                        "source_commit": closure["commit"], "sha256": digest(data),
                        "bytes": len(data), "original_bytes_preserved": True,
                        "compatibility_changes": []})

toolchain = (BASE / "external/lean-toolchain").read_bytes()
assert toolchain.decode("utf-8").strip() == "leanprover/lean4:v4.33.1"
(PROJECT / "lean-toolchain").write_bytes(toolchain)
for origin in ["external", "architect"]:
    license_file = BASE / origin / "LICENSE"
    target = PROJECT / "licenses" / (origin + "-LICENSE")
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(license_file.read_bytes())

lock = load(WORKSPACE / "lake-manifest.json")
assert next(p for p in lock["packages"] if p["name"] == "mathlib")["rev"] == PIN
assert next(p for p in load(BASE / "external/lake-manifest.json")["packages"]
            if p["name"] == "mathlib")["rev"] == PIN
lock["name"] = "zeta9PntKernelReplay"
(PROJECT / "lake-manifest.json").write_text(json.dumps(lock, indent=2) + "\n", encoding="utf-8")
(PROJECT / "lakefile.lean").write_text('''import Lake
open Lake DSL

package zeta9PntKernelReplay

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "0df444a360eaa60ab8c11dca51a86af692955474"

lean_lib Architect where
  roots := #[`Architect]
  globs := #[.one `Architect, .submodules `Architect]

lean_lib PrimeNumberTheoremAnd where
  roots := #[`PrimeNumberTheoremAnd.MediumPNT]
  globs := #[.submodules `PrimeNumberTheoremAnd]
''', encoding="utf-8")

manifest = {
    "lean_version": "4.33.1", "mathlib_revision": PIN,
    "pnt_commit": pnt["commit"], "architect_commit": architect["commit"],
    "pnt_modules": 14, "architect_modules": 9,
    "mathematical_source_changes": [],
    "blueprint_attributes_and_comments_preserved": True,
    "dependency_handling": "Exact upstream source closures vendored only inside this isolated task project; existing external pinned Mathlib packages reused. Upstream Architect utility executables and unrelated PNT modules are omitted because they are outside the actual MediumPNT import closure.",
    "architect_upstream_toolchain": (BASE / "architect/lean-toolchain").read_text(encoding="utf-8").strip(),
    "architect_replay_toolchain": "leanprover/lean4:v4.33.1",
    "architect_toolchain_note": "The fixed Architect commit is tagged for Lean 4.33.0; its original source is replayed unchanged under the requested exact PNT/Mathlib Lean 4.33.1 toolchain. Actual compatibility is established by the build, not assumed.",
    "sources": sources,
}
(BASE / "kernel-source-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"project": str(PROJECT), "original_source_files": len(sources),
                  "source_bytes": sum(row["bytes"] for row in sources),
                  "source_changes": 0, "blueprint_preserved": True}))
