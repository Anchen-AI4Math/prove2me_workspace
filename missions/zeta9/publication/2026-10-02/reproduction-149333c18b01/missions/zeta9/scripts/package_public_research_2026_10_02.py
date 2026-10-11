"""Offline, allowlisted public package and extracted five-group rerun.

Never reads credentials, calls the network, modifies original proofs/certs,
or runs Lean.  Run again after the public overview has been frozen.
"""
from __future__ import annotations

import argparse
import ast
import hashlib
import json
import os
import re
import subprocess
import sys
import time
import uuid
import zipfile
from pathlib import Path

MISSION = Path(__file__).resolve().parents[1]
ROOT = MISSION.parents[1]
OUT = MISSION / "publication/2026-10-02"
PUBLIC_URL = "https://prove2.me/missions/Irrationality_of_%CE%B6(9)%3A_weighted_lattice_route"
GROUPS = [
    ("direction_arithmetic_next", "direction-arithmetic-next-2026-10-02"),
    ("growing_rank_one_route", "growing-rank-one-route-2026-10-02"),
    ("dispersed_pole_frontier", "dispersed-pole-frontier-2026-10-02"),
    ("new_linear_form_route", "new-linear-form-route-2026-10-02"),
    ("new_linear_form_repair", "new-linear-form-route-repair-2026-10-02"),
]
SCRIPT_DIRS = [MISSION / "scripts", MISSION / "roadmap"] + [
    MISSION / f"round{n}/scripts" for n in range(1, 8)]
BANNED_PARTS = {".git", ".lake", "__pycache__", "node_modules", "api-docs",
                "platform-before", "platform-after", "sources", "exact_packages"}
ALLOWED_SUFFIXES = {".md", ".json", ".py", ".lean", ".txt", ".log", ".gz", ".jsonl"}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def relative(path):
    return path.resolve().relative_to(ROOT).as_posix()


def allowed(path):
    path = path.resolve()
    rel = path.relative_to(ROOT)
    if set(rel.parts) & BANNED_PARTS:
        return False
    if path.suffix.lower() not in ALLOWED_SUFFIXES and path.name != "lean-toolchain":
        return False
    if re.search(r"(?:credential|secret|token|\.env|api[-_]snapshot)", path.name, re.I):
        return False
    return (path.is_relative_to(MISSION) or rel.parts[0] in ("Theorems", "Definitions", "Solutions")
            or path == ROOT / "lean-toolchain")


def selected_sources():
    scope = json.loads((MISSION / "scope.json").read_text(encoding="utf-8"))
    chosen, excluded = {}, []

    def add(path, reason):
        path = path.resolve()
        if not path.is_file():
            return
        if allowed(path):
            chosen.setdefault(path, []).append(reason)
        else:
            excluded.append({"path": relative(path), "reason": "public-package exclusion policy"})

    for pattern in scope["sources"]:
        for path in ROOT.glob(pattern):
            add(path, "scope.sources")
    for name in ("README.md", "PUBLIC_OVERVIEW.md", "status.md", "scope.json"):
        add(MISSION / name, "mission navigation and publication overview")
    add(Path(__file__), "offline packaging recipe")
    for path in (
        MISSION / "verification/local-connection-2026-09-28/symbolic.json",
        MISSION / "round7/verification/arithmetic-connection-symbolic.json",
    ):
        add(path, "original symbolic connection data dependency")
    # Import closure uses only the current mission's known script directories.
    # Both independent_audit names exist; the explicit round6 sys.path insertion
    # in the recent callers selects the round6 version, which must be preserved.
    queue, visited = list(chosen), set()
    external = set()
    while queue:
        path = queue.pop()
        if path in visited or path.suffix != ".py":
            continue
        visited.add(path)
        text = path.read_text(encoding="utf-8-sig")
        tree = ast.parse(text, filename=str(path))
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                modules = [a.name for a in node.names]
            elif isinstance(node, ast.ImportFrom) and node.module:
                modules = [node.module]
            else:
                continue
            for module in modules:
                name = module.split(".")[0]
                prefix = "\n".join(text.splitlines()[:node.lineno])
                if name == "independent_audit" and "round6/scripts" in prefix:
                    search = [MISSION / "round6/scripts"] + SCRIPT_DIRS
                else:
                    search = [path.parent] + SCRIPT_DIRS
                dependency = next((d / (name + ".py") for d in search
                                   if (d / (name + ".py")).is_file()), None)
                if dependency:
                    if dependency.resolve() not in chosen:
                        add(dependency, "Python import of " + relative(path))
                        queue.append(dependency.resolve())
                elif name not in sys.stdlib_module_names and name != "__future__":
                    external.add(name)
        # Keep original own-data references when they are literal mission paths.
        for node in ast.walk(tree):
            if isinstance(node, ast.Constant) and isinstance(node.value, str):
                literal = node.value.replace("\\", "/")
                if "\n" not in literal and len(literal) < 200 and "/" in literal:
                    candidate = MISSION / literal
                    if candidate.is_file() and candidate.is_relative_to(MISSION):
                        add(candidate, "literal own-data reference in " + relative(path))
                        if candidate.suffix == ".py":
                            queue.append(candidate.resolve())
    # Lean closure includes actual local imports only.  Mathlib is a pinned
    # external dependency, and unrelated workspace modules are never copied.
    queue = [p for p in chosen if p.suffix == ".lean"]
    visited = set()
    while queue:
        path = queue.pop()
        if path in visited:
            continue
        visited.add(path)
        for module in re.findall(r"(?m)^import\s+([\w.]+)", path.read_text(encoding="utf-8-sig")):
            if module.startswith(("Mathlib", "Lean", "Std", "Init", "Lake")):
                continue
            dependency = ROOT / (module.replace(".", "/") + ".lean")
            if not dependency.is_file() or not allowed(dependency):
                raise RuntimeError("Unpackaged local Lean import: " + module)
            if dependency.resolve() not in chosen:
                add(dependency, "Lean import of " + relative(path))
                queue.append(dependency.resolve())
    add(ROOT / "lean-toolchain", "unchanged original Lean toolchain version")
    return chosen, excluded, sorted(external)


def public_readme():
    commands = "\n".join("python missions/zeta9/scripts/verify_" + s + ".py" for s, _ in GROUPS)
    return f"""# Zeta(9) research source package — 2026-10-02

Public mission: [weighted lattice route]({PUBLIC_URL}).

ζ(9) irrationality is **not proved**. This package preserves our dated written
research, exact finite certificates and selected earlier Lean source modules.
The 2026-10-01/02 research is not newly formalized in Lean. Packaging and Python
reruns do not certify a Lean build. See `missions/zeta9/PUBLIC_OVERVIEW.md` and
`missions/zeta9/status.md` for proved results, finite evidence and open exits.

## Contents and provenance

The archive retains the original `missions/zeta9/` paths and exactly selected
`Theorems/`, `Definitions/`, `Solutions/` imports if needed. Original source and
certificate bytes are unchanged; `source-manifest.json` records their SHA-256,
size and selection reasons. The generated `lakefile.lean` includes only the
selected theorem roots and the original pinned Mathlib commit. It does not
copy the workspace's unrelated task targets. Third-party papers, downloaded
source repositories, credentials, API/platform snapshots, compiled artifacts,
caches and external Python package binaries are excluded. Older paper-audit
scripts may require excluded third-party material obtained separately from
their documented sources; they are not part of the five-group rerun claim.

## Reproduce the five latest groups from an independent extraction

Use Python 3.12 in a virtual environment. From the extracted archive root:

```text
python -m venv .venv
# Activate .venv for your operating system.
python -m pip install -r requirements.txt
{commands}
```

Or run `python rerun_latest.py`, which starts the same five scripts in separate
processes, compares generated JSON bytes with the preserved original records,
and writes `rerun-report.json`. Scripts rewrite only the extracted verification
copies. Keep the original zip and manifest for immutable provenance. The old
`tmp/zeta7/exact_packages` search path may be absent: normal installed
`python-flint` satisfies the imports. No files from that old path are packaged.

All five original certificates record finite checks and bounded sample counts.
Their successful rerun is not a proof of the all-parameter mathematical claims
or of irrationality. Those claims and their open conditions are in the written
research and independent reviews. No all-task Lean build is required or run.

## Offline package verification

The packaging recipe is
`missions/zeta9/scripts/package_public_research_2026_10_02.py`.
Its `--verify` option extracts the final zip into a fresh local directory and
runs the five groups with separately installed external Python dependencies.
The sidecar `reproduction-report.json` identifies the exact tested zip hash,
runtime versions, source hashes and byte comparisons. It performs no network
calls, credentials access or Lean compilation.
"""


RUNNER = '''"""Rerun five finite groups without changing the preserved zip."""
import hashlib, json, subprocess, sys, time
from pathlib import Path
ROOT = Path(__file__).resolve().parent
GROUPS = __GROUPS__
rows = []
for name, directory in GROUPS:
    out = ROOT / "missions/zeta9/verification" / directory
    preserved = {p.name: p.read_bytes() for p in out.glob("*.json")}
    script = ROOT / "missions/zeta9/scripts" / ("verify_" + name + ".py")
    start = time.monotonic()
    run = subprocess.run([sys.executable, str(script)], cwd=ROOT, text=True,
                         encoding="utf-8", errors="replace", capture_output=True)
    comparisons = {name: hashlib.sha256((out / name).read_bytes()).hexdigest() ==
                         hashlib.sha256(data).hexdigest()
                   for name, data in preserved.items() if (out / name).exists()}
    result = {"script": str(script.relative_to(ROOT)).replace(chr(92), "/"),
              "returncode": run.returncode, "elapsed_seconds": round(time.monotonic()-start, 3),
              "preserved_record_sha256": {name:hashlib.sha256(data).hexdigest()
                                           for name,data in preserved.items()},
              "original_json_byte_comparisons": comparisons,
              "stdout": run.stdout, "stderr": run.stderr}
    rows.append(result)
    print(name + ": " + ("PASS" if run.returncode == 0 else "FAIL"), flush=True)
    if run.returncode:
        print(run.stderr, flush=True)
        break
report = {"status": "PASS" if len(rows)==5 and all(r["returncode"]==0 for r in rows) else "FAIL",
          "all_original_json_bytes_identical": all(all(r["original_json_byte_comparisons"].values())
                                                  for r in rows), "groups": rows}
(ROOT / "rerun-report.json").write_text(json.dumps(report, indent=2), encoding="utf-8")
if report["status"] != "PASS":
    raise SystemExit(1)
'''


def generated_files(chosen):
    lake = (ROOT / "lakefile.lean").read_text(encoding="utf-8-sig")
    mathlib = re.search(r'require mathlib from git\s+"([^"]+)"\s*@\s*"([^"]+)"', lake)
    if not mathlib:
        raise RuntimeError("Cannot identify original pinned Mathlib dependency")
    lean_roots = sorted(relative(p)[:-5].replace("/", ".") for p in chosen if p.suffix == ".lean")
    lean_config = ('import Lake\nopen Lake DSL\npackage «zeta9_research» where\n'
                   '  leanOptions := #[⟨`autoImplicit, false⟩]\n'
                   f'require mathlib from git\n  "{mathlib[1]}" @ "{mathlib[2]}"\n'
                   'lean_lib «Zeta9Research» where\n  roots := #[' +
                   ',\n             '.join('`' + m for m in lean_roots) + ']\n')
    return {"PACKAGE-README.md": public_readme().encode("utf-8"),
            "requirements.txt": ("# Python 3.12; versions used for the original certificates.\n"
                                 "python-flint==0.9.0\nsympy==1.13.1\nmpmath==1.4.1\n").encode(),
            "lakefile.lean": lean_config.encode(),
            "rerun_latest.py": RUNNER.replace("__GROUPS__", repr(GROUPS)).encode()}


def create_package():
    chosen, excluded, external = selected_sources()
    originals = {relative(p): p.read_bytes() for p in chosen}
    generated = generated_files(chosen)
    for name, data in originals.items():
        # Never print a possible secret; refuse packaging this exact file.
        if re.search(rb'(?:sk-[A-Za-z0-9]{24,}|Bearer\s+[A-Za-z0-9._-]{24,}|gh[pousr]_[A-Za-z0-9]{30,})', data):
            raise RuntimeError("Potential credential pattern in selected file: " + name)
    manifest = {"schema_version": 1, "package_date": "2026-10-02", "public_mission": PUBLIC_URL,
                "irrationality_proved": False, "new_lean_build_performed": False,
                "scope_sha256": sha((MISSION / "scope.json").read_bytes()),
                "external_import_names": external,
                "original_files": [{"path": name, "size_bytes": len(data), "sha256": sha(data),
                    "selection_reasons": sorted(set(chosen[(ROOT / name).resolve()]))}
                    for name, data in sorted(originals.items())],
                "generated_files": [{"path": name, "size_bytes": len(data), "sha256": sha(data)}
                                    for name, data in sorted(generated.items())],
                "manifest_self_hash_omitted": "Manifest cannot hash itself; zip hash is in the reproduction sidecar.",
                "excluded_scope_files": excluded,
                "excluded_categories": ["third-party PDFs and downloaded source trees", "credentials",
                    "API/platform snapshots", "cache and compiled output", "external Python binaries",
                    "unrelated workspace targets and full Mathlib tree"]}
    manifest_bytes = (json.dumps(manifest, indent=2, ensure_ascii=False) + "\n").encode("utf-8")
    generated["source-manifest.json"] = manifest_bytes
    OUT.mkdir(parents=True, exist_ok=True)
    archive = OUT / "zeta9-research-2026-10-02.zip"
    with zipfile.ZipFile(archive, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as bundle:
        for name, data in sorted((originals | generated).items()):
            info = zipfile.ZipInfo(name, date_time=(2026, 10, 2, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            bundle.writestr(info, data, compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
    (OUT / "source-manifest.json").write_bytes(manifest_bytes)
    (OUT / "PACKAGE-README.md").write_bytes(generated["PACKAGE-README.md"])
    return archive, manifest, originals


def verify_extraction(archive, manifest, originals, dependency_path=None):
    extraction = OUT / ("reproduction-" + uuid.uuid4().hex[:12])
    extraction.mkdir()
    with zipfile.ZipFile(archive) as bundle:
        for name in bundle.namelist():
            target = (extraction / name).resolve()
            if not target.is_relative_to(extraction.resolve()):
                raise RuntimeError("Unsafe archive path: " + name)
        bundle.extractall(extraction)
    assert all((extraction / name).read_bytes() == data for name, data in originals.items())
    assert not (extraction / "tmp/zeta7/exact_packages").exists()
    env = os.environ.copy()
    # External dependency path is a runtime-only installation, never archived.
    # It contains only third-party Python packages and no mission source code.
    env["PYTHONPATH"] = str(dependency_path) if dependency_path else ""
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    env["PYTHONUTF8"] = "1"
    version = subprocess.run([sys.executable, "-c", "import flint,sympy,mpmath,json; "
                              "print(json.dumps({'python_flint':flint.__version__,"
                              "'sympy':sympy.__version__,'mpmath':mpmath.__version__}))"],
                             cwd=extraction, env=env, text=True, encoding="utf-8", capture_output=True)
    if version.returncode:
        raise RuntimeError("Install requirements.txt before extraction verification: " + version.stderr)
    run = subprocess.run([sys.executable, str(extraction / "rerun_latest.py")], cwd=extraction,
                         env=env, text=True, encoding="utf-8", errors="replace", capture_output=True)
    print(run.stdout, end="", flush=True)
    if run.returncode:
        print(run.stderr, flush=True)
        raise RuntimeError("Extracted five-group rerun failed")
    report = json.loads((extraction / "rerun-report.json").read_text())
    # Reruns must preserve all original source files, including their byte hashes.
    unchanged = all((extraction / name).read_bytes() == data for name, data in originals.items()
                    if not name.startswith("missions/zeta9/verification/"))
    report.update(archive_name=archive.name, archive_sha256=sha(archive.read_bytes()),
                  archive_bytes=archive.stat().st_size, extraction_directory=str(extraction),
                  python_version=sys.version, external_versions=json.loads(version.stdout),
                  runtime_dependency_path_used=bool(dependency_path),
                  runtime_dependency_binaries_archived=False,
                  original_source_bytes_unchanged=unchanged,
                  original_source_file_count=len(manifest["original_files"]),
                  network_calls_performed=False, lean_build_performed=False)
    assert unchanged and report["all_original_json_bytes_identical"]
    (OUT / "reproduction-report.json").write_text(json.dumps(report, indent=2), encoding="utf-8")
    return {key: report[key] for key in ("status", "archive_sha256", "archive_bytes",
            "original_source_file_count", "all_original_json_bytes_identical", "original_source_bytes_unchanged")}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify", action="store_true")
    parser.add_argument("--dependency-path", type=Path,
                        help="existing third-party Python installation for offline reruns; never archived")
    args = parser.parse_args()
    archive, manifest, originals = create_package()
    print(json.dumps({"archive": str(archive), "original_file_count": len(originals),
                      "external_imports": manifest["external_import_names"]}), flush=True)
    if args.verify:
        print(json.dumps(verify_extraction(archive, manifest, originals, args.dependency_path), indent=2))


if __name__ == "__main__":
    main()
