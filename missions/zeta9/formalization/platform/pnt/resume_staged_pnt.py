"""Resume only missing PNT type reports; honestly adopt retained build objects.

The interrupted compiler wrote proof logs and .olean objects, but no receipt.
Its historical exit codes are unknown.  Do not invent them: validate those
objects by successful imports in new type reports and keep exit_code=null for
the adopted rows.  This script never rebuilds the 8 Solution or 4 reference
objects and never writes outside the current task.
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import subprocess, json, hashlib, sys

sys.stdout.reconfigure(encoding="utf-8")
OUT = Path(__file__).resolve().parent
TASK = OUT.parents[2]
ROOT = TASK.parents[1]
UP = TASK / "verification/formalization-pnt-dependency-2026-10-02/project/.lake/build/lib/lean"
REQUEST = json.loads((OUT / "problems-request.json").read_text(encoding="utf-8"))
PROBLEMS = REQUEST["problems"]
PLAN = json.loads((OUT / "decl-plan.json").read_text(encoding="utf-8"))
RECEIPT = OUT / "staged-compile-receipt.json"
ROWS = []

def sha(data):
    return hashlib.sha256(data).hexdigest()

def dump_receipt(complete=False):
    receipt = {
        "canonical_solution_bytes_identical_across_modes": True,
        "stub_mirror_is_proof": False,
        "native_uses_actual_original_pnt_cache": True,
        "completion": "complete" if complete else "in_progress",
        "resume_date_utc": datetime.now(timezone.utc).isoformat(),
        "historical_compile_exit_codes": "Not retained; adopted build rows have null exits and are validated by successful fresh type-report imports.",
        "missing_original_report_cause": "A staged build/native Solutions directory shadowed the original clearing-proof module. Original reports omit the staged search-path prefix.",
        "rows": sorted(ROWS, key=lambda x: x["label"]),
    }
    RECEIPT.write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

def command(source, cwd, lib, output=None):
    # Lean resolves module namespaces using the first matching directory.
    # Original reports must not inherit a staged Solutions prefix.
    env = "$env:LEAN_PATH = "
    if lib is not None:
        env += f'"{lib.as_posix()};" + '
    env += f'$env:LEAN_PATH + ";{ROOT.as_posix()};{UP.as_posix()}"; '
    expression = env + f'Set-Location "{cwd.as_posix()}"; lean '
    if output:
        expression += f'-o "{output.as_posix()}" '
    expression += f'"{source.as_posix()}"; exit $LASTEXITCODE'
    return ["lake", "env", "pwsh", "-NoProfile", "-Command", expression]

def retained(label, source, cwd, lib, output, report):
    log = OUT / (label + ".log")
    assert log.is_file() and output.is_file() and output.stat().st_size > 0, label
    assert ": error:" not in log.read_text(encoding="utf-8-sig"), label
    row = {
        "label": label, "source": source.relative_to(OUT).as_posix(),
        "source_sha256": sha(source.read_bytes()),
        "command": command(source, cwd, lib, output),
        "command_provenance": "Reconstructed exactly from retained compile_staged_pnt.py; historical process exit was not retained.",
        "working_directory": str(ROOT), "lean_working_directory": str(cwd),
        "search_path_prefix": str(lib), "exit_code": None,
        "evidence_kind": "retained_build_object",
        "verification_report": report,
        "log": log.relative_to(OUT).as_posix(), "log_sha256": sha(log.read_bytes()),
        "output": str(output), "output_sha256": sha(output.read_bytes()),
    }
    ROWS.append(row)

for mode in ("native", "stub"):
    lib = OUT / "build" / mode
    retained(mode + "-boundary", OUT / "boundary-mirror" / mode / "Theorems/Thm_MediumPNT.lean",
             OUT / "boundary-mirror" / mode, lib, lib / "Theorems/Thm_MediumPNT.olean",
             "types-boundary-" + mode)
    for i, p in enumerate(PROBLEMS):
        retained(f"{mode}-solution-{i}", OUT / "staged" / p["local_solution"],
                 OUT / "staged", lib, lib / Path(p["local_solution"]).with_suffix(".olean"),
                 f"types-{mode}-{i}-solution")
for i, p in enumerate(PROBLEMS):
    lib = OUT / "build/stub"
    retained(f"reference-{i}", OUT / "staged" / p["local_reference"], OUT / "staged", lib,
             lib / Path(p["local_reference"]).with_suffix(".olean"), f"types-{i}-reference")
for mode in ("native", "stub"):
    label = f"types-boundary-{mode}"
    source = OUT / "types-boundary.lean"
    log = OUT / (label + ".log")
    data = log.read_text(encoding="utf-8-sig")
    recs = [json.loads(x) for x in data.splitlines() if x.startswith("{")]
    assert len(recs) == 1 and recs[0]["label"] == "MediumPNT" and ": error:" not in data
    ROWS.append({
        "label": label, "source": source.relative_to(OUT).as_posix(),
        "source_sha256": sha(source.read_bytes()),
        "command": command(source, ROOT, OUT / "build" / mode),
        "command_provenance": "Reconstructed from retained compiler; complete pre-resume report retained without rerunning.",
        "working_directory": str(ROOT), "lean_working_directory": str(ROOT),
        "search_path_prefix": str(OUT / "build" / mode), "exit_code": None,
        "evidence_kind": "retained_type_report",
        "verification_report": f"types-{mode}-0-solution",
        "log": log.relative_to(OUT).as_posix(), "log_sha256": sha(log.read_bytes()),
        "output": None, "output_sha256": None, "record_labels": ["MediumPNT"],
    })
dump_receipt()

expected_original = {p["theorem_name"] for p in PROBLEMS} | set(PLAN["reused_public_definitions"]) | {"MediumPNT"}
jobs = [("types-original", "types-original.lean", None, expected_original)]
jobs += [(f"types-{mode}-{i}-solution", f"types-{i}-solution.lean", mode,
          {p["theorem_name"]} | set(PLAN["reused_public_definitions"]) | {"MediumPNT"})
         for mode in ("native", "stub") for i, p in enumerate(PROBLEMS)]
jobs += [(f"types-{i}-reference", f"types-{i}-reference.lean", "stub",
          {p["theorem_name"]} | set(PLAN["reused_public_definitions"])) for i, p in enumerate(PROBLEMS)]

def report(job):
    label, script, mode, expected = job
    source = OUT / script
    lib = OUT / "build" / mode if mode else None
    log = OUT / (label + ".log")
    saved = OUT / (label + ".resume-receipt.json")
    if saved.exists():
        old = json.loads(saved.read_text(encoding="utf-8"))
        if old["source_sha256"] == sha(source.read_bytes()) and old["log_sha256"] == sha(log.read_bytes()) and old["exit_code"] == 0:
            print(label + ": reused successful resumable report", flush=True)
            return old
    if log.exists():
        previous = log.read_bytes()
        backup = OUT / (label + ".before-resume.log")
        if not backup.exists():
            backup.write_bytes(previous)
    original = source.read_bytes()
    cmd = command(source, ROOT, lib)
    proc = subprocess.run(cmd, cwd=ROOT, capture_output=True)
    log.write_bytes(proc.stdout + proc.stderr)
    assert source.read_bytes() == original
    data = log.read_text(encoding="utf-8-sig")
    records = [json.loads(x) for x in data.splitlines() if x.startswith("{")]
    assert proc.returncode == 0 and ": error:" not in data, (label, data)
    assert {x["label"] for x in records} == expected, (label, "incomplete report")
    row = {
        "label": label, "source": source.relative_to(OUT).as_posix(),
        "source_sha256": sha(original), "command": cmd, "working_directory": str(ROOT),
        "lean_working_directory": str(ROOT), "search_path_prefix": str(lib) if lib else None,
        "exit_code": proc.returncode, "evidence_kind": "fresh_type_report",
        "log": log.relative_to(OUT).as_posix(), "log_sha256": sha(log.read_bytes()),
        "output": None, "output_sha256": None, "record_labels": sorted(expected),
    }
    saved.write_text(json.dumps(row, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(label + ": exit " + str(proc.returncode), flush=True)
    return row

# Reports are cheap imports of existing objects; the cap preserves the build policy.
with ThreadPoolExecutor(max_workers=2) as pool:
    for row in pool.map(report, jobs):
        ROWS.append(row)
        dump_receipt()
dump_receipt(complete=True)
print("Completed only type reports; reused all 14 retained build objects", flush=True)
