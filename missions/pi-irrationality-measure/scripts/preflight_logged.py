"""Check one repaired source file, preserving every attempt's diagnostics."""
import json
import argparse
import hashlib
import os
from pathlib import Path
import subprocess
import sys
import threading
import time

sys.stdout.reconfigure(encoding="utf-8")
TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
PORT = TASK / "port/lean/OAI/NumberTheory/PiExponent"
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("source")
mode = parser.add_mutually_exclusive_group()
mode.add_argument("--solution", action="store_true",
                  help="Check an explicitly scoped Solutions file instead of a port file")
mode.add_argument("--definition", action="store_true",
                  help="Check an explicitly scoped Definitions file")
mode.add_argument("--verification", action="store_true",
                  help="Check a mission-local verification script")
mode.add_argument("--sketch", action="store_true",
                  help="Extract Stage 2 facts from a path relative to port/lean")
mode.add_argument("--sketch-definition", action="store_true",
                  help="Extract Stage 2 facts from an explicitly scoped Definitions file")
parser.add_argument("--timeout-seconds", type=float, default=300)
parser.add_argument("--emit-olean", action="store_true",
                    help="Emit a scoped definition's importable local artifact")
args = parser.parse_args()
if not 0 < args.timeout_seconds <= 300:
    parser.error("The proof-file budget must be positive and at most 300 seconds")
if args.emit_olean and not args.definition:
    parser.error("Artifact emission is restricted to explicitly owned definition modules")
extracting = args.sketch or args.sketch_definition
source_base = (ROOT / "Solutions" if args.solution else ROOT / "Definitions" if args.definition or args.sketch_definition else TASK / "verification"
               if args.verification else TASK / "port/lean" if args.sketch else PORT)
source = (source_base / args.source).resolve()
if not source.is_relative_to(source_base.resolve()) or not source.is_file():
    raise SystemExit("Expected a file within the selected mission source directory")
if args.solution or args.definition or args.sketch_definition:
    scope = json.loads((TASK / "scope.json").read_text(encoding="utf-8"))
    if source.relative_to(ROOT).as_posix() not in scope["sources"]:
        raise SystemExit("The platform source file must be explicitly owned by this mission")
stamp = time.strftime("%Y%m%d-%H%M%S", time.gmtime())
hold_path = TASK / "verification/stage2-hold.json"
if args.sketch and hold_path.exists():
    # A new child sees this only after the previous file completed. It never
    # stops a running compiler or certifies a deferred file as compiled.
    hold = json.loads(hold_path.read_text(encoding="utf-8"))
    deferred = {"source": source.relative_to(ROOT).as_posix(), "exit_code": 75,
                "mode": "sketch", "phase": "controlled_queue_hold",
                "compilation_result_available": False, "source_unchanged": True,
                "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
                "hold_reason": hold["reason"], "hold_sha256": hashlib.sha256(hold_path.read_bytes()).hexdigest()}
    (TASK / "verification/latest-sketch.json").write_text(json.dumps(deferred, indent=2), encoding="utf-8")
    print(json.dumps(deferred), flush=True)
    sys.exit(75)
log_prefix = "sketch" if extracting else "preflight"
log_path = TASK / "verification" / f"{log_prefix}-{source.stem}-{stamp}.log"
env = os.environ.copy()
env["LEAN_NUM_THREADS"] = "1"
started = time.monotonic()
source_sha256 = hashlib.sha256(source.read_bytes()).hexdigest()
timed_out = threading.Event()
print("Preflight log:", log_path.relative_to(ROOT), flush=True)
command = ["lake", "env", "lean", "-DautoImplicit=false"]
runtime_path = TASK / "verification/lean-runtime.json"
runtime_sha256 = None
if runtime_path.exists():
    runtime = json.loads(runtime_path.read_text(encoding="utf-8"))
    for name, expected in runtime["project_hashes"].items():
        if hashlib.sha256((ROOT / name).read_bytes()).hexdigest() != expected:
            raise SystemExit("Pinned workspace configuration changed; recapture lake env before preflight")
    executable = Path(runtime["executable"])
    if hashlib.sha256(executable.read_bytes()).hexdigest() != runtime["executable_sha256"]:
        raise SystemExit("Pinned Lean executable changed; recapture lake env before preflight")
    if not set(runtime["environment"]) <= {"LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT"}:
        raise SystemExit("Runtime snapshot contains an unsupported environment variable")
    env.update(runtime["environment"])
    command = [str(executable), "-DautoImplicit=false"]
    runtime_sha256 = hashlib.sha256(runtime_path.read_bytes()).hexdigest()
if extracting:
    command += ["--run", str((TASK / "verification/RunSketchOracle.lean").relative_to(ROOT))]
output_path = None
if args.emit_olean:
    output_path = (ROOT / ".lake/build/lib/lean" / source.relative_to(ROOT).with_suffix(".olean")).resolve()
    if not output_path.is_relative_to(ROOT.resolve()):
        raise SystemExit("The emitted artifact would escape the workspace")
    output_path.parent.mkdir(parents=True, exist_ok=True)
    command += ["-o", str(output_path.relative_to(ROOT))]
command.append(str(source.relative_to(ROOT)))
with log_path.open("w", encoding="utf-8") as log:
    process = subprocess.Popen(
        command,
        cwd=ROOT, env=env,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
        encoding="utf-8", errors="replace")
    def stop_at_deadline():
        if process.poll() is not None:
            return
        timed_out.set()
        if os.name == "nt":
            # Only this Popen's process tree; Lake may own a child Lean process.
            subprocess.run(["taskkill", "/PID", str(process.pid), "/T", "/F"],
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        else:
            process.kill()
    timer = threading.Timer(max(0, args.timeout_seconds - (time.monotonic() - started)),
                            stop_at_deadline)
    timer.daemon = True
    timer.start()
    assert process.stdout is not None
    for line in process.stdout:
        log.write(line)
        log.flush()
        if not extracting:
            print(line.rstrip(), flush=True)
    original_exit_code = process.wait()
    timer.cancel()
exit_code = 124 if timed_out.is_set() else original_exit_code
record = {"source": source.relative_to(ROOT).as_posix(), "exit_code": exit_code,
          "mode": "sketch-definition" if args.sketch_definition else "sketch" if args.sketch else "verification" if args.verification
          else "solution" if args.solution else "definition" if args.definition else "port",
          "original_exit_code": original_exit_code, "timed_out": timed_out.is_set(),
          "timeout_seconds": args.timeout_seconds,
          "source_sha256": source_sha256,
          "source_unchanged": hashlib.sha256(source.read_bytes()).hexdigest() == source_sha256,
          "seconds": time.monotonic() - started, "log": log_path.relative_to(ROOT).as_posix()}
record["runtime_sha256"] = runtime_sha256
record["runtime_kind"] = "captured-lake-env" if runtime_sha256 else "lake-env"
if output_path is not None:
    record["output_olean"] = output_path.relative_to(ROOT).as_posix()
    record["output_sha256"] = (hashlib.sha256(output_path.read_bytes()).hexdigest()
                               if exit_code == 0 and output_path.exists() else None)
if extracting:
    record["oracle_sha256"] = hashlib.sha256(
        (TASK / "verification/TargetAxioms/SketchOracle.lean").read_bytes()).hexdigest()
    record["runner_sha256"] = hashlib.sha256(
        (TASK / "verification/RunSketchOracle.lean").read_bytes()).hexdigest()
(TASK / "verification" / ("latest-sketch.json" if extracting else "latest-preflight.json")).write_text(
    json.dumps(record, indent=2), encoding="utf-8")
print(json.dumps(record), flush=True)
sys.exit(exit_code)
