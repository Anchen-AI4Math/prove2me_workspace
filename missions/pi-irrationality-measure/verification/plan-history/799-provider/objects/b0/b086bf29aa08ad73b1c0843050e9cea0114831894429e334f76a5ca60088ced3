"""Compile or modecheck one exact staged Lean module with pinned inputs.

Source paths are relative to this mission's verification/ directory. The Lean
module root is also relative to verification/ and is passed to the pinned Lean
CLI as `-R`. OLean output, logs, and certificates stay inside this mission.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import threading
import time


TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
VERIFICATION = TASK / "verification"
RUNTIME_PATH = VERIFICATION / "lean-runtime.json"
STAGED_LIB = VERIFICATION / "staged-build" / "lib" / "lean"
LOG_ROOT = VERIFICATION / "staged-preflight-logs"
TASK_BUILD_LIB = ROOT / ".lake" / "build" / "lib" / "lean"
MAX_TIMEOUT = 300.0
MODULE_COMPONENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")


def sha_bytes(data):
    return hashlib.sha256(data).hexdigest()


def sha_file(path):
    return sha_bytes(path.read_bytes())


def task_relative(path):
    return path.relative_to(TASK).as_posix()


def verification_path(value, label):
    path = Path(value)
    if not path.is_absolute():
        path = VERIFICATION / path
    path = path.resolve()
    if not path.is_relative_to(VERIFICATION.resolve()):
        raise ValueError(f"{label} escapes verification/")
    return path


def workspace_file(relative, label):
    path = (ROOT / relative).resolve()
    if not path.is_relative_to(ROOT.resolve()) or not path.is_file():
        raise ValueError(f"{label} is missing or escapes workspace: {relative}")
    return path


def task_file(relative, label):
    path = (TASK / relative).resolve()
    if not path.is_relative_to(TASK.resolve()) or not path.is_file():
        raise ValueError(f"{label} is missing or escapes the mission: {relative}")
    return path


def read_json(path, label):
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ValueError(f"Cannot read {label} {path}: {exc}") from exc


def validate_runtime():
    raw = RUNTIME_PATH.read_bytes()
    runtime = json.loads(raw)
    runtime_sha = sha_bytes(raw)
    pins = runtime.get("project_hashes")
    if not isinstance(pins, dict) or not pins:
        raise ValueError("lean-runtime.json has no project_hashes pins")
    pin_records = {}
    for relative, expected in sorted(pins.items()):
        path = workspace_file(relative, "runtime pin")
        actual = sha_file(path)
        pin_records[relative] = {"expected_sha256": expected, "actual_sha256": actual,
                                 "matches": actual == expected}
        if actual != expected:
            raise ValueError(f"Pinned project file changed: {relative}")
    executable = Path(runtime.get("executable", "")).resolve()
    if not executable.is_file():
        raise ValueError("Pinned Lean executable is missing")
    executable_sha = sha_file(executable)
    if executable_sha != runtime.get("executable_sha256"):
        raise ValueError("Pinned Lean executable hash does not match runtime snapshot")
    environment = runtime.get("environment")
    allowed = {"LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT"}
    if (not isinstance(environment, dict) or set(environment) - allowed
            or not all(isinstance(v, str) for v in environment.values())
            or not environment.get("LEAN_PATH") or not environment.get("LEAN_SYSROOT")):
        raise ValueError("Runtime environment is missing or contains unsupported keys")
    return runtime, runtime_sha, executable, executable_sha, pin_records


def source_path(value):
    path = Path(value)
    if not path.is_absolute():
        path = VERIFICATION / path
    path = path.resolve()
    if not path.is_relative_to(VERIFICATION.resolve()) or not path.is_file() or path.suffix != ".lean":
        raise ValueError("source must be a .lean file inside verification/")
    return path


def module_identity(source, module_root):
    relative = source.relative_to(module_root).with_suffix("")
    parts = relative.parts
    if not parts or any(not MODULE_COMPONENT.fullmatch(part) for part in parts):
        raise ValueError("source path does not map to a valid Lean module name")
    return ".".join(parts)


def load_manifest(source, explicit):
    if explicit:
        path = verification_path(explicit, "imports manifest")
        if not path.is_file():
            raise ValueError(f"Imports manifest does not exist: {path}")
        return path, read_json(path, "imports manifest")
    candidates = [source.with_suffix(".manifest.json"), source.parent / "manifest.json"]
    for path in candidates:
        if path.is_file() and path.resolve().is_relative_to(VERIFICATION.resolve()):
            return path.resolve(), read_json(path, "stage manifest")
    return None, None


def verify_manifest_inputs(manifest):
    checked = {}
    inputs = manifest.get("input_hashes", {})
    if not isinstance(inputs, dict):
        raise ValueError("Manifest input_hashes must be an object")
    for relative, expected in sorted(inputs.items()):
        # Generator manifests use task-relative input paths (e.g.
        # `verification/extraction-state.json`), unlike source/output fields.
        path = task_file(relative, "manifest input")
        actual = sha_file(path)
        checked[relative] = {"expected_sha256": expected, "actual_sha256": actual,
                             "matches": actual == expected}
        if actual != expected:
            raise ValueError(f"Staged manifest input changed: {relative}")
    return checked


def verify_source_certificate(source, manifest):
    cert = {"source": {"path": task_relative(source), "sha256": sha_file(source),
                        "expected_sha256": None, "matches": None},
            "lineage": []}
    if manifest is None:
        cert["source"]["matches"] = True
        return cert
    expected_source = None
    if manifest.get("output"):
        output = workspace_file(manifest["output"], "generated-output manifest path")
        if output != source:
            raise ValueError("Source path disagrees with manifest output")
        expected_source = manifest.get("output_sha256")
        lineage_fields = (("source", "source_sha256", "port_source"),
                          ("original_source", "original_source_sha256", "original_source"))
    elif manifest.get("statement") or manifest.get("solution"):
        for name, hash_name in (("statement", "statement_sha256"),
                                ("solution", "solution_sha256")):
            if manifest.get(name):
                path = workspace_file(manifest[name], f"manifest {name}")
                expected = manifest.get(hash_name)
                actual = sha_file(path)
                if actual != expected:
                    raise ValueError(f"Manifest-certified {name} file changed")
                if path == source:
                    expected_source = expected
                cert["lineage"].append({"kind": name, "path": task_relative(path),
                                        "expected_sha256": expected, "actual_sha256": actual,
                                        "matches": True})
        lineage_fields = ()
        for name, expected in sorted(manifest.get("snapshot_sha256", {}).items()):
            path = (source.parent / name).resolve()
            if not path.is_relative_to(source.parent.resolve()) or not path.is_file():
                raise ValueError(f"Manifest snapshot escapes stage or is missing: {name}")
            actual = sha_file(path)
            if actual != expected:
                raise ValueError(f"Manifest snapshot changed: {name}")
            if path == source:
                expected_source = expected
            cert["lineage"].append({"kind": "snapshot", "path": task_relative(path),
                                    "expected_sha256": expected, "actual_sha256": actual,
                                    "matches": True})
    else:
        lineage_fields = ()

    for path_key, hash_key, kind in lineage_fields:
        if manifest.get(path_key) and manifest.get(hash_key):
            path = workspace_file(manifest[path_key], f"manifest {kind}")
            expected = manifest[hash_key]
            actual = sha_file(path)
            if actual != expected:
                raise ValueError(f"Manifest-certified {kind} source changed")
            cert["lineage"].append({"kind": kind, "path": task_relative(path),
                                    "expected_sha256": expected, "actual_sha256": actual,
                                    "matches": True})
    actual_source = cert["source"]["sha256"]
    if expected_source is not None:
        if actual_source != expected_source:
            raise ValueError("Staged source bytes differ from manifest certificate")
        cert["source"].update(expected_sha256=expected_source, matches=True)
    else:
        cert["source"]["matches"] = True
    return cert


def certified_imports(source, manifest):
    """Construct imports only from a manifest certificate and compare exact bytes."""
    if not isinstance(manifest, dict):
        raise ValueError("A hash-certified imports manifest is required")
    imports = manifest.get("imports")
    if not isinstance(imports, list) or not all(isinstance(item, str) for item in imports):
        raise ValueError("Manifest must contain an ordered imports array")

    expected = imports
    snapshots = manifest.get("snapshot_sha256", {})
    if source.name in snapshots:
        if source.name == "SnapshotOriginal.lean":
            components = manifest.get("source_components")
            if not isinstance(components, list) or not components:
                raise ValueError("SnapshotOriginal requires certified source_components")
            source_module = components[0].get("source_module")
            if not isinstance(source_module, str):
                raise ValueError("SnapshotOriginal source module is not certified")
            expected = ["Lean", source_module]
        elif source.name == "SnapshotGenerated.lean":
            expected = ["Lean", *imports]
        else:
            raise ValueError(f"No certified import rule for snapshot {source.name}")
    elif manifest.get("output"):
        # Definition bundle: manifest imports are the authoritative exact header.
        pass
    elif source.name not in {Path(manifest.get("statement", "")).name,
                             Path(manifest.get("solution", "")).name}:
        raise ValueError("Source is not a certified bundle, node file, or supported snapshot")

    if not expected or any(not MODULE_COMPONENT.fullmatch(part)
                           for name in expected for part in name.split(".")):
        raise ValueError("Certified imports contain an unsupported Lean module name")
    data = source.read_bytes()
    offset = 0
    for name in expected:
        command = f"import {name}".encode("utf-8")
        if not data.startswith(command, offset):
            raise ValueError("Source bytes do not start with the exact manifest-certified imports")
        offset += len(command)
        if data.startswith(b"\r\n", offset):
            offset += 2
        elif data.startswith(b"\n", offset):
            offset += 1
        else:
            raise ValueError("A certified import line has no exact LF/CRLF terminator")
    return expected


def effective_search_path(captured):
    entries = [STAGED_LIB, TASK_BUILD_LIB]
    entries.extend(Path(item) for item in captured.split(os.pathsep) if item)
    result, seen = [], set()
    for entry in entries:
        path = Path(os.path.abspath(entry))
        key = os.path.normcase(str(path))
        if key not in seen:
            seen.add(key)
            result.append(path)
    return result


def dependency_certificates(imports, search_path, blocked_modules):
    rows = []
    for name in imports:
        if name in blocked_modules:
            raise ValueError(f"Staged file cannot import its own target module: {name}")
        parts = name.split(".")
        if any(not MODULE_COMPONENT.fullmatch(part) for part in parts):
            raise ValueError(f"Unsupported imported module name: {name}")
        relative = Path(*parts).with_suffix(".olean")
        resolved = next(((root / relative, root) for root in search_path
                         if (root / relative).is_file()), None)
        if resolved is None:
            raise ValueError(f"Cannot resolve imported dependency OLean: {name}")
        path, search_root = resolved
        path = path.resolve()
        rows.append({"module": name, "path": str(path), "resolved_search_root": str(search_root),
                     "sha256_before": sha_file(path), "sha256_after": None,
                     "stable_during_compile": None})
    return rows


def kill_tree(process, timeout_event):
    if process.poll() is not None:
        return
    timeout_event.set()
    if os.name == "nt":
        subprocess.run(["taskkill", "/PID", str(process.pid), "/T", "/F"],
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False)
    else:
        process.kill()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", help=".lean path relative to TASK/verification")
    parser.add_argument("--root", required=True,
                        help="Lean module root relative to verification/ (passed to Lean -R)")
    parser.add_argument("--imports-manifest", help="Optional manifest path relative to verification/")
    parser.add_argument("--emit-olean", action="store_true",
                        help="Emit a mission-local OLean for later staged imports")
    parser.add_argument("--timeout-seconds", type=float, default=MAX_TIMEOUT)
    args = parser.parse_args()
    if not 0 < args.timeout_seconds <= MAX_TIMEOUT:
        parser.error("The process budget must be positive and at most 300 seconds")

    module_root = verification_path(args.root, "Lean module root")
    if not module_root.is_dir():
        raise ValueError("--root must be an existing directory inside verification/")
    source = source_path(args.source)
    if not source.is_relative_to(module_root):
        raise ValueError("source must be contained in --root")
    module = module_identity(source, module_root)
    manifest_path, manifest = load_manifest(source, args.imports_manifest)
    manifest_sha_before = sha_file(manifest_path) if manifest_path else None
    runtime, runtime_sha, executable, executable_sha, runtime_pins = validate_runtime()
    if manifest and manifest.get("runtime_sha256") and manifest["runtime_sha256"] != runtime_sha:
        raise ValueError("Manifest runtime hash does not match lean-runtime.json")
    manifest_inputs = verify_manifest_inputs(manifest or {})
    source_certificate = verify_source_certificate(source, manifest)
    source_before = sha_file(source)
    imports = certified_imports(source, manifest)
    search_path = effective_search_path(runtime["environment"]["LEAN_PATH"])
    blocked_modules = {module}
    if manifest.get("solution") and source == workspace_file(manifest["solution"], "solution target"):
        theorem_source = workspace_file(manifest.get("statement", ""), "theorem target")
        if not theorem_source.is_relative_to(module_root):
            raise ValueError("Theorem target source is outside the supplied module root")
        blocked_modules.add(module_identity(theorem_source, module_root))
    dependencies = dependency_certificates(imports, search_path, blocked_modules)

    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S_%fZ")
    module_path = Path(*module.split("."))
    output = STAGED_LIB / module_path.with_suffix(".olean")
    if not output.resolve().is_relative_to(TASK.resolve()):
        raise ValueError("OLean output escapes task directory")
    log_path = LOG_ROOT / (module.replace(".", "_") + "_" + stamp + ".log")
    sidecar = source.with_suffix(source.suffix + ".preflight.json")
    latest = VERIFICATION / "latest-staged-preflight.json"
    for artifact in (output, log_path, sidecar, latest):
        resolved = artifact.resolve()
        if not resolved.is_relative_to(TASK.resolve()):
            raise ValueError(f"Preflight artifact escapes mission directory: {artifact}")
    if not sidecar.resolve().is_relative_to(VERIFICATION.resolve()):
        raise ValueError("Source sidecar escapes verification/")
    if not latest.resolve().is_relative_to(VERIFICATION.resolve()):
        raise ValueError("Latest certificate escapes verification/")

    command = [str(executable), "-DautoImplicit=false", "-R", str(module_root)]
    if args.emit_olean:
        command.extend(["-o", str(output)])
    command.append(str(source))
    environment = os.environ.copy()
    environment.update(runtime["environment"])
    environment["LEAN_PATH"] = os.pathsep.join(str(path) for path in search_path)
    environment["LEAN_NUM_THREADS"] = "1"

    if args.emit_olean:
        output.parent.mkdir(parents=True, exist_ok=True)
        if not output.resolve().is_relative_to(TASK.resolve()):
            raise ValueError("OLean output escaped task directory after directory creation")
        if output.exists():
            output.unlink()
    log_path.parent.mkdir(parents=True, exist_ok=True)
    if not log_path.resolve().is_relative_to(TASK.resolve()):
        raise ValueError("Log path escaped task directory after directory creation")
    started = time.monotonic()
    timeout_event = threading.Event()
    with log_path.open("wb") as log:
        process = subprocess.Popen(command, cwd=ROOT, env=environment,
                                   stdout=log, stderr=subprocess.STDOUT)
        timer = threading.Timer(args.timeout_seconds, kill_tree, args=(process, timeout_event))
        timer.daemon = True
        timer.start()
        try:
            exit_code = process.wait(timeout=args.timeout_seconds)
        except subprocess.TimeoutExpired:
            timeout_event.set()
            kill_tree(process, timeout_event)
            exit_code = process.wait()
        finally:
            timer.cancel()
    elapsed = time.monotonic() - started
    timed_out = timeout_event.is_set()
    log_sha = sha_file(log_path)
    source_after = sha_file(source)
    source_unchanged = source_before == source_after
    for dependency in dependencies:
        path = Path(dependency["path"])
        dependency["sha256_after"] = sha_file(path) if path.is_file() else None
        dependency["stable_during_compile"] = dependency["sha256_before"] == dependency["sha256_after"]
    deps_stable = all(row["stable_during_compile"] for row in dependencies)
    inputs_after = verify_manifest_inputs(manifest or {})
    input_stable = all(inputs_after[key]["actual_sha256"] == row["actual_sha256"]
                        and inputs_after[key]["matches"]
                        for key, row in manifest_inputs.items())
    manifest_after_sha = sha_file(manifest_path) if manifest_path else None
    # Re-read every pinned project file and the executable after the run so the
    # certificate detects concurrent runtime/configuration replacement too.
    runtime_after, runtime_after_sha, executable_after, executable_after_sha, pins_after = validate_runtime()
    runtime_stable = (runtime_sha == runtime_after_sha
                      and executable == executable_after
                      and executable_sha == executable_after_sha
                      and runtime_pins == pins_after)
    manifest_stable = (manifest_path is None or manifest_after_sha == manifest_sha_before)
    try:
        source_certificate_after = verify_source_certificate(source, manifest)
        source_certificate_stable = source_certificate_after == source_certificate
    except (OSError, ValueError):
        source_certificate_after = None
        source_certificate_stable = False
    output_sha = sha_file(output) if args.emit_olean and output.is_file() else None
    success = (exit_code == 0 and not timed_out and elapsed <= args.timeout_seconds
               and source_unchanged and deps_stable and input_stable and runtime_stable
               and manifest_stable and source_certificate_stable
               and (not args.emit_olean or output_sha is not None))

    record = {
        "schema_version": 1,
        "mode": "emit-olean" if args.emit_olean else "modecheck",
        "at_utc": datetime.now(timezone.utc).isoformat(),
        "source": task_relative(source),
        "source_sha256_before": source_before,
        "source_sha256_after": source_after,
        "source_unchanged": source_unchanged,
        "module_root": task_relative(module_root),
        "actual_module_identity": module,
        "module_identity_basis": "Lean.Util.Path.moduleNameOfFileName(source, rootDir)",
        "manifest": task_relative(manifest_path) if manifest_path else None,
        "manifest_sha256_before": manifest_sha_before,
        "manifest_sha256_after": manifest_after_sha,
        "manifest_unchanged": manifest_stable,
        "manifest_input_hashes_before": manifest_inputs,
        "manifest_input_hashes_after": inputs_after,
        "source_certificate": source_certificate,
        "source_certificate_after": source_certificate_after,
        "source_certificate_stable": source_certificate_stable,
        "runtime_path": task_relative(RUNTIME_PATH),
        "runtime_sha256": runtime_sha,
        "runtime_sha256_after": runtime_after_sha,
        "runtime_unchanged": runtime_stable,
        "runtime_project_pins": runtime_pins,
        "runtime_project_pins_after": pins_after,
        "lean_executable": str(executable),
        "lean_executable_sha256": executable_sha,
        "lean_executable_sha256_after": executable_after_sha,
        "captured_environment": runtime["environment"],
        "effective_lean_path": [str(path) for path in search_path],
        "imports": imports,
        "dependency_oleans": dependencies,
        "dependencies_stable_during_compile": deps_stable,
        "command": command,
        "timeout_seconds": args.timeout_seconds,
        "seconds": elapsed,
        "timed_out": timed_out,
        "exit_code": exit_code,
        "output_olean": task_relative(output) if args.emit_olean else None,
        "output_olean_sha256": output_sha,
        "stdout_and_stderr_sha256": log_sha,
        "log": task_relative(log_path),
        "log_sha256": log_sha,
        "input_certificates_stable": (input_stable and runtime_stable and deps_stable
                                       and manifest_stable and source_certificate_stable),
        "success": success,
    }
    sidecar.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    latest.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"module": module, "mode": record["mode"], "exit_code": exit_code,
                      "timed_out": timed_out, "seconds": elapsed, "success": success,
                      "sidecar": task_relative(sidecar), "olean": record["output_olean"],
                      "olean_sha256": output_sha}), flush=True)
    return 0 if success else (124 if timed_out else (exit_code or 1))


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"staged-module preflight refused: {exc}", file=sys.stderr)
        sys.exit(2)
