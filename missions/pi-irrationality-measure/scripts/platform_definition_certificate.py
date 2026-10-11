"""Verify existing closed Definition evidence and export a separate provider certificate.

This is an offline certificate bridge.  It never runs Lean or contacts the
platform, and it deliberately does not turn preview bundle plans into final
generation plans.  The original local OLean proof and (for Collision) the exact
published LF byte variant are recorded as distinct artifacts.
"""
import hashlib
import importlib.util
import json
import difflib
import os
from pathlib import Path
import re
import sys

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
VERIFICATION = TASK / "verification"
STAGES = (
    "Def_OAI_NumberTheory_PiExponent_Analysis_Collision",
    "Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticCollision",
)
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
MODULE_PART = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")
ARCHIVE_MANIFEST_PATH = VERIFICATION / "plan-history" / "799-publication" / "archive-manifest.json"
# The matching old state bytes were not archived. This digest is accepted only
# as a historical witness recorded in the successful preview preflights.
UNRECOVERED_799_STATE_SHA256 = "d9303cbf27f4718755c05c8471eb7bc89e9aef2a4db9263472b7c12ca1f8d720"
OLD_PRE_STAGE_ROOT_RUNTIME = "verification/lean-runtime-before-stage-roots-20261008.json"
OLD_PRE_STAGE_ROOT_SHA256 = "2dc0949be9042af8452d49159eec9fd871a21f6ddc3e14698d4590ec43fc5c6d"
OLD_PRE_SNAKY_RUNTIME = "verification/lean-runtime-before-lakefile-change-20261008.json"
OLD_PRE_SNAKY_SHA256 = "7c50fd8ec1144847da49fb1e802f8acef679ae60502140dd18cec707129b3765"
STAGE_ROOT_AUDIT = "verification/stage-root-runtime-transition.json"
STAGE_ROOT_REGISTRATION = "verification/stage-root-registration.json"
PRIOR_LAKEFILE_AUDIT = "verification/lakefile-change-audit.json"
OLD_MID_LAKEFILE = "verification/lakefile-before-stage-root-registration.lean"
OLD_BASE_LAKEFILE = "verification/lakefile-before-snaky21-addition.lean.txt"
ARCHIVE_CACHE = None


def sha_bytes(raw):
    return hashlib.sha256(raw).hexdigest()


def sha(path):
    return sha_bytes(path.read_bytes())


def read(path):
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path, value):
    raw = (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode("utf-8")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(raw)


def task_path(value, label):
    path = (TASK / value).resolve()
    if not path.is_relative_to(TASK.resolve()) or not path.is_file():
        raise ValueError(f"{label} is missing or escapes the mission: {value}")
    return path


def workspace_path(value, label):
    # Bundle manifests store source/output as workspace-relative missions/...;
    # preflight sidecars instead store source/log/output_olean task-relative.
    path = Path(value)
    path = path.resolve() if path.is_absolute() else (ROOT / path).resolve()
    if not path.is_relative_to(ROOT.resolve()) or not path.is_file():
        raise ValueError(f"{label} is missing or escapes the workspace: {value}")
    return path


def module_for(root, source):
    rel = source.resolve().relative_to(root.resolve()).with_suffix("")
    if not rel.parts or any(not MODULE_PART.fullmatch(part) for part in rel.parts):
        raise ValueError("A staged source path is not a valid Lean module path")
    return ".".join(rel.parts)


def staged_search_path(runtime):
    captured = runtime["environment"]["LEAN_PATH"]
    entries = [VERIFICATION / "staged-build" / "lib" / "lean", ROOT / ".lake" / "build" / "lib" / "lean"]
    entries.extend(Path(item) for item in captured.split(";") if item)
    result, seen = [], set()
    for entry in entries:
        path = Path(__import__("os").path.abspath(entry))
        key = __import__("os").path.normcase(str(path))
        if key not in seen:
            seen.add(key)
            result.append(str(path))
    return result


def normalized_runtime_paths(value):
    paths = []
    seen = set()
    for item in value.split(";"):
        if not item:
            continue
        path = os.path.normcase(os.path.abspath(item))
        if path not in seen:
            seen.add(path)
            paths.append(path)
    return paths


def runtime_transition_certificate():
    """Authenticate the two exact Lakefile-only transitions around old proof runs."""
    current_path = VERIFICATION / "lean-runtime.json"
    current_raw = current_path.read_bytes()
    current = json.loads(current_raw)
    current_sha = sha_bytes(current_raw)
    old_path = task_path(OLD_PRE_STAGE_ROOT_RUNTIME, "pre-stage-root runtime snapshot")
    old_raw = old_path.read_bytes()
    old = json.loads(old_raw)
    old_sha = sha_bytes(old_raw)
    if old_sha != OLD_PRE_STAGE_ROOT_SHA256:
        raise ValueError("Archived pre-stage-root runtime fingerprint changed")
    audit_path = task_path(STAGE_ROOT_AUDIT, "stage-root runtime transition audit")
    audit = read(audit_path)
    registration_path = task_path(STAGE_ROOT_REGISTRATION, "stage-root registration evidence")
    registration = read(registration_path)
    current_lakefile = ROOT / "lakefile.lean"
    mid_lakefile = task_path(OLD_MID_LAKEFILE, "pre-stage-root Lakefile bytes")
    if (current_sha != audit.get("new_runtime_sha256")
            or old_sha != audit.get("old_runtime_sha256")
            or audit.get("old_runtime") != OLD_PRE_STAGE_ROOT_RUNTIME
            or audit.get("new_runtime") != "verification/lean-runtime.json"
            or audit.get("new_runtime_sha256") != sha(current_path)
            or audit.get("registration_sha256") != sha(registration_path)
            or registration.get("source") != "lakefile.lean"
            or registration.get("source_sha256") != old.get("project_hashes", {}).get("lakefile.lean")
            or registration.get("result_sha256") != current.get("project_hashes", {}).get("lakefile.lean")
            or registration.get("result_sha256") != sha(current_lakefile)
            or registration.get("source_sha256") != sha(mid_lakefile)
            or registration.get("applied") is not True
            or not registration.get("prior_extraction_terminal")):
        raise ValueError("Stage-root runtime audit/registration does not bind current and archived bytes")
    addition = registration.get("addition")
    if not isinstance(addition, str) or mid_lakefile.read_bytes() + addition.encode("utf-8") != current_lakefile.read_bytes():
        raise ValueError("Current Lakefile is not the exact archived pre-stage-root bytes plus registered addition")
    if (audit.get("only_project_pin_change") != "lakefile.lean"
            or audit.get("lean_mathlib_versions_equal") is not True
            or audit.get("lean_executable_byte_identical") is not True
            or audit.get("ordered_search_paths_equal") is not True
            or audit.get("historical_certificates_keep_original_fingerprint") is not True):
        raise ValueError("Stage-root runtime audit does not attest the exact runtime compatibility conditions")
    pin_keys = set(current.get("project_hashes", {}))
    if (pin_keys != set(old.get("project_hashes", {}))
            or {k for k in pin_keys if current["project_hashes"][k] != old["project_hashes"][k]} != {"lakefile.lean"}):
        raise ValueError("Current runtime changed project pins beyond the registered Lakefile addition")
    if (old.get("executable") != current.get("executable")
            or old.get("executable_sha256") != current.get("executable_sha256")
            or not Path(current.get("executable", "")).is_file()
            or sha(Path(current["executable"])) != current.get("executable_sha256")):
        raise ValueError("Current and archived runtime do not share the exact Lean executable")
    for relative, expected in current.get("project_hashes", {}).items():
        path = workspace_path(relative, "current runtime pin")
        if sha(path) != expected:
            raise ValueError(f"Current project pin is stale: {relative}")
    for relative, expected in old.get("project_hashes", {}).items():
        if relative == "lakefile.lean":
            continue
        if old.get("project_hashes", {}).get(relative) != current.get("project_hashes", {}).get(relative):
            raise ValueError(f"Historical non-Lakefile pin differs from current: {relative}")
    path_comparisons = audit.get("runtime_path_comparisons", {})
    for key in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT"):
        old_value = old.get("environment", {}).get(key)
        new_value = current.get("environment", {}).get(key)
        entry = path_comparisons.get(key, {})
        raw_equal = old_value == new_value
        normalized_equal = normalized_runtime_paths(old_value or "") == normalized_runtime_paths(new_value or "")
        if (entry.get("raw_equal") is not raw_equal
                or entry.get("normalized_ordered_unique_paths_equal") is not normalized_equal
                or normalized_equal is not True):
            raise ValueError(f"Archived/current normalized search path differs: {key}")
    if (old.get("environment", {}).get("LEAN_PATH") != current.get("environment", {}).get("LEAN_PATH")
            or old.get("environment", {}).get("LEAN_SYSROOT") != current.get("environment", {}).get("LEAN_SYSROOT")):
        raise ValueError("Stage-root registration changed LEAN_PATH or LEAN_SYSROOT")

    # Validate the prior 7c50 -> 2dc lakefile-only transition as the provenance
    # chain for the archived runtime used by the compiler records.
    prior_path = task_path(OLD_PRE_SNAKY_RUNTIME, "pre-Snaky21 runtime snapshot")
    prior_raw = prior_path.read_bytes()
    prior = json.loads(prior_raw)
    prior_sha = sha_bytes(prior_raw)
    if prior_sha != OLD_PRE_SNAKY_SHA256:
        raise ValueError("Archived pre-Snaky21 runtime fingerprint changed")
    prior_audit_path = task_path(PRIOR_LAKEFILE_AUDIT, "prior Lakefile transition audit")
    prior_audit = read(prior_audit_path)
    base_lakefile = task_path(OLD_BASE_LAKEFILE, "pre-Snaky21 Lakefile bytes")
    if (prior_audit.get("old_lakefile_sha256") != prior.get("project_hashes", {}).get("lakefile.lean")
            or prior_audit.get("new_lakefile_sha256") != old.get("project_hashes", {}).get("lakefile.lean")
            or prior_audit.get("exact_prior_bytes_reconstructed") is not True
            or prior_audit.get("only_configuration_change") != "Added unrelated Snaky21Proofs library registration"
            or prior_audit.get("same_lean_executable") is not True
            or prior_audit.get("source_versions_changed") is not False
            or prior_audit.get("source_files_modified") is not False
            or prior_audit.get("shared_lakefile_modified_by_this_check") is not False
            or sha(base_lakefile) != prior.get("project_hashes", {}).get("lakefile.lean")
            or sha(mid_lakefile) != old.get("project_hashes", {}).get("lakefile.lean")):
        raise ValueError("Prior 7c50-to-2dc runtime/Lakefile audit does not match archived snapshots")
    old0_pins, old1_pins = prior.get("project_hashes", {}), old.get("project_hashes", {})
    if (set(old0_pins) != set(old1_pins)
            or {k for k in old0_pins if old0_pins[k] != old1_pins[k]} != {"lakefile.lean"}):
        raise ValueError("Prior runtime transition changed project pins beyond the Snaky21 Lakefile addition")
    if (prior.get("executable") != old.get("executable")
            or prior.get("executable_sha256") != old.get("executable_sha256")):
        raise ValueError("Prior runtime transition changed the Lean executable")
    prior_src = base_lakefile.read_bytes()
    old_src = mid_lakefile.read_bytes()
    insertions = [(i, j, k, l) for tag, i, j, k, l in difflib.SequenceMatcher(None, prior_src, old_src,
                                                                               autojunk=False).get_opcodes()
                  if tag != "equal"]
    expected_snaky = ("lean_lib «Snaky21Proofs» where\n"
                      "  roots := #[]\n"
                      "  globs := #[.submodules `Solutions.Snaky21]\n\n").encode("utf-8")
    if (len(insertions) != 1 or insertions[0][0] != insertions[0][1]
            or old_src[insertions[0][2]:insertions[0][3]] != expected_snaky):
        raise ValueError("Pre-Snaky21 to pre-stage-root Lakefile change is not the exact unrelated registration")
    prior_path_checks = prior_audit.get("normalized_ordered_search_paths_equal", {})
    if set(prior_path_checks) != {"LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT"} or not all(prior_path_checks.values()):
        raise ValueError("Prior Lakefile transition lacks normalized search-path equality")
    for key in prior_path_checks:
        if normalized_runtime_paths(prior.get("environment", {}).get(key, "")) != normalized_runtime_paths(old.get("environment", {}).get(key, "")):
            raise ValueError(f"Prior transition changed normalized {key}")
    if (prior.get("environment", {}).get("LEAN_PATH") != old.get("environment", {}).get("LEAN_PATH")
            or prior.get("environment", {}).get("LEAN_SYSROOT") != old.get("environment", {}).get("LEAN_SYSROOT")):
        raise ValueError("Prior transition changed LEAN_PATH or LEAN_SYSROOT")
    return {
        "current": {"path": current_path.relative_to(TASK).as_posix(), "sha256": current_sha,
                    "runtime": current},
        "historical_stage_root": {"path": old_path.relative_to(TASK).as_posix(), "sha256": old_sha,
                                   "runtime": old},
        "transition_audit": {"path": audit_path.relative_to(TASK).as_posix(), "sha256": sha(audit_path),
                             "registration": registration_path.relative_to(TASK).as_posix(),
                             "registration_sha256": sha(registration_path),
                             "lakefile_addition_exact": True,
                             "changed_pin_only_lakefile": True,
                             "same_lean_executable": True,
                             "normalized_search_paths_equal": True},
        "prior_transition": {"source_runtime": prior_path.relative_to(TASK).as_posix(),
                             "source_runtime_sha256": prior_sha,
                             "source_lakefile": base_lakefile.relative_to(TASK).as_posix(),
                             "target_lakefile": mid_lakefile.relative_to(TASK).as_posix(),
                             "audit": prior_audit_path.relative_to(TASK).as_posix(),
                             "audit_sha256": sha(prior_audit_path),
                             "only_exact_snaky21_registration_added": True,
                             "same_lean_executable": True,
                             "normalized_search_paths_equal": True},
        "record_runtime_by_sha256": {current_sha: current, old_sha: old},
        "historical_stage_root_sha256": old_sha,
        "historical_lakefile_path": mid_lakefile,
    }


def normalize(row, key):
    levels = {name: index for index, name in enumerate(row.get("levelParams", []))}

    def walk(value):
        if not isinstance(value, list):
            return value
        if len(value) == 2 and value[0] == "param":
            if value[1] not in levels:
                raise ValueError("Snapshot refers to an undeclared universe parameter")
            return ["param", levels[value[1]]]
        return [walk(item) for item in value]

    return walk(row[key])


def audit_axioms(log_path, names):
    """Reuse the campaign's strict axiom parser, including universe suffixes."""
    path = TASK / "scripts" / "validate_standalone_platform_node.py"
    spec = importlib.util.spec_from_file_location("campaign_standalone_axiom_auditor", path)
    if spec is None or spec.loader is None:
        raise ValueError("Cannot load the established strict axiom auditor")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    rows = {}
    for name in names:
        result = module.audit_axioms(log_path, name)
        if not isinstance(result, list) or not set(result) <= ALLOWED_AXIOMS:
            raise ValueError(f"Unknown, sorry, or nonstandard axiom in {name}: {result}")
        rows[name] = sorted(result)
    return rows


def archive_index():
    global ARCHIVE_CACHE
    if ARCHIVE_CACHE is not None:
        return ARCHIVE_CACHE
    path = task_path(ARCHIVE_MANIFEST_PATH.relative_to(TASK).as_posix(), "799-plan archive manifest")
    index = read(path)
    if index.get("indexed_modules") != 799 or index.get("validated") is not False:
        raise ValueError("799 plan archive is not an explicitly historical byte-preservation record")
    checked = {}
    for relative, row in index.get("input_files", {}).items():
        archived = task_path(row.get("archive", ""), "Archived 799-plan input")
        if sha(archived) != row.get("sha256") or archived.stat().st_size != row.get("bytes"):
            raise ValueError(f"Preserved 799-plan input failed its archive manifest: {relative}")
        checked[relative] = {"path": archived, "sha256": row["sha256"]}
    ARCHIVE_CACHE = (index, path, checked)
    return ARCHIVE_CACHE


def certified_input_path(relative, expected, archive=None):
    current = task_path(relative, "Definition manifest input")
    current_sha = sha(current)
    if current_sha == expected:
        return {"path": current, "current_sha256": current_sha, "compiled_sha256": expected,
                "provenance": "current"}
    if archive is None:
        _, _, archive = archive_index()
    archived = archive.get(relative)
    if archived and archived["sha256"] == expected:
        return {"path": archived["path"], "current_sha256": current_sha,
                "compiled_sha256": expected, "provenance": "preserved-799-archive"}
    if (relative == "verification/extraction-state.json"
            and expected == UNRECOVERED_799_STATE_SHA256):
        return {"path": None, "current_sha256": current_sha,
                "compiled_sha256": expected, "provenance": "unrecovered-historical-799-state"}
    raise ValueError(f"Historical input changed without a matching archived byte copy: {relative}")


def verify_manifest_inputs(manifest, archive=None):
    checked = {}
    for relative, expected in sorted(manifest.get("input_hashes", {}).items()):
        checked[relative] = certified_input_path(relative, expected, archive)
        checked[relative].pop("path", None)
    return checked


def verify_import_header(source, imports):
    if not isinstance(imports, list) or not imports:
        raise ValueError("Closed Definition has no ordered exact-import certificate")
    if any(not isinstance(name, str) or any(not MODULE_PART.fullmatch(p) for p in name.split("."))
           for name in imports):
        raise ValueError("Definition import list contains an invalid module name")
    if any(name.startswith(("OAI.", "Definitions.", "Theorems.", "Solutions.")) for name in imports):
        raise ValueError("Closed Definition imports another project/platform module")
    data = source.read_bytes()
    offset = 0
    for name in imports:
        command = b"import " + name.encode("ascii")
        if not data.startswith(command, offset):
            raise ValueError("Bundle bytes do not match the manifest's exact imports")
        offset += len(command)
        if data.startswith(b"\r\n", offset):
            offset += 2
        elif data.startswith(b"\n", offset):
            offset += 1
        else:
            raise ValueError("Certified import line has no LF/CRLF terminator")
    return data


def verify_runtime(record, runtime, runtime_sha, runtime_compatibility=None):
    if (record.get("runtime_sha256") != runtime_sha
            or record.get("runtime_sha256_after") != runtime_sha
            or record.get("runtime_unchanged") is not True
            or record.get("captured_environment") != runtime.get("environment")
            or record.get("lean_executable") != runtime.get("executable")
            or record.get("lean_executable_sha256") != runtime.get("executable_sha256")
            or record.get("lean_executable_sha256_after") != runtime.get("executable_sha256")
            or record.get("timeout_seconds") != 300.0
            or record.get("effective_lean_path") != staged_search_path(runtime)
            or not isinstance(record.get("seconds"), (int, float))
            or not 0 < record["seconds"] <= 300):
        raise ValueError("Preflight runtime, timeout, or elapsed-time certificate is invalid")
    for relative, expected in runtime.get("project_hashes", {}).items():
        row = record.get("runtime_project_pins", {}).get(relative)
        after = record.get("runtime_project_pins_after", {}).get(relative)
        if (runtime_compatibility is not None
                and runtime_sha == runtime_compatibility["historical_stage_root_sha256"]
                and relative == "lakefile.lean"):
            actual_path = runtime_compatibility["historical_lakefile_path"]
            actual = sha(actual_path)
        else:
            actual_path = workspace_path(relative, "pinned project file")
            actual = sha(actual_path)
        if (actual != expected or not isinstance(row, dict) or not isinstance(after, dict)
                or row.get("expected_sha256") != expected or row.get("actual_sha256") != expected
                or row.get("matches") is not True or after != row):
            raise ValueError(f"Preflight project pin is invalid: {relative}")
    exe = Path(runtime.get("executable", ""))
    if not exe.is_file() or sha(exe) != runtime.get("executable_sha256"):
        raise ValueError("Pinned Lean executable hash changed")


def verify_preflight(record, runtime, runtime_sha, expected_mode, expected_module,
                     expected_source=None, expected_output=None, expected_imports=None,
                     runtime_compatibility=None):
    if (record.get("mode") != expected_mode or record.get("success") is not True
            or record.get("exit_code") != 0 or record.get("timed_out") is not False
            or record.get("source_unchanged") is not True or not record.get("input_certificates_stable")
            or record.get("dependencies_stable_during_compile") is not True):
        raise ValueError("Preflight did not complete successfully with stable inputs")
    if record.get("actual_module_identity") != expected_module:
        raise ValueError("Preflight actual Lean module identity differs")
    if expected_source is not None:
        source = task_path(record.get("source", ""), "Preflight source")
        if source.resolve() != expected_source.resolve():
            raise ValueError("Preflight source does not name the expected staged file")
        sidecar = source.with_suffix(source.suffix + ".preflight.json")
        if not sidecar.is_file() or read(sidecar) != record:
            raise ValueError("Validation record differs from the actual preflight sidecar")
        actual = sha(source)
        if (record.get("source_sha256_before") != actual
                or record.get("source_sha256_after") != actual):
            raise ValueError("Preflight source bytes/hash differ")
        module_root = (TASK / record.get("module_root", "")).resolve()
        if (not module_root.is_relative_to(TASK.resolve()) or not module_root.is_dir()
                or module_for(module_root, expected_source) != expected_module):
            raise ValueError("Preflight -R root does not yield its recorded module identity")
        command = record.get("command", [])
        executable = str(Path(runtime["executable"]).resolve())
        root_text = str(module_root.resolve())
        source_text = str(expected_source.resolve())
        if (not command or command[0] != executable or "-DautoImplicit=false" not in command
                or "-R" not in command or command[command.index("-R") + 1] != root_text
                or command[-1] != source_text):
            raise ValueError("Recorded Lean command does not match the exact source and module root")
        if expected_mode == "emit-olean":
            if "-o" not in command:
                raise ValueError("Definition emitter command does not request the certified OLean")
        elif "-o" in command:
            raise ValueError("A modecheck command unexpectedly requested an OLean output")
    manifest_path = task_path(record.get("manifest", ""), "Preflight source manifest")
    manifest_sha = sha(manifest_path)
    if (record.get("manifest_sha256_before") != manifest_sha
            or record.get("manifest_sha256_after") != manifest_sha
            or record.get("manifest_unchanged") is not True):
        raise ValueError("Preflight's source manifest changed or differs from its certificate")
    staged_manifest = read(manifest_path)
    before_inputs = record.get("manifest_input_hashes_before")
    after_inputs = record.get("manifest_input_hashes_after")
    if not isinstance(before_inputs, dict) or before_inputs != after_inputs:
        raise ValueError("Preflight's manifest input certificates are absent or unstable")
    historical_inputs = {}
    for relative, evidence in before_inputs.items():
        if (not isinstance(evidence, dict)
                or evidence.get("expected_sha256") != evidence.get("actual_sha256")
                or evidence.get("matches") is not True):
            raise ValueError(f"Preflight manifest input changed: {relative}")
        resolution = certified_input_path(relative, evidence["expected_sha256"])
        if resolution["provenance"] != "current":
            historical_inputs[relative] = {key: value for key, value in resolution.items() if key != "path"}
    for relative, expected in staged_manifest.get("input_hashes", {}).items():
        evidence = before_inputs.get(relative)
        if (not isinstance(evidence, dict) or evidence.get("expected_sha256") != expected
                or evidence.get("actual_sha256") != expected or evidence.get("matches") is not True):
            raise ValueError(f"Preflight input record does not match its manifest: {relative}")
    if (record.get("source_certificate") != record.get("source_certificate_after")
            or record.get("source_certificate_stable") is not True):
        raise ValueError("Preflight source/lineage certificate changed")
    source_cert = record.get("source_certificate")
    source_cert_row = source_cert.get("source", {}) if isinstance(source_cert, dict) else {}
    source_from_cert = task_path(source_cert_row.get("path", ""), "Preflight source certificate path")
    if (source_from_cert.resolve() != expected_source.resolve()
            or source_cert_row.get("sha256") != sha(expected_source)
            or source_cert_row.get("matches") is not True):
        raise ValueError("Preflight source certificate does not match the compiled source")
    for lineage in source_cert.get("lineage", []):
        path = task_path(lineage.get("path", ""), "Preflight source lineage")
        if (sha(path) != lineage.get("expected_sha256")
                or lineage.get("actual_sha256") != lineage.get("expected_sha256")
                or lineage.get("matches") is not True):
            raise ValueError("Preflight source lineage hash is invalid")
    if not 0 < record.get("timeout_seconds", 0) <= 300 or not 0 < record.get("seconds", 0) <= 300:
        raise ValueError("Preflight exceeds the 300-second theorem budget")
    verify_runtime(record, runtime, runtime_sha, runtime_compatibility)
    log = task_path(record.get("log", ""), "Preflight log")
    log_root = (VERIFICATION / "staged-preflight-logs").resolve()
    if (not log.resolve().is_relative_to(log_root) or sha(log) != record.get("log_sha256")
            or record.get("stdout_and_stderr_sha256") != record.get("log_sha256")):
        raise ValueError("Captured compiler stdout/stderr log is missing or changed")
    if expected_imports is not None and record.get("imports") != expected_imports:
        raise ValueError("Preflight exact import list differs")
    deps = record.get("dependency_oleans")
    if not isinstance(deps, list) or not deps:
        raise ValueError("Preflight has no imported OLean certificates")
    for dep in deps:
        path = Path(dep.get("path", ""))
        relative_olean = Path(*dep.get("module", "").split(".")).with_suffix(".olean")
        resolved_root = Path(dep.get("resolved_search_root", ""))
        first_match = next((root / relative_olean for root in map(Path, record["effective_lean_path"])
                            if (root / relative_olean).is_file()), None)
        if (not path.is_file() or dep.get("sha256_before") != dep.get("sha256_after")
                or dep.get("sha256_after") != sha(path)
                or resolved_root not in list(map(Path, record["effective_lean_path"]))
                or first_match is None or first_match.resolve() != path.resolve()
                or dep.get("stable_during_compile") is not True):
            raise ValueError("Imported dependency OLean is missing or changed")
    if expected_mode == "emit-olean":
        output = task_path(record.get("output_olean", ""), "Emitted Definition OLean")
        if (expected_output is None or output.resolve() != expected_output.resolve()
                or sha(output) != record.get("output_olean_sha256")):
            raise ValueError("Emitted Definition OLean identity/hash differs")
    elif record.get("output_olean") is not None or record.get("output_olean_sha256") is not None:
        raise ValueError("Modecheck unexpectedly claims an OLean output")
    return {"record": record, "record_sha256": sha_bytes((json.dumps(record, ensure_ascii=False,
                                                                        sort_keys=True) + "\n").encode("utf-8")),
            "sidecar": sidecar.relative_to(TASK).as_posix() if expected_source is not None else None,
            "sidecar_sha256": sha(sidecar) if expected_source is not None else None,
            "log": log.relative_to(TASK).as_posix(), "log_sha256": sha(log),
            "seconds": record["seconds"], "mode": expected_mode,
            "actual_module_identity": expected_module,
            "historical_input_hash_drift": historical_inputs,
            "dependencies": [{"module": d["module"], "sha256": d["sha256_after"],
                              "path": d["path"]} for d in deps]}


def verify_manifest(stage_name):
    manifest_path = VERIFICATION / "bundles-preview" / "Definitions" / f"{stage_name}.manifest.json"
    output = manifest_path.with_name(stage_name + ".lean")
    manifest = read(manifest_path)
    if (manifest.get("platform_module") != "Definitions." + stage_name
            or not isinstance(manifest.get("source_module"), str)
            or manifest.get("provisional") is not True
            or manifest.get("validated") is not False
            or manifest.get("submission_ready") is not False):
        raise ValueError("Expected an explicitly provisional preview bundle manifest")
    expected_platform = "Definitions.Def_" + manifest["source_module"].replace(".", "_")
    if expected_platform != manifest["platform_module"]:
        raise ValueError("Source module does not map to the declared platform module")
    source = workspace_path(manifest["source"], "Definition port source")
    original = workspace_path(manifest["original_source"], "Original Definition source")
    bundle = workspace_path(manifest["output"], "Generated Definition source")
    expected_relative = Path("port/lean") / Path(*manifest["source_module"].split("."))
    original_relative = Path("source/lean") / Path(*manifest["source_module"].split("."))
    if (source.resolve() != (TASK / expected_relative.with_suffix(".lean")).resolve()
            or original.resolve() != (TASK / original_relative.with_suffix(".lean")).resolve()):
        raise ValueError("Manifest source/original-source paths do not correspond to their Lean module")
    if bundle.resolve() != output.resolve():
        raise ValueError("Manifest output does not resolve to the expected preview Definition path")
    for path, field in [(source, "source_sha256"), (original, "original_source_sha256"),
                        (bundle, "output_sha256")]:
        if sha(path) != manifest.get(field):
            raise ValueError(f"Manifest source/output digest mismatch: {field}")
    _, _, archive = archive_index()
    inputs = verify_manifest_inputs(manifest, archive)
    raw = verify_import_header(bundle, manifest.get("imports"))
    import_inventory_resolution = certified_input_path(
        "verification/ast-import-inventory.json", manifest["input_hashes"]["verification/ast-import-inventory.json"], archive)
    import_inventory_path = import_inventory_resolution["path"]
    import_inventory = read(import_inventory_path)
    source_imports = import_inventory.get("modules", {}).get(manifest["source_module"])
    transitive = import_inventory.get("transitive_external_imports", {}).get(manifest["source_module"])
    if (not source_imports or not transitive
            or source_imports.get("source_sha256") != sha(source)
            or transitive.get("unextracted_project_modules") != []
            or manifest["imports"] != transitive.get("external_imports")):
        raise ValueError("Bundle imports do not equal the AST-certified complete external import closure")
    return {"path": manifest_path, "manifest": manifest, "source": source,
            "original_source": original, "bundle": bundle, "imports": manifest["imports"],
            "input_hashes": inputs, "import_inventory_sha256": sha(import_inventory_path),
            "import_inventory_provenance": {key: value for key, value in import_inventory_resolution.items()
                                             if key != "path"},
            "output_bytes": raw}


def verify_graph_names(manifest, names):
    _, _, archive = archive_index()
    inputs = manifest.get("input_hashes", {})
    unit_plan_resolution = certified_input_path(
        "verification/platform-unit-plan-preview.json", inputs["verification/platform-unit-plan-preview.json"], archive)
    graph_resolution = certified_input_path(
        "verification/decl_graph.jsonl", inputs["verification/decl_graph.jsonl"], archive)
    unit_plan_path = unit_plan_resolution["path"]
    graph_path = graph_resolution["path"]
    unit_plan = read(unit_plan_path)
    units = {unit["id"]: unit for unit in unit_plan["units"]}
    graph_rows = [json.loads(line) for line in graph_path.read_bytes().splitlines() if line]
    graph = {row["name"]: row for row in graph_rows}
    selected_names = []
    for unit_id in manifest.get("selected_units", []):
        unit = units.get(unit_id)
        if not unit or unit.get("module") != manifest["source_module"]:
            raise ValueError("Selected unit is absent or owned by another source module")
        if len(unit.get("graph_names", [])) != 1 or unit.get("is_instance_command"):
            raise ValueError("Closed-provider certificate only accepts one ordinary graph name per unit")
        name = unit["graph_names"][0]
        row = graph.get(name)
        if not row or row.get("module") != manifest["source_module"]:
            raise ValueError("Graph declaration does not match the source-owned module")
        if row.get("kind") not in {"def", "definition", "abbrev"} or row.get("isPrivate") or row.get("isInstance"):
            raise ValueError("Provider declaration is not an ordinary public definition")
        selected_names.append(name)
    if selected_names != names:
        raise ValueError("Snapshot names/order disagree with AST-selected source-owned declarations")
    selected = set(selected_names)
    for name in selected_names:
        row = graph[name]
        for dep in row.get("typeDeps", []) + row.get("valueDeps", []) + row.get("constructors", []):
            if dep in graph and dep not in selected:
                raise ValueError(f"Definition is not kernel-closed over project declarations: {name} -> {dep}")
    return {"graph_sha256": sha(graph_path), "graph_provenance": graph_resolution["provenance"],
            "unit_plan_sha256": sha(unit_plan_path), "unit_plan_provenance": unit_plan_resolution["provenance"],
            "graph_names": selected_names}


def verify_local_stage(stage_name, current_runtime, current_runtime_sha, runtime_compatibility):
    bundle_data = verify_manifest(stage_name)
    manifest, bundle, source = bundle_data["manifest"], bundle_data["bundle"], bundle_data["source"]
    stage = VERIFICATION / "definition-validation" / stage_name
    validation_path = stage / "validation.json"
    validation = read(validation_path)
    names = validation.get("provided_names")
    if (not isinstance(names, list) or not names or validation.get("validated") is not True
            or validation.get("kernel_types_and_values_equal") is not True
            or validation.get("standard_axioms_only") is not True
            or validation.get("submission_ready") is not False):
        raise ValueError("Closed Definition validation does not have the required positive evidence")
    if (validation.get("source_manifest_sha256") != sha(bundle_data["path"])
            or validation.get("output_sha256") != sha(bundle)
            or validation.get("snapshot_core_sha256") != sha(VERIFICATION / "TypedSnapshotCore.inc")):
        raise ValueError("Validation certificate no longer binds the preview bundle and snapshot core")
    graph_cert = verify_graph_names(manifest, names)
    if (manifest.get("renames") or manifest.get("kept_local_instances")
            or manifest.get("elaboration_only_helpers")):
        raise ValueError("Provider candidate is not a closed ordinary no-helper Definition bundle")

    rows_by_variant = {}
    for variant in ("original", "generated"):
        json_path = stage / f"{variant}-definitions.json"
        expected_sha = validation.get("type_value_snapshots", {}).get(json_path.name)
        if not json_path.is_file() or sha(json_path) != expected_sha:
            raise ValueError(f"Typed {variant} snapshot is absent or changed")
        rows = read(json_path)
        if [row.get("name") for row in rows] != names:
            raise ValueError(f"Typed {variant} snapshot declarations/order differ")
        rows_by_variant[variant] = rows
    for old, new in zip(rows_by_variant["original"], rows_by_variant["generated"]):
        if (len(old.get("levelParams", [])) != len(new.get("levelParams", []))
                or normalize(old, "type") != normalize(new, "type")
                or normalize(old, "value") != normalize(new, "value")):
            raise ValueError("Original and generated kernel types/values differ: " + old["name"])

    snapshot_paths = {}
    for filename, expected in validation.get("snapshots", {}).items():
        path = stage / filename
        if not path.is_file() or sha(path) != expected:
            raise ValueError(f"Typed snapshot source changed: {filename}")
        snapshot_paths[filename] = path
    if set(snapshot_paths) != {"SnapshotOriginal.lean", "SnapshotGenerated.lean"}:
        raise ValueError("Expected exactly Original and Generated typed snapshot source files")

    records = validation.get("preflights")
    if not isinstance(records, list) or len(records) != 3:
        raise ValueError("Expected exactly three actual stage preflight records")
    record_runtime_shas = {record.get("runtime_sha256") for record in records}
    if len(record_runtime_shas) != 1:
        raise ValueError("Definition preflights do not share one exact runtime fingerprint")
    record_runtime_sha = next(iter(record_runtime_shas))
    runtime_map = runtime_compatibility["record_runtime_by_sha256"]
    if record_runtime_sha not in runtime_map:
        raise ValueError("Definition preflight runtime is neither the current nor certified historical runtime")
    runtime = runtime_map[record_runtime_sha]
    runtime_sha = record_runtime_sha
    historical_context = None
    if runtime_sha != current_runtime_sha:
        if runtime_sha != runtime_compatibility["historical_stage_root_sha256"]:
            raise ValueError("Only the exact archived pre-stage-root runtime is allowed historically")
        historical_context = runtime_compatibility
    bundle_root = (VERIFICATION / "bundles-preview").resolve()
    emitter = next((r for r in records if r.get("mode") == "emit-olean"), None)
    if emitter is None:
        raise ValueError("Original local Definition OLean emission is missing")
    original_snapshot_record = next((r for r in records if Path(r.get("source", "")).name == "SnapshotOriginal.lean"), None)
    generated_snapshot_record = next((r for r in records if Path(r.get("source", "")).name == "SnapshotGenerated.lean"), None)
    if original_snapshot_record is None or generated_snapshot_record is None:
        raise ValueError("Original/generated snapshot module preflight records are incomplete")
    olean_rel = Path("verification/staged-build/lib/lean") / Path(*manifest["platform_module"].split("."))
    olean_path = (TASK / olean_rel).with_suffix(".olean")
    if not olean_path.is_file():
        raise ValueError("Emitted Definition OLean is missing")
    expected_header = verify_import_header(bundle, manifest["imports"])
    preflight_summaries = []
    # Record order is captured generation order: emit, original snapshot, generated snapshot.
    for record in records:
        source_basename = Path(record.get("source", "")).name
        if record is emitter:
            expected_source = bundle
            expected_mode = "emit-olean"
            expected_identity = manifest["platform_module"]
            imports = manifest["imports"]
            expected_output = olean_path
        elif source_basename == "SnapshotOriginal.lean":
            expected_source = snapshot_paths["SnapshotOriginal.lean"]
            expected_mode = "modecheck"
            expected_identity = "SnapshotOriginal"
            imports = ["Lean", manifest["source_module"]]
            expected_output = None
        elif source_basename == "SnapshotGenerated.lean":
            expected_source = snapshot_paths["SnapshotGenerated.lean"]
            expected_mode = "modecheck"
            expected_identity = "SnapshotGenerated"
            imports = ["Lean", manifest["platform_module"]]
            expected_output = None
        else:
            raise ValueError("Unexpected module identity in Definition preflight list")
        if record.get("actual_module_identity") != expected_identity:
            raise ValueError("Snapshot compiler module identity differs")
        preflight_summaries.append(verify_preflight(record, runtime, runtime_sha, expected_mode,
                                                    expected_identity, expected_source,
                                                    expected_output, imports, historical_context))
    manifest_inputs = manifest.get("input_hashes", {})
    for record in records:
        captured = record.get("manifest_input_hashes_before", {})
        for relative, expected in manifest_inputs.items():
            evidence = captured.get(relative)
            if (not isinstance(evidence, dict) or evidence.get("expected_sha256") != expected
                    or evidence.get("actual_sha256") != expected or evidence.get("matches") is not True):
                raise ValueError(f"Compiler did not use the bundle's certified input: {relative}")

    axioms = validation.get("axioms", {})
    expected_source_axioms = audit_axioms(task_path(original_snapshot_record["log"], "Original snapshot log"), names)
    expected_gen_axioms = audit_axioms(task_path(generated_snapshot_record["log"], "Generated snapshot log"), names)
    if axioms.get("source") != expected_source_axioms or axioms.get("generated") != expected_gen_axioms:
        raise ValueError("Recorded source/generated axiom declarations disagree with actual output logs")
    if any(not set(values) <= ALLOWED_AXIOMS for side in axioms.values() for values in side.values()):
        raise ValueError("Unknown, sorry, or nonstandard proof axiom is present")

    return {
        "source_module": manifest["source_module"],
        "platform_module": manifest["platform_module"],
        "canonical_reuse": False,
        "manifest": bundle_data["path"].relative_to(ROOT).as_posix(),
        "manifest_sha256": sha(bundle_data["path"]),
        "source": source.relative_to(ROOT).as_posix(),
        "source_sha256": sha(source),
        "original_source": bundle_data["original_source"].relative_to(ROOT).as_posix(),
        "original_source_sha256": sha(bundle_data["original_source"]),
        "output": bundle.relative_to(ROOT).as_posix(),
        "output_sha256": sha(bundle),
        "output_bytes": len(bundle_data["output_bytes"]),
        "imports": manifest["imports"],
        "manifest_input_hashes": bundle_data["input_hashes"],
        "exact_import_closure": {"source_inventory_sha256": bundle_data["import_inventory_sha256"],
                                 "imports": manifest["imports"]},
        "provided_names": names,
        "project_kernel_dependencies": [],
        "ast_ownership": graph_cert,
        "local_olean": {"path": olean_path.relative_to(TASK).as_posix(),
                        "sha256": sha(olean_path), "module": manifest["platform_module"],
                        "preflight_mode": emitter["mode"], "preflight_log_sha256": emitter["log_sha256"]},
        "validation_path": validation_path.relative_to(TASK).as_posix(),
        "validation_sha256": sha(validation_path),
        "snapshot_core_sha256": validation["snapshot_core_sha256"],
        "typed_snapshots": {path.name: sha(path) for path in snapshot_paths.values()},
        "type_value_snapshot_hashes": dict(validation["type_value_snapshots"]),
        "kernel_types_and_values_equal": True,
        "standard_axioms_only": True,
        "axioms": axioms,
        "preflights": preflight_summaries,
        "compiler_runtime_sha256": runtime_sha,
        "compiler_runtime_provenance": ("current-runtime" if runtime_sha == current_runtime_sha
                                         else "historical-stage-root-runtime-exact-audited-compatible"),
        "current_final_generation_eligible": False,
        "plan_status": "historical-provisional-preview-only",
        "submission_ready": False,
    }


def verify_publication(stage_name, provider, runtime, runtime_sha, runtime_compatibility=None):
    stage = VERIFICATION / "definition-validation" / stage_name
    pub_path = stage / "publication.json"
    payload_path = stage / "publish-payload.json"
    metadata_path = stage / "metadata.json"
    payload_raw = payload_path.read_bytes()
    payload = json.loads(payload_raw.decode("utf-8"))
    publication = read(pub_path)
    metadata = read(metadata_path)
    readback = publication.get("target_readback")
    body = readback.get("body") if isinstance(readback, dict) else None
    definition = payload.get("definition")
    if not isinstance(definition, str):
        raise ValueError("Published Definition payload has no UTF-8 source body")
    def_raw = definition.encode("utf-8")
    payload_sha = sha_bytes(payload_raw)
    expected_env = "0df444a360eaa60ab8c11dca51a86af692955474"
    if (publication.get("publish_payload_sha256") != payload_sha
            or publication.get("definition_name") != payload.get("definition_name")
            or publication.get("visibility") != "public"
            or publication.get("environment") != expected_env
            or payload.get("env") != expected_env
            or payload.get("private") is not False):
        raise ValueError("Published Definition payload metadata/hash do not match publication intent")
    response = publication.get("publish_response", {})
    verdict = publication.get("last_publish_verdict", {})
    verdict_body = verdict.get("body", {}) if isinstance(verdict, dict) else {}
    if (response.get("http_status") != 202
            or response.get("body", {}).get("job_id") != publication.get("job_id")
            or verdict.get("http_status") != 200
            or verdict_body.get("id") != publication.get("job_id")
            or verdict_body.get("status") != "PUBLISHED"
            or verdict_body.get("theorem_id") != publication.get("definition_id")
            or verdict_body.get("visibility") != "public"):
        raise ValueError("Recorded Definition publication job is not a completed public PUBLISHED result")
    target_name = "Definitions." + stage_name
    if provider["platform_module"] != target_name:
        raise ValueError("Published theorem is not the name exported by its local generated bundle")
    if payload.get("definition_name") != provider["platform_module"].removeprefix("Definitions.Def_"):
        raise ValueError("Published public name does not correspond to the generated Definition module")
    # Exact public source body must be either the generated bundle or the separately certified
    # actual uploaded byte variant (Collision's historical LF normalization).
    bundle_path = workspace_path(provider["output"], "Generated Definition source")
    variant_cert_path = stage / "uploaded-variant-validation.json"
    variant = None
    if def_raw != bundle_path.read_bytes():
        if not variant_cert_path.is_file():
            raise ValueError("Published source differs from generated bytes and has no separate variant certificate")
        variant = read(variant_cert_path)
        uploaded = stage / "uploaded" / "Definitions" / f"{stage_name}.lean"
        uploaded_snapshot = stage / "uploaded" / "SnapshotUploaded.lean"
        uploaded_manifest_path = uploaded.with_suffix(".manifest.json")
        snapshot_manifest_path = uploaded_snapshot.with_suffix(".manifest.json")
        uploaded_manifest = read(uploaded_manifest_path)
        snapshot_manifest = read(snapshot_manifest_path)
        if (not uploaded.is_file() or uploaded.read_bytes() != def_raw
                or sha(uploaded) != variant.get("server_definition_sha256")
                or variant.get("server_readback_definition_sha256") != sha_bytes(def_raw)
                or variant.get("validated") is not True
                or variant.get("kernel_types_and_values_equal") is not True
                or variant.get("standard_axioms_only") is not True
                or variant.get("runtime_sha256") != runtime_sha):
            raise ValueError("Published byte variant lacks a valid independent uploaded-body certificate")
        if (variant.get("definition_id") != publication.get("definition_id")
                or variant.get("old_publication_sha256") != sha(pub_path)
                or variant.get("published_payload_file_sha256") != payload_sha
                or variant.get("published_payload_wire_sha256") != payload_sha
                or variant.get("server_definition_sha256") != sha_bytes(def_raw)
                or variant.get("server_definition_bytes") != len(def_raw)
                or not isinstance(body, dict)
                or variant.get("server_readback_definition_sha256") != sha_bytes(
                    body.get("definition", "").encode("utf-8"))
                or variant.get("original_validation_sha256") != provider["validation_sha256"]):
            raise ValueError("Uploaded variant certificate does not bind to this publication/readback/original proof")
        if (uploaded_manifest.get("output") != uploaded.relative_to(ROOT).as_posix()
                or uploaded_manifest.get("output_sha256") != sha(uploaded)
                or uploaded_manifest.get("definition_id") != publication.get("definition_id")
                or uploaded_manifest.get("published_payload_sha256") != payload_sha
                or snapshot_manifest.get("output") != uploaded_snapshot.relative_to(ROOT).as_posix()
                or snapshot_manifest.get("output_sha256") != sha(uploaded_snapshot)
                or snapshot_manifest.get("imports") != ["Lean", *provider["imports"]]):
            raise ValueError("Uploaded source/snapshot manifest identity, body, or imports differ")
        if (variant.get("uploaded_lean_source_sha256") != sha(uploaded)
                or variant.get("uploaded_source_manifest_sha256") != sha(uploaded_manifest_path)
                or variant.get("uploaded_snapshot_source_sha256") != sha(uploaded_snapshot)
                or variant.get("uploaded_snapshot_manifest_sha256") != sha(snapshot_manifest_path)):
            raise ValueError("Uploaded source or snapshot hashes differ from the supplemental certificate")
        if not variant.get("preflights") or set(variant["preflights"]) != {
                uploaded.name, uploaded_snapshot.name}:
            raise ValueError("Uploaded byte variant does not have exactly two recorded preflights")
        variant_preflights = []
        for source, module, imports in [
                (uploaded, provider["platform_module"], provider["imports"]),
                (uploaded_snapshot, "SnapshotUploaded", ["Lean", *provider["imports"]])]:
            record = variant["preflights"][source.name]
            sidecar = source.with_suffix(source.suffix + ".preflight.json")
            if (not sidecar.is_file()
                    or variant["preflight_record_sha256"].get(source.name) != sha(sidecar)
                    or read(sidecar) != record):
                raise ValueError("Uploaded variant preflight sidecar differs from the saved certificate")
            verified = verify_preflight(record, runtime, runtime_sha, "modecheck", module,
                                        source, None, imports, runtime_compatibility)
            variant_preflights.append(verified)
        if variant.get("provided_names") != provider["provided_names"]:
            raise ValueError("Uploaded byte variant certifies different declarations")
        uploaded_rows = stage / "uploaded-definitions.json"
        original_rows = stage / "original-definitions.json"
        if not uploaded_rows.is_file() or not original_rows.is_file():
            raise ValueError("Uploaded variant type/value rows are missing")
        for left, right in zip(read(original_rows), read(uploaded_rows)):
            if (left.get("name") != right.get("name")
                    or len(left.get("levelParams", [])) != len(right.get("levelParams", []))
                    or normalize(left, "type") != normalize(right, "type")
                    or normalize(left, "value") != normalize(right, "value")):
                raise ValueError("Published variant changed a source-owned kernel type/value")
        uploaded_audit = audit_axioms(task_path(
            variant["preflights"][uploaded_snapshot.name]["log"], "Uploaded snapshot log"),
            provider["provided_names"])
        recorded_uploaded_axioms = variant.get("axioms", {}).get("uploaded")
        if (recorded_uploaded_axioms != uploaded_audit
                or variant.get("axioms", {}).get("source") != provider["axioms"].get("source")
                or any(not set(values) <= ALLOWED_AXIOMS for values in uploaded_audit.values())):
            raise ValueError("Uploaded variant proof axioms differ from the actual snapshot log")
        variant_record = {"kind": "separate-uploaded-byte-variant", "path": uploaded.relative_to(TASK).as_posix(),
                          "sha256": sha(uploaded), "certificate": variant_cert_path.relative_to(TASK).as_posix(),
                          "certificate_sha256": sha(variant_cert_path),
                          "original_local_olean_retained_separately": True,
                          "preflights": variant_preflights,
                          "kernel_types_and_values_equal": True}
    else:
        variant_record = None
    if not isinstance(readback, dict):
        raise ValueError("PUBLISHED Definition is missing its public readback record")
    if (readback.get("http_status") != 200 or not isinstance(body, dict)
            or body.get("theorem_id") != publication.get("definition_id")
            or body.get("theorem_name") != payload.get("definition_name")
            or body.get("status") != "Definition"
            or body.get("visibility") != "public"
            or body.get("mathlib_rev") != publication.get("environment")
            or body.get("definition") != definition):
        raise ValueError("Public Definition readback does not exactly match the payload/body/id")
    name = payload.get("definition_name")
    metadata_name = metadata.get("definition_title")
    if metadata_name and body.get("theorem_title") != metadata_name:
        raise ValueError("Public readback title disagrees with staged metadata")
    for field in ("definition_title", "natural_language_statement", "source", "tags"):
        if payload.get(field) != metadata.get(field):
            raise ValueError(f"Public payload metadata differs from its staged metadata: {field}")
    for payload_field, readback_field in (("definition_title", "theorem_title"),
                                          ("natural_language_statement", "natural_language_statement"),
                                          ("source", "source"), ("tags", "tags")):
        left, right = body.get(readback_field), payload.get(payload_field)
        if payload_field == "tags" and isinstance(left, list) and isinstance(right, list):
            equal = len(left) == len(set(left)) and len(right) == len(set(right)) and set(left) == set(right)
        else:
            equal = left == right
        if not equal:
            raise ValueError(f"Public readback metadata differs from submitted payload: {payload_field}")
    return {"status": "PUBLISHED", "theorem_name": name,
            "definition_id": publication["definition_id"], "environment": publication["environment"],
            "visibility": "public", "publication_sha256": sha(pub_path),
            "payload_path": payload_path.relative_to(TASK).as_posix(), "payload_sha256": payload_sha,
            "payload_definition_sha256": sha_bytes(def_raw), "payload_bytes": len(def_raw),
            "exact_public_readback": True, "readback_sha256": sha_bytes(
                json.dumps(body, ensure_ascii=False, sort_keys=True).encode("utf-8")),
            "uploaded_variant": variant_record}


def build_provider_certificate():
    runtime_compatibility = runtime_transition_certificate()
    runtime_path = VERIFICATION / "lean-runtime.json"
    runtime = runtime_compatibility["current"]["runtime"]
    runtime_sha = runtime_compatibility["current"]["sha256"]
    if runtime.get("environment", {}).get("LEAN_PATH") is None:
        raise ValueError("Pinned runtime has no captured Lean environment")
    archive, archive_manifest_path, archived_files = archive_index()
    providers = []
    for stage_name in STAGES:
        provider = verify_local_stage(stage_name, runtime, runtime_sha, runtime_compatibility)
        compiler_runtime_sha = provider["compiler_runtime_sha256"]
        compiler_runtime = runtime_compatibility["record_runtime_by_sha256"][compiler_runtime_sha]
        record_compatibility = (runtime_compatibility
                                if compiler_runtime_sha == runtime_compatibility["historical_stage_root_sha256"]
                                else None)
        provider["public_readback"] = verify_publication(stage_name, provider, compiler_runtime,
                                                         compiler_runtime_sha, record_compatibility)
        if record_compatibility is not None:
            provider["historical_runtime_evidence"] = {
                "runtime_path": runtime_compatibility["historical_stage_root"]["path"],
                "runtime_sha256": compiler_runtime_sha,
                "transition_audit": runtime_compatibility["transition_audit"],
                "prior_transition": runtime_compatibility["prior_transition"],
                "original_compiler_fingerprints_preserved": True,
            }
        providers.append(provider)
    return {
        "schema_version": 1,
        "certificate_kind": "closed-definition-provider-certificate",
        "runtime_path": runtime_path.relative_to(TASK).as_posix(),
        "runtime_sha256": runtime_sha,
        "runtime_transition_audit": {
            "current_runtime": {"path": runtime_compatibility["current"]["path"],
                                "sha256": runtime_compatibility["current"]["sha256"]},
            "historical_stage_root_runtime": {"path": runtime_compatibility["historical_stage_root"]["path"],
                                              "sha256": runtime_compatibility["historical_stage_root"]["sha256"]},
            "transition_audit": runtime_compatibility["transition_audit"],
            "prior_transition": runtime_compatibility["prior_transition"],
            "validated_exact_historical_compiler_runtime": True,
            "changed_project_pin_only_lakefile": True,
            "same_lean_executable_and_normalized_search_paths": True,
        },
        "historical_799_archive": {
            "manifest": archive_manifest_path.relative_to(TASK).as_posix(),
            "manifest_sha256": sha(archive_manifest_path),
            "indexed_modules": archive["indexed_modules"],
            "preserved_input_count": len(archived_files),
            "all_preserved_input_hashes_verified": True,
            "archive_validated_as_proof": False,
            "extraction_state_recovered": False,
            "unrecovered_state_sha256": UNRECOVERED_799_STATE_SHA256,
        },
        "providers": providers,
        "scope_limits": {
            "all_current_bundle_plans_remain_provisional": True,
            "preview_plan_is_not_promoted_to_final_875_module_plan": True,
            "certifies_existing_local_and_published_definition_evidence_only": True,
            "does_not_certify_any_Theorems_or_Solutions_node": True,
            "does_not_modify_accepted_or_published_artifacts": True,
        },
        "submission_ready": False,
    }


def main():
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", default="provider-certificate.json",
                        help="Output filename inside verification/ (default: provider-certificate.json)")
    args = parser.parse_args()
    out = (VERIFICATION / args.output).resolve()
    if not out.is_relative_to(VERIFICATION.resolve()):
        raise ValueError("Provider certificate output must stay inside verification/")
    certificate = build_provider_certificate()
    write_json(out, certificate)
    print(json.dumps({"validated": True, "providers": [row["platform_module"] for row in certificate["providers"]],
                      "public_readbacks": [row["public_readback"]["definition_id"] for row in certificate["providers"]],
                      "output": out.relative_to(TASK).as_posix(), "output_sha256": sha(out),
                      "preview_plan_final": False, "submission_ready": False}))


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError) as exc:
        raise SystemExit("Definition provider certificate refused to proceed: " + str(exc))
