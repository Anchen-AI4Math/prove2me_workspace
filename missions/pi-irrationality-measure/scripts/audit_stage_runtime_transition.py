"""Audit the exact Lake registration change and preserve both runtime fingerprints."""
import hashlib
import json
import os
from pathlib import Path

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def paths(value):
    result = []
    for part in value.split(os.pathsep):
        if not part:
            continue
        normalized = os.path.normcase(os.path.abspath(part))
        if normalized not in result:
            result.append(normalized)
    return result


def main():
    old_path = TASK / "verification/lean-runtime-before-stage-roots-20261008.json"
    new_path = TASK / "verification/lean-runtime.json"
    registration_path = TASK / "verification/stage-root-registration.json"
    old, new = json.loads(old_path.read_bytes()), json.loads(new_path.read_bytes())
    registration = json.loads(registration_path.read_bytes())
    old_config = TASK / "verification/lakefile-before-stage-root-registration.lean"
    current_config = ROOT / "lakefile.lean"
    if (sha(old_config) != registration["source_sha256"]
            or sha(current_config) != registration["result_sha256"]
            or old_config.read_bytes()+registration["addition"].encode("utf-8") != current_config.read_bytes()
            or old["project_hashes"]["lakefile.lean"] != sha(old_config)
            or new["project_hashes"]["lakefile.lean"] != sha(current_config)):
        raise ValueError("Stage registration is not the exact appended task-library change")
    for key in ("executable", "executable_sha256"):
        if old[key] != new[key]:
            raise ValueError("Lean executable changed during task library registration")
    for key in ("lake-manifest.json", "lean-toolchain"):
        if old["project_hashes"][key] != new["project_hashes"][key] or sha(ROOT / key) != new["project_hashes"][key]:
            raise ValueError("Lean/Mathlib version pins changed")
    if sha(Path(new["executable"])) != new["executable_sha256"]:
        raise ValueError("Actual Lean executable no longer matches both runtimes")
    comparisons = {}
    for key in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT"):
        before, after = old["environment"].get(key, ""), new["environment"].get(key, "")
        same = paths(before) == paths(after)
        comparisons[key] = {"raw_equal": before == after,
                            "normalized_ordered_unique_paths_equal": same,
                            "old": before, "new": after}
        if not same:
            raise ValueError("Runtime search path changed after task registration: " + key)
    record = {"validated": True, "old_runtime": old_path.relative_to(TASK).as_posix(),
              "old_runtime_sha256": sha(old_path), "new_runtime": new_path.relative_to(TASK).as_posix(),
              "new_runtime_sha256": sha(new_path), "registration_sha256": sha(registration_path),
              "only_project_pin_change": "lakefile.lean", "lean_mathlib_versions_equal": True,
              "lean_executable_byte_identical": True, "ordered_search_paths_equal": True,
              "runtime_path_comparisons": comparisons,
              "historical_certificates_keep_original_fingerprint": True,
              "scope": "Exact addition of three already-validated stage build roots. Historical proof certificates are not rewritten or upgraded."}
    output = TASK / "verification/stage-root-runtime-transition.json"
    output.write_bytes((json.dumps(record, indent=2)+"\n").encode("utf-8"))
    print(json.dumps({key: record[key] for key in
                      ("validated", "old_runtime_sha256", "new_runtime_sha256", "ordered_search_paths_equal")}))


if __name__ == "__main__":
    main()
