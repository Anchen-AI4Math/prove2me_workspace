"""Run only under lake env; save the exact pinned Lean executable and search paths."""
import hashlib
import json
import os
from pathlib import Path
import shutil

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]


def hashes():
    return {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
            for name in ("lakefile.lean", "lake-manifest.json", "lean-toolchain")}


def main():
    executable = shutil.which("lean")
    if executable is None or not os.environ.get("LEAN_PATH"):
        raise SystemExit("Capture must run under the workspace's lake env")
    executable = str(Path(executable).resolve())
    # Keep only runtime variables; no account tokens or credential variables.
    runtime = {"executable": executable, "project_hashes": hashes(),
               "executable_sha256": hashlib.sha256(Path(executable).read_bytes()).hexdigest(),
               "environment": {name: os.environ[name]
                               for name in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT")
                               if name in os.environ}}
    output = TASK / "verification/lean-runtime.json"
    output.write_text(json.dumps(runtime, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"runtime_captured": True, "executable": executable,
                      "project_hashes": runtime["project_hashes"]}))


if __name__ == "__main__":
    main()
