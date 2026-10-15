"""Run a frozen mission command list serially; stop on the first failed context."""
import argparse
import hashlib
import json
import shlex
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

TASK = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("command_file")
args = parser.parse_args()
file = (TASK / args.command_file).resolve()
if not file.is_relative_to(TASK / "verification"):
    raise ValueError("Command list escapes this mission's verification directory")
raw = file.read_bytes()
commands = []
for line in raw.decode("utf-8").splitlines():
    if not line.strip():
        continue
    parts = shlex.split(line)
    if parts[:1] == ["&"] and len(parts) > 2:
        if Path(parts[1]).resolve() != Path(sys.executable).resolve():
            raise ValueError("PowerShell command selects a different Python runtime")
        parts = ["python", *parts[2:]]
    if (parts[:2] != ["python", "scripts/preflight_staged_module_windows_bounded.py"]
            or "--timeout-seconds" not in parts
            or parts[parts.index("--timeout-seconds") + 1] != "300"):
        raise ValueError("Only the existing 300-second bounded runner is allowed")
    commands.append([sys.executable, "-X", "utf8", *parts[1:]])
stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S_%fZ")
output = file.parent / ("bounded-batch-" + stamp + ".json")
record = {"command_file": file.relative_to(TASK).as_posix(),
          "command_file_sha256": hashlib.sha256(raw).hexdigest(),
          "serial_execution": True, "context_count": len(commands), "results": []}


def save():
    output.write_bytes((json.dumps(record, ensure_ascii=False, indent=2) + "\n").encode())


save()
for index, command in enumerate(commands, 1):
    if file.read_bytes() != raw:
        raise ValueError("Frozen command list changed during execution")
    print(json.dumps({"context": index, "total": len(commands), "started": command[4]}), flush=True)
    result = subprocess.run(command, cwd=TASK, capture_output=True,
                            creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
    log = file.parent / ("bounded-batch-" + stamp + "-c" + str(index) + ".log")
    log.write_bytes(result.stdout + result.stderr)
    row = {"context": index, "command": command, "exit_code": result.returncode,
           "log": log.relative_to(TASK).as_posix(), "log_sha256": hashlib.sha256(log.read_bytes()).hexdigest()}
    record["results"].append(row)
    save()
    print(json.dumps(row), flush=True)
    if result.returncode:
        print(result.stdout.decode("utf-8", errors="replace")[-5000:], flush=True)
        print(result.stderr.decode("utf-8", errors="replace")[-5000:], flush=True)
        sys.exit(result.returncode)
record["all_contexts_passed"] = True
save()
print(json.dumps({"all_contexts_passed": True, "record": output.relative_to(TASK).as_posix()}), flush=True)
