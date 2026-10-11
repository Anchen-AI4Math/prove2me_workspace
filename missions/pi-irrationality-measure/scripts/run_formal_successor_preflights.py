"""Run the frozen f2/f3 four-file checks serially; stop at the first failure."""
from pathlib import Path
import json
import subprocess
import sys

TASK = Path(__file__).resolve().parents[1]
SPECS = {"f2": "OAI_PiExponent_FormalLogTruncation_logTail_mem_rationalWeightedIdeal",
         "f3": "OAI_PiExponent_FormalLogTruncation_shiftMap_truncatedFormalJet"}

for node, stem in SPECS.items():
    root = "flp3/" + node
    names = ["Thm_" + stem + ".lean", "Sol_" + stem + ".lean",
             "SnapshotOriginal.lean", "SnapshotGeneratedWithRefs.lean"]
    for index, name in enumerate(names, 1):
        command = [sys.executable, str(TASK / "scripts/preflight_staged_module.py"), root + "/" + name,
                   "--root", root, "--imports-manifest", root + "/c" + str(index) + ".json",
                   "--timeout-seconds", "300"]
        result = subprocess.run(command, cwd=TASK, capture_output=True, check=False)
        (TASK / "verification" / ("flp3-" + node + "-" + str(index) + "-console.json")).write_bytes(result.stdout)
        (TASK / "verification" / ("flp3-" + node + "-" + str(index) + "-stderr.txt")).write_bytes(result.stderr)
        print(json.dumps({"node": node, "file": name, "exit_code": result.returncode}), flush=True)
        if result.returncode:
            sys.exit(result.returncode)
