"""Record the actual Lean parser header span, without re-building proofs."""
from pathlib import Path
import hashlib
import json
import subprocess

OUT = Path(__file__).resolve().parent
TASK = OUT.parents[2]
ROOT = TASK.parents[1]
SOURCE = TASK / "formalization/CoefficientMapJet.lean"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
wrapper = OUT / "stage2-header.ps1"
wrapper.write_text(f'& lean --run "{(OUT / "extract_header.lean").as_posix()}" "{SOURCE.as_posix()}"\nexit $LASTEXITCODE\n', encoding="utf-8")
command = ["lake", "env", "pwsh", "-NoProfile", "-ExecutionPolicy", "Bypass", "-File", str(wrapper)]
p = subprocess.run(command, cwd=ROOT, capture_output=True)
stdout, stderr = OUT / "header_info.jsonl", OUT / "stage2-header-errors.log"
stdout.write_bytes(p.stdout)
stderr.write_bytes(p.stderr)
(OUT / "stage2-header-exit.txt").write_text(str(p.returncode) + "\n", encoding="utf-8")
assert p.returncode == 0, p.stderr.decode("utf-8-sig")
receipt = json.loads((OUT / "oracle-execution-receipt.json").read_text(encoding="utf-8"))
assert sha(SOURCE) == receipt["source_sha256"]
row = {"label": "stage2-header", "command": command, "working_directory": str(ROOT), "exit_code": p.returncode,
       "source": str(SOURCE), "source_sha256": sha(SOURCE), "extractor": "extract_header.lean", "extractor_sha256": sha(OUT / "extract_header.lean"),
       "stdout": stdout.name, "stdout_sha256": sha(stdout), "stderr": stderr.name, "stderr_sha256": sha(stderr),
       "wrapper": wrapper.name, "wrapper_sha256": sha(wrapper)}
receipt["rows"] = [r for r in receipt["rows"] if r["label"] != "stage2-header"] + [row]
(OUT / "oracle-execution-receipt.json").write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print(p.stdout.decode("utf-8-sig").strip())
