"""Execute copied official Lean oracles; only config and parser-snapshot extras."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

sys.stdout.reconfigure(encoding="utf-8")
OUT = Path(__file__).resolve().parent
TASK = OUT.parents[2]
ROOT = TASK.parents[1]
OLD = TASK / "formalization/platform/coefficient"
SOURCE = TASK / "formalization/CoefficientMap.lean"
EXPECTED = "e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03"

def sha(data):
    return hashlib.sha256(data).hexdigest()

assert sha(SOURCE.read_bytes()) == EXPECTED
stage1 = (OLD / "extract_decl_graph.lean").read_text(encoding="utf-8-sig")
assert stage1.count("missions.zeta9.formalization.ShortZeroCoefficient") == 2
stage1 = stage1.replace("missions.zeta9.formalization.ShortZeroCoefficient", "missions.zeta9.formalization.CoefficientMap")
stage1 = stage1.replace("missions/zeta9/formalization/platform/coefficient/decl_graph.jsonl", "missions/zeta9/formalization/platform/coefficient-map/decl_graph.jsonl")
(OUT / "extract_decl_graph.lean").write_text(stage1, encoding="utf-8")
stage2 = (OLD / "extract_sketch_info.lean").read_text(encoding="utf-8-sig")
stage2 = stage2.replace("missions/zeta9/formalization/platform/coefficient/oracle-input.lean", "missions/zeta9/formalization/platform/coefficient-map/oracle-input.lean")
marker = "  let fm := inputCtx.fileMap\n"
assert stage2.count(marker) == 1
extra = '''  -- Parser-certified command spans only; used to remove diagnostics.
  for cmd in s.commands do
    IO.println (Json.mkObj [("kind", Json.str "command"),
      ("syntaxKind", Json.str cmd.getKind.toString),
      ("span", rangeJson fm (some cmd))]).compress
'''
stage2 = stage2.replace(marker, marker + extra)
(OUT / "extract_sketch_info.lean").write_text(stage2, encoding="utf-8")
original_lib = OUT / "build/original"
olean = original_lib / "missions/zeta9/formalization/CoefficientMap.olean"
olean.parent.mkdir(parents=True, exist_ok=True)
rows = []

def run(label, source, args=(), output=None):
    env = f'$env:LEAN_PATH = "{original_lib.as_posix()};" + $env:LEAN_PATH + ";{ROOT.as_posix()}"\n'
    cmd = env + "& lean "
    if output:
        cmd += '-o "' + output.as_posix() + '" '
    cmd += '"' + source.as_posix() + '" '
    cmd += " ".join('"' + a + '"' for a in args) + "\nexit $LASTEXITCODE\n"
    wrapper = OUT / (label + ".ps1")
    wrapper.write_text(cmd, encoding="utf-8")
    invocation = ["lake", "env", "pwsh", "-NoProfile", "-ExecutionPolicy", "Bypass", "-File", str(wrapper)]
    p = subprocess.run(invocation, cwd=ROOT, capture_output=True)
    log = OUT / (label + ".log")
    log.write_bytes(p.stdout + p.stderr)
    (OUT / (label + "-exit.txt")).write_text(str(p.returncode) + "\n", encoding="utf-8")
    assert sha(SOURCE.read_bytes()) == EXPECTED
    row = {"label": label, "command": invocation, "working_directory": str(ROOT), "exit_code": p.returncode, "source": str(source), "source_sha256": sha(source.read_bytes()), "log": log.name, "log_sha256": sha(log.read_bytes()), "wrapper": wrapper.name, "wrapper_sha256": sha(wrapper.read_bytes()), "output": str(output) if output else None, "output_sha256": sha(output.read_bytes()) if output and output.exists() else None}
    rows.append(row)
    print(label + ": exit " + str(p.returncode), flush=True)
    assert p.returncode == 0, log.read_text(encoding="utf-8-sig")

run("original-compile", SOURCE, output=olean)
run("stage1-extract", OUT / "extract_decl_graph.lean")
# `lean --run` is needed for the Stage2 executable.
stage2_wrapper = OUT / "stage2-extract.ps1"
stage2_wrapper.write_text(f'$env:LEAN_PATH = "{original_lib.as_posix()};" + $env:LEAN_PATH + ";{ROOT.as_posix()}"\n& lean --run "{(OUT / "extract_sketch_info.lean").as_posix()}" "{SOURCE.as_posix()}" "ZetaNine.CoefficientMap"\nexit $LASTEXITCODE\n', encoding="utf-8")
invocation = ["lake", "env", "pwsh", "-NoProfile", "-ExecutionPolicy", "Bypass", "-File", str(stage2_wrapper)]
p = subprocess.run(invocation, cwd=ROOT, capture_output=True)
(OUT / "sketch_info.jsonl").write_bytes(p.stdout)
(OUT / "stage2-extract-errors.log").write_bytes(p.stderr)
(OUT / "stage2-extract-exit.txt").write_text(str(p.returncode) + "\n", encoding="utf-8")
assert p.returncode == 0, p.stderr.decode("utf-8-sig")
assert sha(SOURCE.read_bytes()) == EXPECTED
snapshot = (OUT / "oracle-input.lean").read_bytes()
assert snapshot == SOURCE.read_bytes().replace(b"\r\n", b"\n")
facts = [json.loads(line) for line in p.stdout.decode("utf-8-sig").splitlines() if line.startswith("{")]
rows.append({"label": "stage2-extract", "command": invocation, "working_directory": str(ROOT), "exit_code": p.returncode, "source": str(SOURCE), "source_sha256": EXPECTED, "oracle_input_sha256": sha(snapshot), "oracle_input_bytes": len(snapshot), "stdout": "sketch_info.jsonl", "stdout_sha256": sha(p.stdout), "stderr": "stage2-extract-errors.log", "stderr_sha256": sha(p.stderr), "wrapper": stage2_wrapper.name, "wrapper_sha256": sha(stage2_wrapper.read_bytes()), "fact_counts": {kind: sum(f["kind"] == kind for f in facts) for kind in ["decl", "ref", "command"]}})
(OUT / "oracle-execution-receipt.json").write_text(json.dumps({"source_sha256": EXPECTED, "source_unchanged": True, "official_stage1": "formalization/platform/coefficient/extract_decl_graph.lean", "official_stage2": "formalization/platform/coefficient/extract_sketch_info.lean", "changes": ["Only Stage1 import/project/output configuration changed.", "Stage2 output snapshot directory changed; parser command spans added solely for diagnostic removal."], "rows": rows}, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"source_sha256": EXPECTED, "stage2_fact_counts": rows[-1]["fact_counts"]}, ensure_ascii=False), flush=True)
