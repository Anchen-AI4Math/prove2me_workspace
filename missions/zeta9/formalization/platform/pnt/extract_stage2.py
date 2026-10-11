"""Execute the official elaboration oracle, with parser-span/snapshot extras."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import subprocess, json, hashlib, sys

sys.stdout.reconfigure(encoding="utf-8")
OUT = Path(__file__).resolve().parent
TASK = OUT.parents[2]
ROOT = TASK.parents[1]
UP = TASK / "verification/formalization-pnt-dependency-2026-10-02/project/.lake/build/lib/lean"
modules = json.loads((OUT / "reachable-local-graph.json").read_text(encoding="utf-8-sig"))["participating_source_modules"]

def sha(data):
    return hashlib.sha256(data).hexdigest()

def run(module):
    path = ROOT.joinpath(*module.split(".")).with_suffix(".lean")
    before = path.read_bytes()
    stem = module.replace(".", "_")
    snapshot = OUT / (stem + "-oracle-input.lean")
    expression = (f'$env:LEAN_PATH += ";{ROOT.as_posix()};{UP.as_posix()}"; '
                  f'lean --run "{(OUT / "extract_pnt_sketch_info.lean").as_posix()}" '
                  f'"{path.as_posix()}" "" "{snapshot.as_posix()}"; exit $LASTEXITCODE')
    cmd = ["lake", "env", "pwsh", "-NoProfile", "-Command", expression]
    p = subprocess.run(cmd, cwd=ROOT, capture_output=True)
    (OUT / (stem + "-sketch.jsonl")).write_bytes(p.stdout)
    (OUT / (stem + "-sketch.stderr.log")).write_bytes(p.stderr)
    assert path.read_bytes() == before, "Source changed during elaboration"
    assert p.returncode == 0, (module, p.stdout.decode("utf-8"), p.stderr.decode("utf-8"))
    assert snapshot.read_bytes() == before.replace(b"\r\n", b"\n")
    facts = [json.loads(x) for x in p.stdout.decode("utf-8-sig").splitlines() if x.startswith("{")]
    row = {"module":module, "source":str(path), "source_sha256":sha(before),
           "oracle_input":str(snapshot), "oracle_input_sha256":sha(snapshot.read_bytes()),
           "exit_code":p.returncode, "command":cmd,
           "fact_counts":{k:sum(x["kind"] == k for x in facts) for k in ["decl","ref","import","command"]}}
    print(module + ": " + str(row["fact_counts"]), flush=True)
    return row

with ThreadPoolExecutor(max_workers=2) as pool:
    rows = list(pool.map(run, modules))
(OUT / "stage2-extract-receipt.json").write_text(json.dumps(rows, ensure_ascii=False, indent=2)+"\n", encoding="utf-8")
