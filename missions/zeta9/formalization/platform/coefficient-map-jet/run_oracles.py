"""Execute official declaration/ref metaprograms on frozen Jet and actual Base."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys
import shutil

sys.stdout.reconfigure(encoding="utf-8")
OUT = Path(__file__).resolve().parent
TASK = OUT.parents[2]
ROOT = TASK.parents[1]
BASE_BATCH = TASK / "formalization/platform/coefficient-map"
ORACLE_ORIGIN = TASK / "formalization/platform/coefficient"
SOURCE = TASK / "formalization/CoefficientMapJet.lean"
BASE_SOURCE = TASK / "formalization/CoefficientMap.lean"
EXPECTED = "e50e11c0afd2eaac1d5c58c412e5e59bc5c2068c9826063eacee8dc88fc1735a"
BASE_EXPECTED = "e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03"

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

assert sha(SOURCE) == EXPECTED and sha(BASE_SOURCE) == BASE_EXPECTED
stage1 = (ORACLE_ORIGIN / "extract_decl_graph.lean").read_text(encoding="utf-8-sig")
assert stage1.count("missions.zeta9.formalization.ShortZeroCoefficient") == 2
stage1 = stage1.replace("import missions.zeta9.formalization.ShortZeroCoefficient", "import missions.zeta9.formalization.CoefficientMapJet")
stage1 = stage1.replace("let projPrefix := `missions.zeta9.formalization.ShortZeroCoefficient", "let projPrefix := `missions.zeta9.formalization")
stage1 = stage1.replace("missions/zeta9/formalization/platform/coefficient/decl_graph.jsonl", "missions/zeta9/formalization/platform/coefficient-map-jet/decl_graph.jsonl")
(OUT / "extract_decl_graph.lean").write_text(stage1, encoding="utf-8")
stage2 = (BASE_BATCH / "extract_sketch_info.lean").read_text(encoding="utf-8-sig").replace("missions/zeta9/formalization/platform/coefficient-map/oracle-input.lean", "missions/zeta9/formalization/platform/coefficient-map-jet/oracle-input.lean")
(OUT / "extract_sketch_info.lean").write_text(stage2, encoding="utf-8")
original_lib = OUT / "build/original"
base_original_lib = BASE_BATCH / "build/original"
base_olean = base_original_lib / "missions/zeta9/formalization/CoefficientMap.olean"
base_receipt = json.loads((BASE_BATCH / "oracle-execution-receipt.json").read_text(encoding="utf-8"))
assert sha(base_olean) == base_receipt["rows"][0]["output_sha256"]
olean = original_lib / "missions/zeta9/formalization/CoefficientMapJet.olean"
olean.parent.mkdir(parents=True, exist_ok=True)
local_base_olean = original_lib / "missions/zeta9/formalization/CoefficientMap.olean"
# Lean picks the first existing module hierarchy; keep its actual Base object in
# the same isolated hierarchy as Jet, rather than a later shadowed prefix.
shutil.copyfile(base_olean, local_base_olean)
assert sha(local_base_olean) == sha(base_olean)
rows = []
prefix = f'$env:LEAN_PATH = "{original_lib.as_posix()};{base_original_lib.as_posix()};" + $env:LEAN_PATH + ";{ROOT.as_posix()}"\n'

def run(label, source, output=None):
    wrapper = OUT / (label + ".ps1")
    command = prefix + "& lean "
    if output:
        command += '-o "' + output.as_posix() + '" '
    command += '"' + source.as_posix() + '"\nexit $LASTEXITCODE\n'
    wrapper.write_text(command, encoding="utf-8")
    invocation = ["lake", "env", "pwsh", "-NoProfile", "-ExecutionPolicy", "Bypass", "-File", str(wrapper)]
    p = subprocess.run(invocation, cwd=ROOT, capture_output=True)
    log = OUT / (label + ".log")
    log.write_bytes(p.stdout + p.stderr)
    (OUT / (label + "-exit.txt")).write_text(str(p.returncode) + "\n", encoding="utf-8")
    rows.append({"label": label, "command": invocation, "working_directory": str(ROOT), "exit_code": p.returncode,
                 "source": str(source), "source_sha256": sha(source), "log": log.name, "log_sha256": sha(log),
                 "wrapper": wrapper.name, "wrapper_sha256": sha(wrapper), "output": str(output) if output else None,
                 "output_sha256": sha(output) if output and output.exists() else None})
    print(label + ": exit " + str(p.returncode), flush=True)
    assert p.returncode == 0, log.read_text(encoding="utf-8-sig")
    assert sha(SOURCE) == EXPECTED and sha(BASE_SOURCE) == BASE_EXPECTED

run("original-compile", SOURCE, output=olean)
run("stage1-extract", OUT / "extract_decl_graph.lean")
wrapper = OUT / "stage2-extract.ps1"
wrapper.write_text(prefix + f'& lean --run "{(OUT / "extract_sketch_info.lean").as_posix()}" "{SOURCE.as_posix()}" "ZetaNine"\nexit $LASTEXITCODE\n', encoding="utf-8")
invocation = ["lake", "env", "pwsh", "-NoProfile", "-ExecutionPolicy", "Bypass", "-File", str(wrapper)]
p = subprocess.run(invocation, cwd=ROOT, capture_output=True)
(OUT / "sketch_info.jsonl").write_bytes(p.stdout)
(OUT / "stage2-extract-errors.log").write_bytes(p.stderr)
(OUT / "stage2-extract-exit.txt").write_text(str(p.returncode) + "\n", encoding="utf-8")
assert p.returncode == 0, p.stderr.decode("utf-8-sig")
snapshot = (OUT / "oracle-input.lean").read_bytes()
assert snapshot == SOURCE.read_bytes().replace(b"\r\n", b"\n")
facts = [json.loads(line) for line in p.stdout.decode("utf-8-sig").splitlines() if line.startswith("{")]
rows.append({"label": "stage2-extract", "command": invocation, "working_directory": str(ROOT), "exit_code": p.returncode,
             "source": str(SOURCE), "source_sha256": EXPECTED, "oracle_input_sha256": hashlib.sha256(snapshot).hexdigest(),
             "oracle_input_bytes": len(snapshot), "stdout": "sketch_info.jsonl", "stdout_sha256": sha(OUT / "sketch_info.jsonl"),
             "stderr": "stage2-extract-errors.log", "stderr_sha256": sha(OUT / "stage2-extract-errors.log"),
             "wrapper": wrapper.name, "wrapper_sha256": sha(wrapper),
             "fact_counts": {kind: sum(f["kind"] == kind for f in facts) for kind in ["decl", "ref", "command"]}})
graph = [json.loads(line) for line in (OUT / "decl_graph.jsonl").read_text().splitlines()]
modules = sorted({r["module"] for r in graph})
assert modules == ["missions.zeta9.formalization.CoefficientMap", "missions.zeta9.formalization.CoefficientMapJet"]
receipt = {"source_sha256": EXPECTED, "source_unchanged": sha(SOURCE) == EXPECTED,
           "base_source_sha256": BASE_EXPECTED, "base_source_unchanged": sha(BASE_SOURCE) == BASE_EXPECTED,
           "base_original_olean": base_olean.relative_to(TASK).as_posix(), "base_original_olean_sha256": sha(base_olean),
           "task_local_base_object_copy": local_base_olean.relative_to(TASK).as_posix(), "task_local_base_object_copy_sha256": sha(local_base_olean),
           "base_original_oracle_receipt": (BASE_BATCH / "oracle-execution-receipt.json").relative_to(TASK).as_posix(),
           "base_original_oracle_receipt_sha256": sha(BASE_BATCH / "oracle-execution-receipt.json"),
           "official_stage1": "formalization/platform/coefficient/extract_decl_graph.lean",
           "official_stage2": "formalization/platform/coefficient/extract_sketch_info.lean",
           "graph_modules": modules,
           "changes": ["Stage1 root/config/output only; common module prefix includes actual imported Base and Jet.", "Stage2 snapshot directory plus parser command spans solely for diagnostic and mission-import replacement."], "rows": rows}
(OUT / "oracle-execution-receipt.json").write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"graph_records": len(graph), "graph_modules": modules, "stage2_fact_counts": rows[-1]["fact_counts"]}, ensure_ascii=False), flush=True)
