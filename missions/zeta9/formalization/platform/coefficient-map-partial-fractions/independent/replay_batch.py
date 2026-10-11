"""Fresh independent official graph/parser/header, staged compiles and import audits."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

sys.stdout.reconfigure(encoding="utf-8")
OUT = Path(__file__).resolve().parent
BATCH = OUT.parent
TASK = OUT.parents[3]
ROOT = TASK.parents[1]
NATIVE = OUT / "cache/native/build"
PLATFORM = OUT / "cache/platform/build"
CONTROLS = {
    "author-audit.json": "d416ad774d2f4a7b599151aef4f460a42395f116cf5e13d577d311ca2a9aa20f",
    "root-copy-plan.json": "6d60147f78b8463471c32fb257c9fd3fbad22c970733487c469dfb821650b847",
    "source-manifest.json": "7ee6aa8437cdaa046a3a24f2e9c0f0033e89a51fc64b389ba992d342ad104208",
    "SHA256SUMS.txt": "f59940eca0b4b749bd363bc46b7b9fb99b79f1faf3022c2ae82b0d802992d32d"}
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def load(path): return json.loads(path.read_text(encoding="utf-8-sig"))
def write(path, obj): path.write_text(json.dumps(obj, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
def frozen():
    assert all(sha(BATCH / name) == h for name,h in CONTROLS.items())
    for row in load(BATCH / "source-manifest.json")["files"]:
        path = TASK / row["task_relative"]
        assert path.stat().st_size == row["bytes"] and sha(path) == row["sha256"]
frozen()
preparation = load(OUT / "prepare-compile-receipt.json")
assert len(preparation["rows"]) == 7 and all(r["exit_code"] == 0 for r in preparation["rows"])
rows = []

def run(label, source, cache, output=None, args=None, stdout_copy=None):
    args = args or []
    wrapper = OUT / (label + ".ps1")
    command = f'$env:LEAN_PATH = "{cache.as_posix()};" + $env:LEAN_PATH + ";{ROOT.as_posix()}"\n& lean '
    if output:
        output.parent.mkdir(parents=True, exist_ok=True)
        command += '-o "' + output.as_posix() + '" '
    if args: command += '--run '
    command += '"' + source.as_posix() + '"' + ''.join(' "' + a + '"' for a in args) + '\nexit $LASTEXITCODE\n'
    wrapper.write_text(command, encoding="utf-8")
    invocation = ["lake", "env", "pwsh", "-NoProfile", "-ExecutionPolicy", "Bypass", "-File", str(wrapper)]
    p = subprocess.run(invocation, cwd=ROOT, capture_output=True)
    log = OUT / (label + ".log")
    log.write_bytes(p.stdout + p.stderr)
    if stdout_copy: stdout_copy.write_bytes(p.stdout)
    exitfile = OUT / (label + "-exit.txt")
    exitfile.write_text(str(p.returncode) + "\n", encoding="utf-8")
    rows.append({"label": label, "command": invocation, "working_directory": str(ROOT), "exit_code": p.returncode,
        "source_root_relative": source.relative_to(ROOT).as_posix(), "source_sha256": sha(source),
        "log": log.name, "log_sha256": sha(log), "exit_file": exitfile.name, "exit_file_sha256": sha(exitfile),
        "wrapper": wrapper.name, "wrapper_sha256": sha(wrapper), "cache": cache.relative_to(OUT).as_posix(),
        "output": output.relative_to(OUT).as_posix() if output else None,
        "output_sha256": sha(output) if output and output.exists() else None,
        "stdout_copy": stdout_copy.name if stdout_copy else None, "stdout_sha256": sha(stdout_copy) if stdout_copy else None})
    write(OUT / "replay-compile-receipt.json", {"review_role": "Independent final PF platform replay", "author_frozen_controls": CONTROLS,
        "rows": rows, "complete": False, "all_exit_codes_actually_observed": True, "root_scope_API_credentials_writes": False})
    print(label + ": exit " + str(p.returncode), flush=True)
    frozen()
    if p.returncode: print(log.read_text(encoding="utf-8-sig"), flush=True)
    assert p.returncode == 0, "Actual failure logs retained."

graph = (BATCH / "extract_decl_graph.lean").read_text(encoding="utf-8-sig")
assert graph.count('IO.FS.writeFile "../decl_graph.jsonl"') == 1
graph = graph.replace('IO.FS.writeFile "../decl_graph.jsonl"', 'IO.FS.writeFile "' + (OUT / "native-decl-graph.jsonl").as_posix() + '"')
(OUT / "extract-native-graph.lean").write_text(graph, encoding="utf-8")
run("actual-stage1", OUT / "extract-native-graph.lean", NATIVE)
for name in preparation["original_sources_sha256"]:
    oracle = (BATCH / ("extract_" + name + "_sketch.lean")).read_text(encoding="utf-8-sig")
    old = "../oracle-input.lean" if name == "CoefficientMapPartialFractions" else "../" + name + "-oracle-input.lean"
    assert oracle.count(old) == 1
    oracle = oracle.replace(old, (OUT / (name + "-native-snapshot.lean")).as_posix())
    script = OUT / ("extract-native-" + name + ".lean")
    script.write_text(oracle, encoding="utf-8")
    run("actual-stage2-" + name, script, NATIVE,
        args=[(TASK / "formalization" / (name + ".lean")).as_posix(), "ZetaNine"], stdout_copy=OUT / (name + "-native-facts.jsonl"))
header = OUT / "extract-native-header.lean"
header.write_bytes((BATCH / "extract_header.lean").read_bytes())
run("actual-stage2-header", header, NATIVE, args=[(TASK / "formalization/CoefficientMapPartialFractions.lean").as_posix()], stdout_copy=OUT / "native-header.jsonl")
plan = load(BATCH / "root-copy-plan.json")
for row in plan["files"]:
    source = TASK / row["staged_task_relative"]
    assert sha(source) == row["sha256"]
    module_path = row["root_relative_destination"]
    output = PLATFORM / (module_path.removesuffix(".lean") + ".olean")
    run("staged-" + Path(module_path).stem, source, PLATFORM, output=output)
scripts = ["types_original.lean", "types_definition.lean"] + [f"types_{i}_{kind}.lean" for i in range(3) for kind in ["solution", "reference"]] + [f"helpers_{i}.lean" for i in range(3)] + ["stage-boundary-audit.lean"]
for name in scripts:
    source = OUT / name
    source.write_bytes((BATCH / name).read_bytes())
    run("replay-" + source.stem, source, NATIVE if name == "types_original.lean" else PLATFORM)
write(OUT / "replay-compile-receipt.json", {"review_role": "Independent final PF platform replay", "author_frozen_controls": CONTROLS,
    "rows": rows, "complete": True, "all_exit_codes_actually_observed": True, "root_scope_API_credentials_writes": False,
    "frozen_author_bytes_unchanged": True})
