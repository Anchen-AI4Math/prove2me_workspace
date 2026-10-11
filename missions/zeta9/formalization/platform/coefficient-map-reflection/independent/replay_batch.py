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
CONTROLS = {'author-audit.json': '7d48c5b7197fc9d9543b35063c256aa73bea606a59866ea81df227f731105651', 'root-copy-plan.json': 'd8a5022833267eba1884f519a2f61b80343dfae4f53820e80ae57c2c9a6e5ad6', 'source-manifest.json': 'fe3ec5bf2de4944eb186c72ad299c1b52e51fbe04f9b68f512253d4e34d9812a', 'SHA256SUMS.txt': 'd7e497dd9e6d69f538dd77390b4b516c0ec8ecdbcb93cdc1eb5a3490e93eaba3'}
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
assert len(preparation["rows"]) == 9 and all(r["exit_code"] == 0 for r in preparation["rows"])
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
    write(OUT / "replay-compile-receipt.json", {"review_role": "Independent final Reflection platform replay", "author_frozen_controls": CONTROLS,
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
run("actual-stage2-header", header, NATIVE, args=[(TASK / "formalization/CoefficientMapReflection.lean").as_posix()], stdout_copy=OUT / "native-header.jsonl")
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
run("independent-new-boundary", OUT / "new-boundary-audit.lean", PLATFORM)
graph_rows = [json.loads(line) for line in (OUT / "native-decl-graph.jsonl").read_text(encoding="utf-8-sig").splitlines() if line.startswith("{")]
by_name = {row["name"]:row for row in graph_rows}
core = [row for row in graph_rows if row["module"].endswith(".CoefficientMapReflection") and row["startLine"] > 0]
reached, work = set(), [row["name"] for row in core] + [row["name"] for row in graph_rows if row["isInstance"]]
while work:
    name = work.pop()
    if name in reached: continue
    reached.add(name)
    work.extend(by_name[name]["typeDeps"] + by_name[name]["valueDeps"])
proof_names = sorted(name for name in reached if by_name[name]["kind"] == "theorem" and by_name[name]["startLine"] > 0)
assert len(proof_names) == 64
helper_audit = OUT / "independent-native-required-proofs.lean"
helper_text = '''import missions.zeta9.formalization.CoefficientMapReflection
import Lean
open Lean Meta
set_option pp.fullNames true
set_option pp.universes false
run_meta do
  for name in [
'''
helper_text += ",\n".join("    `" + name for name in proof_names)
helper_text += '''] do
    let ci ← getConstInfo name
    let typ ← ppExpr ci.type
    let axs ← Lean.collectAxioms name
    IO.println (Json.mkObj [("declaration", Json.str name.toString),
      ("type", Json.str typ.pretty), ("axioms", toJson (axs.toList.map Name.toString))]).compress
'''
helper_audit.write_text(helper_text, encoding="utf-8")
run("independent-native-required-proofs", helper_audit, NATIVE)
write(OUT / "replay-compile-receipt.json", {"review_role": "Independent final Reflection platform replay", "author_frozen_controls": CONTROLS,
    "rows": rows, "complete": True, "all_exit_codes_actually_observed": True, "root_scope_API_credentials_writes": False,
    "frozen_author_bytes_unchanged": True})
