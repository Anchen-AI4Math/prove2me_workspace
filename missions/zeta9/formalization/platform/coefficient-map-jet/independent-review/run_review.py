"""Independently replay Jet integration in a new isolated task-local project."""
from pathlib import Path
import hashlib, json, os, subprocess, sys
sys.stdout.reconfigure(encoding="utf-8")
HERE = Path(__file__).resolve().parent
BATCH = HERE.parent
TASK = BATCH.parents[2]
ROOT = TASK.parents[1]
BASE = TASK / "formalization/platform/coefficient-map"
PROJECT = HERE / "project"
PIN = "0df444a360eaa60ab8c11dca51a86af692955474"
EXPECTED = {"CoefficientMap":"e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03", "CoefficientMapJet":"e50e11c0afd2eaac1d5c58c412e5e59bc5c2068c9826063eacee8dc88fc1735a"}
NS = "ZetaNine.CoefficientMapJet"
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,s):
    p.parent.mkdir(parents=True,exist_ok=True)
    p.write_text(s,encoding="utf-8",newline="\n")
def rows(p): return [json.loads(s) for s in p.read_text(encoding="utf-8-sig").splitlines() if s.startswith("{")]
for name,h in EXPECTED.items(): assert sha(TASK / f"formalization/{name}.lean") == h
PROJECT.mkdir(parents=True,exist_ok=True)
write(PROJECT / "lakefile.lean",f'''import Lake
open Lake DSL
package zeta9JetIntegrationIndependent
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "{PIN}"
lean_lib Native where
  roots := #[`missions.zeta9.formalization.CoefficientMap, `missions.zeta9.formalization.CoefficientMapJet]
  globs := #[.one `missions.zeta9.formalization.CoefficientMap, .one `missions.zeta9.formalization.CoefficientMapJet]
lean_lib Definitions
lean_lib Solutions
lean_lib Theorems
''')
for n in ["lake-manifest.json","lean-toolchain"]: (PROJECT / n).write_bytes((ROOT / n).read_bytes())
(PROJECT / ".lake").mkdir(exist_ok=True)
if not (PROJECT / ".lake/packages").exists():
    p = subprocess.run(["cmd","/c","mklink","/J",str(PROJECT / ".lake/packages"),str(ROOT / ".lake/packages")],capture_output=True)
    assert p.returncode == 0,(p.stdout+p.stderr).decode(errors="replace")
for name in EXPECTED:
    p = PROJECT / f"missions/zeta9/formalization/{name}.lean"
    p.parent.mkdir(parents=True,exist_ok=True)
    p.write_bytes((TASK / f"formalization/{name}.lean").read_bytes())
plan = json.loads((BATCH / "root-copy-plan.json").read_text(encoding="utf-8-sig"))
base_def = plan["required_existing_Base_definition"]
base_def_path = base_def["root_relative"]
p = PROJECT / base_def_path
p.parent.mkdir(parents=True,exist_ok=True)
p.write_bytes((BASE / "staged" / base_def_path).read_bytes())
assert sha(p) == base_def["sha256"]
for f in plan["files"]:
    p = PROJECT / f["root_relative_destination"]
    p.parent.mkdir(parents=True,exist_ok=True)
    p.write_bytes((TASK / f["staged_task_relative"]).read_bytes())
    assert sha(p) == f["sha256"]
for filename,old,new in [
    ("extract_decl_graph.lean","missions/zeta9/formalization/platform/coefficient-map-jet/decl_graph.jsonl","../decl_graph.jsonl"),
    ("extract_sketch_info.lean","missions/zeta9/formalization/platform/coefficient-map-jet/oracle-input.lean","../oracle-input.lean")]:
    text = (BATCH / filename).read_text(encoding="utf-8-sig")
    assert text.count(old) == 1
    write(PROJECT / filename,text.replace(old,new))
base_oracle = (BASE / "extract_sketch_info.lean").read_text(encoding="utf-8-sig")
old = "missions/zeta9/formalization/platform/coefficient-map/oracle-input.lean"
assert base_oracle.count(old) == 1
write(PROJECT / "extract_base_sketch.lean",base_oracle.replace(old,"../base-oracle-input.lean"))
(PROJECT / "extract_header.lean").write_bytes((BATCH / "extract_header.lean").read_bytes())
reporters = ["types_original.lean","types_definition.lean"] + [f"types_{i}_{kind}.lean" for i in range(3) for kind in ["solution","reference"]]
for filename in reporters: (PROJECT / filename).write_bytes((BATCH / filename).read_bytes())
graph = rows(BATCH / "decl_graph.jsonl")
proofnames = [g["name"] for g in graph if g["module"].endswith(".CoefficientMapJet") and g["kind"] == "theorem" and g["startLine"] > 0]
assert len(proofnames) == 19
for i,f in enumerate([f for f in plan["files"] if f["root_relative_destination"].startswith("Solutions/")]):
    module = f["root_relative_destination"].removesuffix(".lean").replace("/",".")
    selected = module.split("Sol_ZetaNine_CoefficientMapJet_")[1]
    names = [NS + ".checked_" + selected if n == NS + "." + selected else n for n in proofnames]
    names += ["ZetaNine.CoefficientMap.clearedPoleProduct_ne_zero","solution"]
    original = (BATCH / "types_original.lean").read_text(encoding="utf-8-sig")
    header = original.split('  emit "')[0].replace("import missions.zeta9.formalization.CoefficientMapJet","import " + module)
    write(PROJECT / f"helpers_{i}.lean",header + "".join(f'  emit "{n}" `{n}\n' for n in names))
env = os.environ.copy()
env.pop("LEAN_PATH",None)
receipt = {"source_sha256":EXPECTED,"mathlib_rev":PIN,"root_writes":False,"API_called":False,"rows":[]}
def run(label,command,stdout_file=None):
    p = subprocess.run(command,cwd=PROJECT,env=env,capture_output=True)
    log = HERE / (label + ".log")
    log.write_bytes(p.stdout+p.stderr)
    write(HERE / (label + "-exit.txt"),str(p.returncode) + "\n")
    if stdout_file:
        (HERE / stdout_file).write_bytes(p.stdout)
        (HERE / (label + "-stderr.log")).write_bytes(p.stderr)
    receipt["rows"].append({"label":label,"command":command,"working_directory":str(PROJECT),"exit_code":p.returncode,"log":log.name,"log_sha256":sha(log)})
    write(HERE / "compile-receipt.json",json.dumps(receipt,ensure_ascii=False,indent=2) + "\n")
    print(label + ": exit " + str(p.returncode),flush=True)
    for name,h in EXPECTED.items(): assert sha(TASK / f"formalization/{name}.lean") == h
    if p.returncode: print(log.read_text(encoding="utf-8-sig"),flush=True)
    assert p.returncode == 0
run("toolchain",["lake","env","lean","--version"])
for name in EXPECTED: run("build-original-" + name,["lake","--no-cache","build","missions.zeta9.formalization." + name])
run("stage1-extract",["lake","env","lean","extract_decl_graph.lean"])
run("stage2-extract",["lake","env","lean","--run","extract_sketch_info.lean","missions/zeta9/formalization/CoefficientMapJet.lean","ZetaNine"],"sketch_info.jsonl")
run("stage2-base-extract",["lake","env","lean","--run","extract_base_sketch.lean","missions/zeta9/formalization/CoefficientMap.lean","ZetaNine.CoefficientMap"],"base-sketch_info.jsonl")
run("stage2-header",["lake","env","lean","--run","extract_header.lean","missions/zeta9/formalization/CoefficientMapJet.lean"],"header_info.jsonl")
run("build-Base-Definition",["lake","--no-cache","build",base_def_path.removesuffix(".lean").replace("/",".")])
for i,f in enumerate(plan["files"]): run("build-staged-" + str(i),["lake","--no-cache","build",f["root_relative_destination"].removesuffix(".lean").replace("/",".")])
for filename in reporters: run(filename.removesuffix(".lean"),["lake","env","lean",filename])
for i in range(3): run("helpers_" + str(i),["lake","env","lean",f"helpers_{i}.lean"])
receipt["complete"] = True
receipt["all_exit_codes_actually_observed"] = True
write(HERE / "compile-receipt.json",json.dumps(receipt,ensure_ascii=False,indent=2) + "\n")
print("Independent Jet replay complete: 26 observed successful runs, no native/staged olean cache borrowing.",flush=True)
