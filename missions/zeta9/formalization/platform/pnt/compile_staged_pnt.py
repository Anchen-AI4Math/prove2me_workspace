"""Build identical canonical Solution bytes against two honest PNT mirrors."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import subprocess, json, hashlib, sys

sys.stdout.reconfigure(encoding="utf-8")
OUT = Path(__file__).resolve().parent
TASK = OUT.parents[2]
ROOT = TASK.parents[1]
UP = TASK / "verification/formalization-pnt-dependency-2026-10-02/project/.lake/build/lib/lean"
PROBLEMS = json.loads((OUT/"problems-request.json").read_text(encoding="utf-8"))["problems"]
STAGED = OUT / "staged"
rows = []

def sha(data):
    return hashlib.sha256(data).hexdigest()

def run(label, source, cwd, lib, output=None):
    prefix = f'"{lib.as_posix()};" + ' if lib else ''
    env = f'$env:LEAN_PATH = {prefix}$env:LEAN_PATH + ";{ROOT.as_posix()};{UP.as_posix()}"; '
    expression = env+f'Set-Location "{cwd.as_posix()}"; lean '
    if output:
        output.parent.mkdir(parents=True, exist_ok=True)
        expression += f'-o "{output.as_posix()}" '
    expression += f'"{source.as_posix()}"; exit $LASTEXITCODE'
    cmd = ["lake","env","pwsh","-NoProfile","-Command",expression]
    original = source.read_bytes()
    proc = subprocess.run(cmd,cwd=ROOT,capture_output=True)
    log = OUT/(label+".log")
    log.write_bytes(proc.stdout+proc.stderr)
    assert source.read_bytes() == original
    row = {"label":label,"source":source.relative_to(OUT).as_posix(),"source_sha256":sha(original),
           "command":cmd,"working_directory":str(ROOT),"lean_working_directory":str(cwd),
           "search_path_prefix":str(lib) if lib else None,"exit_code":proc.returncode,
           "log":log.relative_to(OUT).as_posix(),"log_sha256":sha(log.read_bytes()),
           "output":str(output) if output else None,"output_sha256":sha(output.read_bytes()) if output and output.exists() else None}
    rows.append(row)
    print(label+": exit "+str(proc.returncode),flush=True)
    assert proc.returncode == 0, (label,(proc.stdout+proc.stderr).decode("utf-8"))
    return row

def mirror(mode):
    lib = OUT/"build"/mode
    run(mode+"-boundary",OUT/"boundary-mirror"/mode/"Theorems/Thm_MediumPNT.lean",
        OUT/"boundary-mirror"/mode,lib,lib/"Theorems/Thm_MediumPNT.olean")

for mode in ["native","stub"]:
    mirror(mode)

jobs = [(mode,i,p) for mode in ["native","stub"] for i,p in enumerate(PROBLEMS)]
def compile_solution(job):
    mode,i,p = job
    lib = OUT/"build"/mode
    source = STAGED/p["local_solution"]
    return run(f"{mode}-solution-{i}",source,STAGED,lib,lib/Path(p["local_solution"]).with_suffix(".olean"))
with ThreadPoolExecutor(max_workers=2) as pool:
    list(pool.map(compile_solution,jobs))

for i,p in enumerate(PROBLEMS):
    lib = OUT/"build/stub"
    run(f"reference-{i}",STAGED/p["local_reference"],STAGED,lib,
        lib/Path(p["local_reference"]).with_suffix(".olean"))

def report(job):
    label,script,mode = job
    return run(label,OUT/script,ROOT,OUT/"build"/mode if mode else None)
# A staged Solutions directory shadows unrelated original Solutions modules.
report_jobs = [("types-original","types-original.lean",None)]
report_jobs += [(f"types-boundary-{mode}","types-boundary.lean",mode) for mode in ["native","stub"]]
report_jobs += [(f"types-{mode}-{i}-solution",f"types-{i}-solution.lean",mode) for mode in ["native","stub"] for i in range(len(PROBLEMS))]
report_jobs += [(f"types-{i}-reference",f"types-{i}-reference.lean","stub") for i in range(len(PROBLEMS))]
with ThreadPoolExecutor(max_workers=2) as pool:
    list(pool.map(report,report_jobs))

receipt = {"canonical_solution_bytes_identical_across_modes":True,
           "stub_mirror_is_proof":False,"native_uses_actual_original_pnt_cache":True,
           "rows":rows}
(OUT/"staged-compile-receipt.json").write_text(json.dumps(receipt,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
print("Completed genuine-native and boundary-stub build matrix",flush=True)
