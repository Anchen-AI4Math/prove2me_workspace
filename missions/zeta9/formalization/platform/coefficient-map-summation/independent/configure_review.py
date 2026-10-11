"""Prepare a new independent Sum review; no author or parent file is written."""
from pathlib import Path
import hashlib, json, re, subprocess, sys
sys.stdout.reconfigure(encoding="utf-8")
OUT = Path(__file__).resolve().parent
BATCH = OUT.parent
TASK = OUT.parents[3]
ROOT = TASK.parents[1]
RECIPE = TASK / "formalization/platform/coefficient-map-finite-sum/independent"
CONTROLS = {
    "author-audit.json":"eed4d2dc0cd429401cf7b7bbffd34cb556cc2159f773c57dcdb8fe9cbee37a79",
    "root-copy-plan.json":"ab40b8a9bbb5904e1d6c277c7408803eb60d9b64efd0fea0af14c607386d4adc",
    "source-manifest.json":"73bd31d478d3d53ae6c95c43ef6f6908b05179824eb2ffb63126d74335bb40c8",
    "SHA256SUMS.txt":"f58a3da3f38496e1004ed2f6f2a4185143fa9cddaaf3fbf0e2d0198bb39de813"}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p): return json.loads(p.read_text(encoding="utf-8-sig"))
def write(p,d): p.write_text(json.dumps(d,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
assert all(sha(BATCH/n)==h for n,h in CONTROLS.items())
assert not (OUT/"cache").exists(), "This configuration requires a genuinely new review."
for r in load(BATCH/"source-manifest.json")["files"]:
    p=TASK/r["task_relative"]
    assert sha(p)==r["sha256"] and p.stat().st_size==r["bytes"]
write(OUT/"frozen-controls.json",{"status":"PARENT_FROZEN_AUTHOR_HANDOFF","controls":CONTROLS,
    "independent_review_not_yet_claimed":True})
plan=load(BATCH/"root-copy-plan.json")
original=load(BATCH/"author-audit.json")["sources_sha256"]
assert len(original)==7 and original["CoefficientMapSummation"]=="c207e8fec1358e86afd61d39853a498c9758555286b7774e5f5d7809495e876d"
required={Path(r["root_relative"]).stem:r["sha256"] for r in plan["required_existing_Definitions"]}
defs={"Def_ZetaNine_HarmonicStability":required.pop("Def_ZetaNine_HarmonicStability"),**required}
assert len(defs)==7
for r in plan["files"]:
    p=ROOT/r["root_relative_destination"]
    assert sha(p)==r["sha256"] and p.read_bytes()==(TASK/r["staged_task_relative"]).read_bytes()
for r in plan["required_existing_Definitions"]:
    assert sha(ROOT/r["root_relative"])==r["sha256"]
rootnames=["root-install-receipt.json","task-build.log","task-build-exit.txt","task-check.log","task-check-exit.txt"]
build=(BATCH/"task-build.log").read_text(encoding="utf-8-sig")
jobs=int(re.search(r"Build completed successfully \((\d+) jobs\)\.",build).group(1))
assert jobs==3789 and (BATCH/"task-build-exit.txt").read_text().strip()=="0"
write(OUT/"root-evidence-handoff.json",{"status":"PARENT_INSTALLED_AND_SCOPED_BUILD_OBSERVED",
    "hashes":{n:sha(BATCH/n) for n in rootnames},"observed_build_jobs":jobs})

prep=(RECIPE/"prepare_build.py").read_text(encoding="utf-8")
prep=prep.replace("Independent FS preparation","Independent Summation preparation")
prep=re.sub(r"ORIGINAL = \{.*?\}\nDEFS = \{.*?\}\n", "ORIGINAL = "+repr(original)+"\nDEFS = "+repr(defs)+"\n",prep,flags=re.S)
prep=prep.replace("len(rows) == 11","len(rows) == 15")
(OUT/"prepare_build.py").write_text(prep,encoding="utf-8")

replay=(RECIPE/"replay_batch.py").read_text(encoding="utf-8")
replay=replay.replace("independent FS", "independent Summation").replace("Independent FS", "Independent Summation").replace("CoefficientMapFiniteSum", "CoefficientMapSummation")
replay=replay.replace('len(prep["rows"]) == 11','len(prep["rows"]) == 15')
replay=replay.replace('["HarmonicStability"]','["Def_ZetaNine_HarmonicStability"]')
replay=replay.replace('name == "HarmonicStability"','name == "Def_ZetaNine_HarmonicStability"')
replay=replay.replace('len(core) == 11','len(core) == 24')
(OUT/"replay_batch.py").write_text(replay,encoding="utf-8")

p=subprocess.run(["lake","env","lean","--version"],cwd=ROOT,capture_output=True)
(OUT/"actual-toolchain.log").write_bytes(p.stdout+p.stderr)
(OUT/"actual-toolchain-exit.txt").write_text(str(p.returncode)+"\n",encoding="utf-8")
assert p.returncode==0 and b"4.33.1" in p.stdout
env=load(RECIPE/"actual-environment.json")
env.update({"actual_runtime_exit_code":p.returncode,"lean_runtime_stdout":p.stdout.decode("utf-8"),
    "root_lake_manifest_sha256":sha(ROOT/"lake-manifest.json"),"root_toolchain_sha256":sha(ROOT/"lean-toolchain")})
write(OUT/"actual-environment.json",env)
write(OUT/"recipe-provenance.json",{"status":"PREPARED_ONLY_NOT_FINAL_VERDICT",
    "reference_independent_recipes":[{"task_relative":(RECIPE/n).relative_to(TASK).as_posix(),"sha256":sha(RECIPE/n)} for n in ["prepare_build.py","replay_batch.py","mechanical_review.py","finalize_review.py"]],
    "new_actual_source_count":7,"pure_Harmonic_Def":True,"fresh_native_and_platform_caches":True,
    "native_staged_objects_borrowed":False,"root_scope_API_credentials_writes":False})
print("Summation independent review configuration ready; no proof PASS claimed.")
