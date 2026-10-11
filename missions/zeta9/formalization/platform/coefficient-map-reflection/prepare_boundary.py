"""Recompile original Reflection boundary statements against the actual staged rho1 Solution."""
from pathlib import Path
import hashlib,json,os,subprocess,sys
sys.stdout.reconfigure(encoding="utf-8")
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[2];PROJECT=OUT / "project"
original=TASK / "verification/formalization-coefficient-map-reflection-2026-10-03/independent-boundary-audit.lean"
s=original.read_text(encoding="utf-8-sig")
s=s.replace("import missions.zeta9.formalization.CoefficientMapReflection","import Solutions.Sol_ZetaNine_CoefficientMapReflection_rho_one_zero_of_strong_proper")
s=s.replace("rho_one_zero_of_strong_proper","checked_rho_one_zero_of_strong_proper")
s=s.replace("Sol_ZetaNine_CoefficientMapReflection_checked_rho_one_zero_of_strong_proper","Sol_ZetaNine_CoefficientMapReflection_rho_one_zero_of_strong_proper")
for dest in [OUT / "stage-boundary-audit.lean",PROJECT / "stage-boundary-audit.lean"]:dest.write_text(s,encoding="utf-8",newline="\n")
(OUT / "stage-boundary-provenance.json").write_text(json.dumps({"prior_native_audit_task_relative":original.relative_to(TASK).as_posix(),"prior_native_audit_sha256":hashlib.sha256(original.read_bytes()).hexdigest(),"changes":"Only import the complete actual staged rho1 Solution and resolve its selected renamed endpoint; all original boundary statements and proof bodies otherwise unchanged.","source_modified":False},indent=2)+"\n",encoding="utf-8")
env=os.environ.copy();env.pop("LEAN_PATH",None)
p=subprocess.run(["lake","env","lean","stage-boundary-audit.lean"],cwd=PROJECT,env=env,capture_output=True)
(OUT / "stage-boundary-audit.log").write_bytes(p.stdout+p.stderr)
(OUT / "stage-boundary-audit-exit.txt").write_text(str(p.returncode)+"\n",encoding="utf-8")
records=[json.loads(line) for line in p.stdout.decode("utf-8-sig").splitlines() if line.startswith("{")]
(OUT / "stage-boundary-report.json").write_text(json.dumps({"exit_code":p.returncode,"records":records,"all_standard_axioms":all(set(r["axioms"])<={"propext","Classical.choice","Quot.sound"} for r in records),"log_sha256":hashlib.sha256((OUT / "stage-boundary-audit.log").read_bytes()).hexdigest()},ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
print(json.dumps({"boundary_exit":p.returncode,"records":len(records)}),flush=True)
if p.returncode:print((p.stdout+p.stderr).decode("utf-8-sig"),flush=True)
assert p.returncode==0
