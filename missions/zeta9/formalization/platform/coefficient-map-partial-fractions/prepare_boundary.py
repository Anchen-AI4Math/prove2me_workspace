"""Recompile prior exact native boundary checks against the actual staged global Solution."""
from pathlib import Path
import hashlib,json,os,subprocess,sys
sys.stdout.reconfigure(encoding="utf-8")
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[2];PROJECT=OUT / "project"
original=TASK / "verification/formalization-coefficient-map-partial-fractions-2026-10-03/independent-boundary-audit.lean"
s=original.read_text(encoding="utf-8-sig")
s=s.replace("import missions.zeta9.formalization.CoefficientMapPartialFractions","import Solutions.Sol_ZetaNine_CoefficientMapPartialFractions_actual_global_partial_fractions")
s=s.replace("actual_global_partial_fractions","checked_actual_global_partial_fractions")
# Restore module path after renaming theorem references only in this audit wrapper.
s=s.replace("Sol_ZetaNine_CoefficientMapPartialFractions_checked_actual_global_partial_fractions","Sol_ZetaNine_CoefficientMapPartialFractions_actual_global_partial_fractions")
s=s.replace("quartic_is_proper n W hW","(by unfold ProperMultiplier; omega)")
a=s.index("  have hW := weightedNumerator_zero_implies_multiplier_zero")
b=s.index("\n\ntheorem pf_ind_n_zero_X_five_rational_sum_zero",a)
s=s[:a]+'''  have h := congrArg (fun p : ℚ[X] => p.eval 1) hz
  norm_num [weightedNumerator, baseNumerator, baseU] at h
'''+s[b:]
for dest in [OUT / "stage-boundary-audit.lean",PROJECT / "stage-boundary-audit.lean"]:dest.write_text(s,encoding="utf-8",newline="\n")
(OUT / "stage-boundary-provenance.json").write_text(json.dumps({"prior_native_audit_task_relative":original.relative_to(TASK).as_posix(),"prior_native_audit_sha256":hashlib.sha256(original.read_bytes()).hexdigest(),"changes":"Import complete staged global Solution, use its renamed exact global endpoint, inline audit-only quartic degree omega, replace unused Injectivity proof dependency with direct polynomial evaluation at1; native boundary statements remain exact.","proof_source_modified":False},indent=2)+"\n",encoding="utf-8")
env=os.environ.copy();env.pop("LEAN_PATH",None)
p=subprocess.run(["lake","env","lean","stage-boundary-audit.lean"],cwd=PROJECT,env=env,capture_output=True)
(OUT / "stage-boundary-audit.log").write_bytes(p.stdout+p.stderr)
(OUT / "stage-boundary-audit-exit.txt").write_text(str(p.returncode)+"\n",encoding="utf-8")
records=[json.loads(line) for line in p.stdout.decode("utf-8-sig").splitlines() if line.startswith("{")]
(OUT / "stage-boundary-report.json").write_text(json.dumps({"exit_code":p.returncode,"records":records,"all_standard_axioms":all(set(r["axioms"])<={"propext","Classical.choice","Quot.sound"} for r in records),"log_sha256":hashlib.sha256((OUT / "stage-boundary-audit.log").read_bytes()).hexdigest()},ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
print(json.dumps({"boundary_exit":p.returncode,"records":len(records)}),flush=True)
if p.returncode:print((p.stdout+p.stderr).decode("utf-8-sig"),flush=True)
assert p.returncode==0
