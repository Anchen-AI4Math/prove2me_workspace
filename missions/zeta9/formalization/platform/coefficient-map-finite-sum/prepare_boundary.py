"""Recompile exact prior FS independent boundaries and new all-Nat shifts against staged grouped Sol."""
from pathlib import Path
import hashlib,json,os,subprocess,sys
sys.stdout.reconfigure(encoding='utf-8')
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[2];PROJECT=OUT/'project'
original=TASK/'verification/formalization-coefficient-map-finite-sum-2026-10-03/independent-boundary-audit.lean'
s=original.read_text(encoding='utf-8-sig')
s=s.replace('import missions.zeta9.formalization.CoefficientMapFiniteSum','import Solutions.Sol_ZetaNine_CoefficientMapFiniteSum_actual_grouped_finite_identity')
s=s.replace('actual_grouped_finite_identity n T W hp\n','checked_actual_grouped_finite_identity n T W hp\n')
s=s.replace('`ZetaNine.CoefficientMapFiniteSum.actual_grouped_finite_identity,','`ZetaNine.CoefficientMapFiniteSum.checked_actual_grouped_finite_identity,')
extra='''
theorem fs_stage_difference_T_zero (s j : ℕ) :
    harmonicPower s (0+j)-harmonicPower s 0 =
      ∑ k ∈ Icc 1 j, 1/((0 : ℚ)+(k : ℚ))^s := harmonic_difference_eq_shifted s 0 j

theorem fs_stage_difference_j_zero (s T : ℕ) :
    harmonicPower s (T+0)-harmonicPower s T =
      ∑ k ∈ Icc (1 : ℕ) 0, 1/((T : ℚ)+(k : ℚ))^s := harmonic_difference_eq_shifted s T 0

theorem fs_stage_difference_s_zero (T j : ℕ) :
    harmonicPower 0 (T+j)-harmonicPower 0 T =
      ∑ k ∈ Icc 1 j, 1/((T : ℚ)+(k : ℚ))^0 := harmonic_difference_eq_shifted 0 T j

theorem fs_stage_harmonicPower_s_zero (N : ℕ) : harmonicPower 0 N = (N : ℚ) := by
  simp [harmonicPower]

'''
s=s.replace('run_meta do',extra+'run_meta do')
s=s.replace('`fs_ind_n_zero_X_four_not_two_degree_gap] do emit name',
 '`fs_ind_n_zero_X_four_not_two_degree_gap, `fs_stage_difference_T_zero, `fs_stage_difference_j_zero,\n    `fs_stage_difference_s_zero, `fs_stage_harmonicPower_s_zero] do emit name')
for p in [OUT/'stage-boundary-audit.lean',PROJECT/'stage-boundary-audit.lean']:p.write_text(s,encoding='utf-8',newline='\n')
(OUT/'stage-boundary-provenance.json').write_text(json.dumps({'original_task_relative':original.relative_to(TASK).as_posix(),
 'original_sha256':hashlib.sha256(original.read_bytes()).hexdigest(),
 'changes':'Import actual staged grouped Sol and resolve selected renamed grouped theorem; all original40 source/value/closed statements exact. Append four genuine allNat/T0/j0/s0/harmonicPower0 checks. No original proof body is otherwise changed.'},indent=2)+'\n',encoding='utf-8')
env=os.environ.copy();env.pop('LEAN_PATH',None);env['LEAN_NUM_THREADS']='1'
p=subprocess.run(['lake','env','lean','stage-boundary-audit.lean'],cwd=PROJECT,env=env,capture_output=True)
(OUT/'stage-boundary-audit.log').write_bytes(p.stdout+p.stderr)
(OUT/'stage-boundary-audit-exit.txt').write_text(str(p.returncode)+'\n',encoding='utf-8')
records=[json.loads(t) for t in p.stdout.decode('utf-8-sig').splitlines() if t.startswith('{')]
(OUT/'stage-boundary-report.json').write_text(json.dumps({'exit_code':p.returncode,'records':records,
 'all_standard_axioms':all(set(r['axioms'])<={'propext','Classical.choice','Quot.sound'} for r in records),
 'log_sha256':hashlib.sha256((OUT/'stage-boundary-audit.log').read_bytes()).hexdigest()},ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'boundary_exit':p.returncode,'records':len(records)}),flush=True)
if p.returncode:print((p.stdout+p.stderr).decode('utf-8-sig'),flush=True)
assert p.returncode==0
