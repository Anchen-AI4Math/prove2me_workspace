"""Generate exact point-log witnesses for the independent fixed-model bound."""
from fractions import Fraction as F
import importlib.util
import json
from pathlib import Path
import sys
here=Path(__file__).resolve().parent
source=Path('D:/users/self_projects/math_discovery/3 SUM/3sum_certificate_1p960614_v3/3sum_certificate_v3')
sys.path.insert(0,str(source))
spec=importlib.util.spec_from_file_location('audited_certificate',source/'verify_certificate.py')
m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
data=json.loads((source/'certificates/c232_quartic.json').read_text(encoding='utf-8'))
t=m.rational(data['barrier_split']); u=m.rational(data['barrier_ratio_point'])
points=[('32*split',32*t,18),('2*(1-split)',2*(1-t),26),
        ('1+split/231',1+t/231,4),('8*ratioPoint',8*u,18),
        ('2*(1-ratioPoint)',2*(1-u),24),('1+ratioPoint/231',1+u/231,5)]
record=[]
def lean(q): return f'({q.numerator}/{q.denominator} : ℝ)'
for expr,y,n in points:
    iv=m.log_iv(y)
    lo=m.floor_dec(iv.lo,22); hi=m.ceil_dec(iv.hi,22)
    z=(y-1)/(y+1)
    while True:
        s=sum((z**(2*i+1)/F(2*i+1) for i in range(n)),F(0))
        tail=z**(2*n+1)/(1-z*z)
        if lo<=2*s and 2*(s+tail)<=hi: break
        n+=1
    record.append(dict(expr=expr,y=str(y),z=str(z),lo=str(lo),hi=str(hi),terms=n))
head='''import Submission.ThreeSum.FixedModelAlgebra

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
open scoped BigOperators

noncomputable section
namespace ThreeSum1960614.FixedModel

def ratioPoint : ℝ := 859960785302793/5000000000000000

private def series (n : ℕ) (z : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, z^(2*i+1)/(2*i+1)

private theorem interval {y z L U : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1)
    (hy : (1+z)/(1-z)=y) (n : ℕ)
    (hl : L ≤ 2*series n z)
    (hu : 2*(series n z+z^(2*n+1)/(1-z^2)) ≤ U) :
    L ≤ Real.log y ∧ Real.log y ≤ U := by
  have hleft := mul_le_mul_of_nonneg_left (Real.sum_range_le_log_div hz0 hz1 n)
    (by norm_num : (0 : ℝ) ≤ 2)
  have hright := mul_le_mul_of_nonneg_left (Real.log_div_le_sum_range_add hz0 hz1 n)
    (by norm_num : (0 : ℝ) ≤ 2)
  have hlo : 2*series n z ≤ Real.log y := by
    rw [← hy]
    simpa [series,mul_comm,mul_left_comm,mul_assoc,div_eq_mul_inv] using hleft
  have hhi : Real.log y ≤ 2*(series n z+z^(2*n+1)/(1-z^2)) := by
    rw [← hy]
    calc
      _ = 2*(1/2*Real.log ((1+z)/(1-z))) := by ring
      _ ≤ _ := by simpa [series] using hright
  exact ⟨hl.trans hlo,hhi.trans hu⟩

theorem witness_logs :
'''
parts=[f'    ({lean(F(r["lo"]))} ≤ Real.log ({r["expr"]}) ∧\n      Real.log ({r["expr"]}) ≤ {lean(F(r["hi"]))})' for r in record]
code=head+' ∧\n'.join(parts)+' := by\n  refine ⟨?_,?_,?_,?_,?_,?_⟩\n'
for r in record:
    code+=f'  · exact interval (z := {lean(F(r["z"]))}) (by norm_num) (by norm_num)\n'
    code+=f'      (by norm_num [split,ratioPoint]) {r["terms"]} (by norm_num [series]) (by norm_num [series])\n'
code+='\nend ThreeSum1960614.FixedModel\n'
dest=here/'machine/lean/Submission/ThreeSum/ModelWitnessLogs.lean'
assert not dest.exists(),'Do not overwrite an edited proof module'
dest.write_text(code,encoding='utf-8')
(here/'verification/model-log-witnesses.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print('Generated six exact point log intervals; terms:',[r['terms'] for r in record])
