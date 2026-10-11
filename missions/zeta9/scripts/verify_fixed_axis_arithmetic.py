"""Rational integration and filtered-minor bookkeeping; no new lattice scan."""
from pathlib import Path
from fractions import Fraction as Q
import sys,json,hashlib
MISSION=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(MISSION/'scripts'))
from verify_vc_budget import log_interval
sys.set_int_max_str_digits(0)

def interval_sum_shifted(a,b,N):
    # Sum j>=0 [1/(2j+a)-1/(2j+b)], 0<a<b.
    partial=sum((1/(2*j+a)-1/(2*j+b) for j in range(N)),Q(0))
    # f decreases: integral_N^infty f <= sum_N^infty f <= integral_(N-1)^infty f.
    low=log_interval((2*N+b)/(2*N+a))[0]/2
    high=log_interval((2*(N-1)+b)/(2*(N-1)+a))[1]/2
    return (partial+low,partial+high)

def main():
    N=2000
    axis=interval_sum_shifted(Q(2),Q(16,7),N)
    odd_late=interval_sum_shifted(Q(8,7),Q(2),N)
    upper_c=interval_sum_shifted(Q(4,3),Q(2),N)
    lower_rho=(Q(15,2)-axis[1]+odd_late[0],Q(15,2)-axis[0]+odd_late[1])
    lower_c=(lower_rho[0]-Q(19,2),lower_rho[1]-Q(19,2))
    upper_rho=(Q(19,2)+upper_c[0],Q(19,2)+upper_c[1])
    assert axis[1]<Q(106618,10**6)
    cuts=sorted(set([Q(0),Q(1,7),Q(2,7),Q(1,3),Q(3,7),Q(4,7),Q(2,3),Q(5,7),Q(6,7),Q(1)]))
    cells=[]
    for lo,hi in zip(cuts,cuts[1:]):
        t=(lo+hi)/2
        even=[int(t>Q(2,3)),2+int(t>Q(6,7)),4+int(t>Q(4,7)),6+int(t>Q(2,7))]
        odd=[1,3+int(t>Q(5,7)),5+int(t>Q(3,7)),7+int(t>Q(1,7))]
        De=(3*t//2)+(7*t//2)
        Do=(3*(1+t)//2)+(7*(1+t)//2)
        d3e=sum(even[:3])-12;d3o=sum(odd[:3])-12
        assert De-d3e==even[3]
        assert Do-d3o==odd[3]+int(t>Q(1,3))
        cells.append({'interval':[str(lo),str(hi)],'even_weights':even,'odd_weights':odd,
                      'even_delta3_lower':d3e,'odd_delta3_lower':d3o,
                      'even_a1_upper':0,'odd_a1_upper':int(t>Q(1,3))})
    def encode(bounds):return {'exact_interval':list(map(str,bounds)),'decimal_interval':list(map(float,bounds))}
    result={'status':'passed','series_terms':N,'axis_exponent':encode(axis),
        'odd_late_t_gt_1_7':encode(odd_late),
        'rho_lower_exponent':encode(lower_rho),'rho_upper_exponent':encode(upper_rho),
        'c_lower_exponent':encode(lower_c),'c_upper_exponent':encode(upper_c),
        'filtered_minor_cells':cells,
        'scope':'Only exact envelope bookkeeping and rigorous series integrals; infinite-parameter local claims are proved in the research note.',
        'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    out=MISSION/'verification/fixed-axis-arithmetic-2026-09-29';out.mkdir(parents=True,exist_ok=True)
    (out/'certificate.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v['decimal_interval'] for k,v in result.items() if isinstance(v,dict) and 'decimal_interval' in v}))
    print('PASS nine rational cells and six rigorous integral bounds; no lattice scan.')

if __name__=='__main__':main()
