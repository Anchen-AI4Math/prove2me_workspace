"""Exact integer-polynomial check of the read Connection snapshot. No Lean runs."""
from pathlib import Path
import json,hashlib
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[1]
SOURCE=TASK/'formalization/CoefficientMapConnection.lean';PAPER=TASK/'round7/research/connection.md'
def clean(p):return {m:c for m,c in p.items() if c}
def add(p,q):
 r=p.copy()
 for m,c in q.items():r[m]=r.get(m,0)+c
 return clean(r)
def neg(p):return {m:-c for m,c in p.items()}
def sub(p,q):return add(p,neg(q))
def mul(p,q):
 r={}
 for (i,j),a in p.items():
  for (k,l),b in q.items():r[i+k,j+l]=r.get((i+k,j+l),0)+a*b
 return clean(r)
def powp(p,k):
 r={(0,0):1}
 while k:
  if k%2:r=mul(r,p)
  p=mul(p,p);k//=2
 return r
def con(a):return {(0,0):a} if a else {}
def degree_t(p):return max((i for i,j in p),default=-1)
def coefficient_t(p,k):return {(0,j):c for (i,j),c in p.items() if i==k}
def substitute_t(p,f):
 r={}
 for (i,j),c in p.items():r=add(r,mul({(0,j):c},powp(f,i)))
 return r
def at_n(p,a):
 r={}
 for (i,j),c in p.items():r[i,0]=r.get((i,0),0)+c*a**j
 return clean(r)
def encoded(p):return [{'t_degree':i,'n_degree':j,'coefficient':c} for (i,j),c in sorted(p.items())]
T={(1,0):1};N={(0,1):1};ONE=con(1);U=mul(T,add(T,N))
# Cast(Nat(n-1)) equals n-1 only on n>=1. This uniform expression models that domain.
V=mul(T,add(T,sub(N,ONE)));W=mul(add(T,ONE),add(T,N))
nm1=sub(T,add(N,ONE));np1=add(T,add(N,ONE))
A=mul(nm1,powp(np1,10));B=mul(add(T,add(mul(con(2),N),ONE)),powp(sub(T,ONE),10))
D=powp(sub(U,add(N,ONE)),10);S=neg(add(T,N))
checks=[]
def check(name,ok,detail=None):
 checks.append({'name':name,'exact_integer_polynomial_check':bool(ok),'detail':detail});assert ok,name
check('D_pullback_factor_matches_paper',D==mul(powp(sub(T,ONE),10),powp(np1,10)))
check('v_minus_n_simple_factor',sub(V,N)==mul(sub(T,ONE),add(T,N)))
check('A_at_one_is_minus_n_times_n_plus_two_power_ten',substitute_t(A,ONE)==neg(mul(N,powp(add(N,con(2)),10))))
check('reflection_keeps_U_and_swaps_v_w',substitute_t(U,S)==U and substitute_t(V,S)==W and substitute_t(W,S)==V)
check('reflection_prefactors_change_sign_and_swap',substitute_t(A,S)==neg(B) and substitute_t(B,S)==neg(A))
basis=[]
for a in range(10):
 h=sub(mul(A,powp(V,a)),mul(B,powp(W,a)))
 check('H_basis_'+str(a)+'_reflection',substitute_t(h,S)==h)
 check('H_basis_'+str(a)+'_leading_t_degree',degree_t(h)==10+2*a and coefficient_t(h,10+2*a)==add(mul(con(7),N),con(18-2*a)))
 residual=h.copy();coeffs={}
 while residual:
  d=degree_t(residual);assert d%2==0;k=d//2;c=coefficient_t(residual,d);coeffs[k]=c
  residual=sub(residual,mul(c,powp(U,k)))
 check('H_basis_'+str(a)+'_integral_U_reconstruction',not residual and max(coeffs)==5+a)
 basis.append({'q_degree':a,'t_degree':degree_t(h),'U_degree':max(coeffs),'leading_coefficient_n':encoded(coeffs[max(coeffs)]),'integer_U_coefficients':{str(k):encoded(c) for k,c in sorted(coeffs.items())}})
# Output coordinates of the Lean map are even t-coefficients, not literal u-coefficients.
change=[]
for i in range(15):
 row=[]
 for k in range(15):
  c=coefficient_t(powp(U,k),2*i);row.append(encoded(c))
  if i>k:assert not c
  if i==k:assert c==ONE
 change.append(row)
check('u_coefficient_to_even_t_coefficient_matrix_unipotent_upper_triangular',True,{'dimension':15,'determinant':1,'fixed_n_or_symbolic_n':True})
q9=powp(V,9);w9=powp(W,9)
actual_paper_H0=sub(at_n(mul(A,q9),0),at_n(mul(B,w9),0))
check('paper_n0_P0_qX9_has_nonzero_q_and_zero_H',not actual_paper_H0 and powp(T,9)!={}, {'P':0,'q':'X^9','both_H_terms':'t^9*(t-1)^10*(t+1)^10'})
leanV0=powp(T,2);paperV0=mul(T,sub(T,ONE))
check('Nat_sub_n0_definition_differs_from_paper_v',leanV0!=paperV0)
leanH0q9=sub(mul(at_n(A,0),powp(leanV0,9)),mul(at_n(B,0),powp(at_n(W,0),9)))
check('paper_n0_kernel_example_is_not_the_same_modified_Lean_H0',leanH0q9!={})
for p,name in [(SOURCE,'observed-Connection-source.lean'),(PAPER,'observed-connection-paper.md')]:
 (OUT/name).write_bytes(p.read_bytes())
data={'status':'EXACT_OFFLINE_ALIGNMENT_CHECK_ONLY_NOT_FINAL_INDEPENDENT_PASS','Lean_executed':False,'author_Connection_not_frozen':True,'source_snapshot_sha256':hashlib.sha256((OUT/'observed-Connection-source.lean').read_bytes()).hexdigest(),'paper_snapshot_sha256':hashlib.sha256((OUT/'observed-connection-paper.md').read_bytes()).hexdigest(),
 'actual_source_path':'formalization/CoefficientMapConnection.lean','paper_path':'round7/research/connection.md','author_source_modified':False,'checks':checks,'basis_certificates':basis,'output_coordinate_change_matrix':change,
 'homogeneous_kernel_scope':'n>=1; q.natDegree<=9; P has no degree bound in the kernel-zero theorem',
 'fifteen_dimensional_scope':'P degree<=4, q degree<=9, n>=1; output coordinates are coeff_t(0,2,...,28)',
 'tenfold_root_argument':'D(t) is divisible by(t-1)^10; A(1)=-n(n+2)^10 nonzero; v(t)-n=(t-1)(t+n) has simple root at1; nonzero q would have root multiplicity at least10 at n, contradicting degree<=9.',
 'no_Aggregate_GL5_hypothesis_needed_by_this_source_kernel_argument':True,'full_R_ratio_formal_coordinate_connection_J_or_irrationality_verified':False}
(OUT/'offline-alignment-report.json').write_bytes((json.dumps(data,ensure_ascii=False,indent=2)+'\n').encode())
print(json.dumps({'offline_checks':len(checks),'all_exact_checks':all(c['exact_integer_polynomial_check'] for c in checks),'Lean_executed':False,'final_independent_PASS_claimed':False}))
