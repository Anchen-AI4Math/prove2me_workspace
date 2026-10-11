"""Exact rational instance checks, independent of Lean and not an induction proof."""
from fractions import Fraction as F
import json,sys
from prepare import OUT,verify,dump,SOURCE_HASH
sys.stdout.reconfigure(encoding='utf-8')
verify()
def trim(a):
 a=list(map(F,a))
 while a and a[-1]==0:a.pop()
 return a
def add(a,b):return trim([(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))])
def scale(a,b):return trim([b*x for x in a])
def mul(a,b):
 if not a or not b:return []
 c=[F(0)]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return trim(c)
def power(a,n):
 b=[F(1)]
 for _ in range(n):b=mul(b,a)
 return b
def comp(a,b):
 c=[]
 for x in reversed(a):c=add(mul(c,b),[x])
 return c
def coeff(a,k):return a[k] if k<len(a) else F(0)
def mon(k):return [F(0)]*k+[F(1)]
def degree(a):return max(0,len(a)-1)
def genuine(n):
 u=[0,n,1];v=[0,n-1,1];w=[n,n+1,1]
 d=power(add(u,[-n-1]),10)
 a=mul([-n-1,1],power([n+1,1],10))
 b=mul([2*n+1,1],power([-1,1],10))
 def op(p,q):return add(mul(d,comp(p,u)),add(mul(a,comp(q,v)),scale(mul(b,comp(q,w)),-1)))
 return u,op
def inverse(matrix):
 d=len(matrix);a=[list(map(F,row))+[F(i==j) for j in range(d)] for i,row in enumerate(matrix)]
 determinant=F(1)
 for k in range(d):
  pivot=next((i for i in range(k,d) if a[i][k]),None);assert pivot is not None
  if pivot!=k:a[k],a[pivot]=a[pivot],a[k];determinant=-determinant
  factor=a[k][k];determinant*=factor;a[k]=[x/factor for x in a[k]]
  for i in range(d):
   if i!=k:
    factor=a[i][k];a[i]=[x-factor*y for x,y in zip(a[i],a[k])]
 assert [r[:d] for r in a]==[[F(i==j) for j in range(d)] for i in range(d)]
 return [r[d:] for r in a],determinant
checks=[];instances=[]
def check(name,condition,detail=None):
 assert condition,name
 checks.append({'name':name,'pass':True,'exact_rational_arithmetic':True,'detail':detail})
for n in [1,2,3]:
 u,op=genuine(n);cols=[op(mon(i),[]) if i<5 else op([],mon(i-5)) for i in range(15)]
 matrix=[[coeff(cols[j],2*i) for j in range(15)] for i in range(15)]
 inv,det=inverse(matrix)
 check(f'n{n}_fifteen_matrix_nonsingular',det!=0,{'determinant':str(det),'output_basis':'even t coefficients 0..28','input_basis':'P degrees0..4, q degrees0..9'})
 for i,p in enumerate(cols):
  check(f'n{n}_column{i}_degree_and_affine_reflection',degree(p)<=28 and comp(p,[-n,-1])==p)
 change=[[coeff(power(u,j),2*i) for j in range(15)] for i in range(15)]
 check(f'n{n}_u_to_even_t_basis_unipotent',all(change[i][i]==1 and all(change[i][j]==0 for j in range(i)) for i in range(15)))
 z=[F(1)]
 for k in [1,2,3]:z=mul(z,[-(n+k)*(2*n+k),1])
 rhs=[(f'actual_target_r{r}',scale(mul(z,power([-n-1,1],r)),((n+1)*(n+2))**7)) for r in range(5)]
 rhs+=[('mixed_degree14',list(map(F,range(1,16)))),('zero_target',[])]
 sol=[]
 for label,f in rhs:
  target=comp(f,u);v=[coeff(target,2*i) for i in range(15)]
  c=[sum((inv[i][j]*v[j] for j in range(15)),F(0)) for i in range(15)]
  p,q=trim(c[:5]),trim(c[5:])
  check(f'n{n}_{label}_full_original_polynomial_solution',op(p,q)==target and degree(p)<=4 and degree(q)<=9,{'projection_only':False,'target_u_degree':degree(f),'target_t_degree':degree(target)})
  sol.append({'name':label,'input15_P5_Q10':[str(x) for x in c]})
 instances.append({'n':n,'actual_even_t_matrix':[[str(x) for x in row] for row in matrix],'determinant':str(det),'solutions':sol})
check('index_split_nonmonomial_P_nonmonic_and_q_degree9',trim(list(range(1,16))[:5])==list(map(F,range(1,6))) and trim(list(range(1,16))[5:])==list(map(F,range(6,16))))
u,op0=genuine(0)
check('written_rational_n0_nonzero_q9_kernel',op0([],mon(9))==[])
# Reconstruct the clipped Nat source expression separately at n=0.
clipped=add(mul([-1,1],mul(power([1,1],10),comp(mon(9),[0,0,1]))),scale(mul([1,1],mul(power([-1,1],10),comp(mon(9),[0,1,1]))),-1))
check('native_Nat_clipped_n0_q9_is_not_written_kernel',clipped!=[])
dump(OUT/'exact-instance-checks.json',{'status':'EXACT_RATIONAL_FINITE_INSTANCE_CHECKS_NOT_UNIVERSAL_PROOF','source_sha256':SOURCE_HASH,'checks':checks,'instances':instances,
 'historical_symbolic39_universal_integer_polynomial_checks_separate':True,'Lean_executed_here':False})
print(str(len(checks))+' exact rational instance checks; three nonsingular 15x15 maps and 21 full original target solutions',flush=True)
