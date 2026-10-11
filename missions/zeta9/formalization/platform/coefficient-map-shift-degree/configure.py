"""Prepare a self-contained ShiftDegree batch from the frozen mechanical driver."""
from pathlib import Path
import hashlib,json
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[2]
SUM=TASK/'formalization/platform/coefficient-map-summation'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for line in (SUM/'SHA256SUMS.txt').read_text(encoding='utf-8').splitlines():
 h,p=line.split('  ',1);assert sha(SUM/p)==h
s=(SUM/'prepare_batch.py').read_text(encoding='utf-8')
a=s.index('BASE=TASK /');b=s.index('\n\ndef sha',a)
s=s[:a]+'''JET=TASK / "formalization/platform/coefficient-map-jet"
REV="0df444a360eaa60ab8c11dca51a86af692955474"
NS="ZetaNine.CoefficientMapShiftDegree"
EXPECTED={"CoefficientMapShiftDegree":"96efe64f218c07a9d941136af1b4a0874bca9627c01be262c53e4445e0876953"}
DEFS=["shiftA","shiftB","shiftDifference"]
TARGETS=["actual_shift_difference_coefficient","actual_shift_difference_degree_lower_bound","actual_shift_difference_small_degree_implies_zero"]
ARGS=["n H hH","n hn H hH hdeg","n hn H hdeg hsmall"]
MATHLIB=["Mathlib.Algebra.Polynomial.Taylor","Mathlib.Algebra.Polynomial.Reverse","Mathlib.Tactic"]
import argparse
ap=argparse.ArgumentParser();ap.add_argument("--prepare-only",action="store_true")
options=ap.parse_args()
'''+s[b:]
s=s.replace('CoefficientMapSummation','CoefficientMapShiftDegree')
a=s.index('math_review=');b=s.index('PROJECT.mkdir(',a)
s=s[:a]+'''math_review=TASK/"verification/formalization-coefficient-map-shift-degree-independent-2026-10-04/independent-review.json"
assert sha(math_review)=="d38de9f7991fedbd716bd2b1824cda09f979c1da91191bff43e8f0ea3922e5df"
math=json.loads(math_review.read_text(encoding="utf-8-sig"));assert math["verdict"]=="PASS" and len(math["checks"])==16 and len(math["stable_files"])==54
for row in math["stable_files"]:assert sha(ROOT/row["root_relative"])==row["sha256"]
author=TASK/"verification/formalization-coefficient-map-shift-degree-2026-10-04"
assert sha(author/"compile-receipt.json")=="93595416db563dd9cd8ffb5030455eed1edfe678b392ec64b1bd4930fdb7f853"
assert sha(author/"SHA256SUMS.txt")=="88f22efde6ad2e4552c878e55ca09f5247f9ab4ffa567c7d5edc91036808f4c5"
for line in (author/"SHA256SUMS.txt").read_text(encoding="utf-8").splitlines():
 h,path=line.split("  ",1);assert sha(ROOT/path)==h
'''+s[b:]
a=s.index('write(PROJECT / "lakefile.lean"');b=s.index('for name in ["lake-manifest.json"',a)
s=s[:a]+'''write(PROJECT / "lakefile.lean",f\'''import Lake
open Lake DSL
package zeta9ShiftDegreeOfflineAuthor
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "{REV}"
lean_lib Native where
  roots := #[`missions.zeta9.formalization.CoefficientMapShiftDegree]
  globs := #[.one `missions.zeta9.formalization.CoefficientMapShiftDegree]
lean_lib Definitions
lean_lib Solutions
lean_lib Theorems
\''')
'''+s[b:]
a=s.index('existing_defs=[]');b=s.index('\ng=(JET /',a)
s=s[:a]+'existing_defs=[]\n'+s[b:]
s='\n'.join(l for l in s.splitlines() if not l.startswith('g=g.replace("let isProj'))+'\n'
s=s.replace('list(EXPECTED)+[PURE_NAME]','list(EXPECTED)')
s=s.replace('("Definitions/"+name+".lean" if name==PURE_NAME else "missions/zeta9/formalization/"+name+".lean")','"missions/zeta9/formalization/"+name+".lean"')
a=s.index('if options.prepare_only:');b=s.index('\nrun("toolchain"',a)
s=s[:a]+'''if options.prepare_only:
 dump(OUT/"preparation-state.json",{"source_sha256":EXPECTED,"selected_actual_endpoints":TARGETS,"native_sources_copied":1,"new_genuine_Definitions":DEFS,"parent_Definitions":[],"external_proof_dependencies":[],"Lean_executed":False,"API_calls":False,"root_scope_writes":False})
 print("Mechanical preparation complete; no Lean executed.")
 sys.exit(0)
'''+s[b:]
s=s.replace('assert len(core)==24 and sum(g["kind"]=="def" for g in core)==3 and sum(g["kind"]=="theorem" for g in core)==21','assert len(core)==15 and sum(g["kind"]=="def" for g in core)==3 and sum(g["kind"]=="theorem" for g in core)==12')
a=s.index('bridge="";bridge_facts=');b=s.index('write(OUT / "actual-proof-bridge',a)
s=s[:a]+'bridge="";bridge_facts=[];helper_names=[];bridge_open_context=[]\nassert all(byname[n]["module"]=="missions.zeta9.formalization.CoefficientMapShiftDegree" for n in reached)\n'+s[b:]
a=s.index('definition="import Definitions.');b=s.index('\nfirst_def=',a)
s=s[:a]+'''definition="\\n".join("import "+m for m in MATHLIB[:-1])+"\\n\\nset_option autoImplicit false\\nnoncomputable section\\nnamespace "+NS+"\\n\\n"
'''+s[b:]
a=s.index('assert header["start"]');b=s.index('\nfs=facts[',a)
s=s[:a]+'assert header["start"]["offset"]==0 and source[:he].decode().strip().splitlines()==["import "+m for m in MATHLIB]\n'+s[b:]
a=s.index('preamble=');b=s.index('\ntargets=[];',a)
s=s[:a]+'''preamble="import Definitions.Def_ZetaNine_CoefficientMapShiftDegree\\n\\nset_option autoImplicit false\\nopen Polynomial\\nopen ZetaNine "+NS+"\\n"
solheader="import Definitions.Def_ZetaNine_CoefficientMapShiftDegree\\n"+"\\n".join("import "+m for m in MATHLIB)+"\\n\\n"
origin="Zeta(9) actual polynomial shift operator: missions/zeta9/research/coefficient-map-shift-degree-2026-10-04.md. Frozen source SHA256 "+EXPECTED["CoefficientMapShiftDegree"]+". The relationship to the rational telescoper is proved separately; it is not an input to these polynomial endpoints."
definition_nl=r"""For natural $n$, define actual rational polynomials $A_n=(X-(n+1))(X+n)^{10}$, $B_n=X^{10}(X+2n+1)$ and the actual linear shift difference $D_n(H)=A_nH-B_nH(X+1)$. These are three genuine polynomial definitions with no degree, kernel, rational-function or inverse premise."""
dump(OUT/"definitions-request.json",[{"definition_name":"ZetaNine_CoefficientMapShiftDegree","definition_title":"Actual rational polynomial shift difference operator","definition":definition,"natural_language_statement":definition_nl,"source":origin,"tags":["polynomials","number-theory","formalization"],"env":REV,"private":False}])
titles=["Exact next surviving coefficient of the actual polynomial shift difference","Actual shift difference degree lower bound in the nonresonant domain","A low-degree actual shift difference forces the input polynomial to vanish"]
naturals=[r"""For every natural $n$ and nonzero rational polynomial $H$ of natural degree $d$, the coefficient of $X^{d+10}$ in the actual $D_n(H)$ equals $(7n-2-d)\\operatorname{LC}(H)$. This identity needs only $H\\ne0$; no positivity, parity, degree-gap, monicity or preassigned operator relation is assumed. The degree-$d+11$ terms cancel in the actual polynomial calculation.""",r"""Let $n\\ge1$ and let nonzero $H\\in\\mathbb Q[X]$ satisfy $d=\\operatorname{natdeg}H\\le7n-3$. Then $d+10\\le\\operatorname{natdeg}D_n(H)$. The exact coefficient is proved nonzero from these original inequalities. No parity or monicity premise is added. The bound matters: $n=1,H=X^5$ lies outside it and has vanishing coefficient of $X^{15}$ although $D_1(X^5)(1)=-1152$.""",r"""Let $n\\ge1$ and $H\\in\\mathbb Q[X]$ satisfy $\\operatorname{natdeg}H\\le7n-3$ and $\\operatorname{natdeg}D_n(H)\\le8$. Then $H=0$. No nonzero-input premise or kernel equation is assumed: the original low operator degree and quotient degree bound yield a contradiction if $H\\ne0$. Zero input, constant input and the $n=1,X^5$ resonance are preserved by exact boundary checks. These polynomial facts do not by themselves state a rational telescoper relationship, coefficient-map inverse or zeta irrationality.""" ]
'''+s[b:]
s=s.replace('"source_defs":3,"source_proofs":21','"source_defs":3,"source_proofs":12').replace('"source_declarations":24,"actual_defs":3,"original_proofs":21','"source_declarations":15,"actual_defs":3,"original_proofs":12')
s=s.replace('assert len(all_defs)==43','assert len(all_defs)==3')
s=s.replace('all seven actual Lean source parser/ref oracles plus the actual pure Harmonic definition oracle','the actual self-contained Lean parser/ref oracle')
s=s.replace('["number-theory","polynomials","partial-fractions","formalization"]','["number-theory","polynomials","finite-differences","formalization"]')
s=s.replace('open ZetaNine '+ '"+NS+" ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapFiniteSum ZetaNine.HarmonicStability\\n','open ZetaNine "+NS+"\\n')
(OUT/'prepare_batch.py').write_text(s,encoding='utf-8',newline='\n')
compile(s,str(OUT/'prepare_batch.py'),'exec')
print('ShiftDegree standalone driver configured; no Lean executed.')
