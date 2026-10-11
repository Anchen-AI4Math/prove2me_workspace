from pathlib import Path
import json,sys
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[2];TEL=TASK/'formalization/platform/coefficient-map-telescoper'
plan=json.loads((OUT/'preparation-state.json').read_text(encoding='utf-8-sig'))
s=(TEL/'prepare_batch.py').read_text(encoding='utf-8-sig')
start=s.index('assert not BUILD.exists()');tail=s[start:]
for a,b in [('CoefficientMapTelescoper','CoefficientMapKernelBridge'),('native_sources_copied":9','native_sources_copied":11'),('len(core)==31','len(core)==30'),('g["kind"]=="def" for g in core)==6','g["kind"]=="def" for g in core)==7'),('g["kind"]=="theorem" for g in core)==25','g["kind"]=="theorem" for g in core)==23'),('len(all_defs)==55','len(all_defs)==65'),('"source_defs":6','"source_defs":7'),('"source_proofs":25','"source_proofs":23'),('"source_declarations":31','"source_declarations":30'),('"actual_defs":6','"actual_defs":7'),('"original_proofs":25','"original_proofs":23'),('all nine actual native','all eleven actual native')]:tail=tail.replace(a,b)
tail=tail.replace('"CoefficientMapSummation","CoefficientMapAggregate"]:', '"CoefficientMapSummation","CoefficientMapAggregate","CoefficientMapTelescoper","CoefficientMapShiftDegree"]:')
a=tail.index('definition="import Definitions.');b=tail.index('header=rows(',a)
tail=tail[:a]+'''subprocess.run([sys.executable,str(OUT/"generate_closed_equiv_field.py")],check=True)
definition=(OUT/"staged"/defpath).read_text(encoding="utf-8-sig")
field_provenance=json.loads((OUT/"embedded-bijection-provenance.json").read_text(encoding="utf-8-sig"))
definition_open_context=[]
'''+tail[b:]
a=tail.index('assert header["start"]');b=tail.index('\n\nfs=',a)
tail=tail[:a]+'''assert header["start"]["offset"]==0 and source[:he].decode().strip().splitlines()==["import missions.zeta9.formalization.CoefficientMapTelescoper","import missions.zeta9.formalization.CoefficientMapShiftDegree","import Mathlib.Order.Interval.Set.Infinite"]'''+tail[b:]
a=tail.index('origin=');b=tail.index('\ntargets=[];',a)
tail=tail[:a]+'''origin="Zeta(9) actual original five-dimensional coefficient map kernel and rational inverse: missions/zeta9/research/coefficient-map-kernel-2026-10-04.md. Frozen source SHA256 "+EXPECTED["CoefficientMapKernelBridge"]+". The actual kernel, polynomial relation, bijection, inverse and sum are derived from genuine data and source proofs."
definition_nl="Define the original positive/negative products and shift factors, the actual five-dimensional rational quartic aggregate equivalence, its actual inverse multiplier and prescribed real linear form. The equivalence constructor's bijective proof is closed from the genuine source proof closure, without an added kernel/bijection/inverse premise. All seven actual data functions and original Even n, n>=2 domain remain fixed. No integer inverse, denominator height, small linear form or irrationality claim is made."
dump(OUT/"definitions-request.json",[{"definition_name":"ZetaNine_CoefficientMapKernelBridge","definition_title":"Actual rational quartic aggregate equivalence and inverse multiplier","definition":definition,"natural_language_statement":definition_nl,"source":origin,"tags":["number-theory","polynomials","linear-algebra","formalization"],"env":REV,"private":False}])
titles=["The actual quartic coefficient map has trivial kernel","The actual five-dimensional rational coefficient map is bijective","The actual inverse multiplier has its prescribed sum and absolute convergence"]
naturals=["Let n>=2 be even and W be a rational polynomial of natural degree at most4. If its genuine aggregate F_n(W) is zero, then W is zero. The true rational telescoper, infinitely many positive regular evaluation points, polynomial identity and shift-degree obstruction are proved internally; none is an extra premise.","For each even n>=2 the original five-dimensional rational aggregate map on quartic coordinates is bijective. Injectivity follows from the actual quartic kernel result, then finite dimensionality gives surjectivity. No determinant, rank, bijection or inverse assumption is added.","For each even n>=2 and b:Fin5->Rat, the actual inverse rational quartic multiplier produces a HasSum of the actual weightedR at positive integers with value prescribedL(b), and its absolute norms are Summable. The input b contains the rational constant and zeta3,5,7,9 coefficients. This is the original genuine HasSum, not a totalized tsum identity. Integer inverse coefficients, height bounds and irrationality remain unproved here."]
'''+tail[b:]
tail=tail.replace('"new_external_theorem_boundaries":[]','"embedded_bijection_provenance_sha256":sha(OUT/"embedded-bijection-provenance.json"),"new_external_theorem_boundaries":[]')
utilities=s[s.index('def sha(p)'):s.index('math_review=')]
head='''"""KernelBridge actual offline author; one serial Lean lane only."""
from pathlib import Path
import hashlib,json,os,subprocess,sys
sys.stdout.reconfigure(encoding="utf-8")
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[2];ROOT=TASK.parents[1];PROJECT=OUT/"p";BUILD=TASK/".rt/k1/b"
JET=TASK/"formalization/platform/coefficient-map-jet"
REV="0df444a360eaa60ab8c11dca51a86af692955474";NS="ZetaNine.CoefficientMapKernelBridge"
subprocess.run([sys.executable,str(OUT/"prepare_plan.py")],check=True)
plan=json.loads((OUT/"preparation-state.json").read_text(encoding="utf-8-sig"))
EXPECTED=plan["sources_sha256"];DEFS=plan["new_actual_definitions"]
TARGETS=[r["name"].split(".")[-1] for r in plan["selected_actual_endpoints"]];ARGS=[r["arguments"] for r in plan["selected_actual_endpoints"]]
PURE_NAME="Def_ZetaNine_HarmonicStability"
CONTROL_MODULES=[r["module"] for r in plan["native_controls"]]
control_bindings=[dict(r,task_relative=r["source_task_relative"]) for r in plan["native_controls"]]
existing_defs=plan["required_parent_definitions"]
(PROJECT/".lake").mkdir(exist_ok=True)
if not (PROJECT/".lake/packages").exists():
 p=subprocess.run(["cmd","/c","mklink","/J",str(PROJECT/".lake/packages"),str(ROOT/".lake/packages")],capture_output=True)
 assert p.returncode==0,(p.stdout+p.stderr).decode(errors="replace")
'''
(OUT/'prepare_batch.py').write_text(head+utilities+tail,encoding='utf-8',newline='\n')
for name in ['prepare_data_equivalence.py','prepare_boundaries.py']:
 t=(TEL/name).read_text(encoding='utf-8-sig').replace("TASK/'.rt/t1/b'","TASK/'.rt/k1/b'")
 if name=='prepare_boundaries.py':
  t=t.replace('coefficient-map-telescoper-independent','coefficient-map-kernel-bridge-independent').replace('coefficient-map-telescoper-2026','coefficient-map-kernel-2026').replace('CoefficientMapTelescoper','CoefficientMapKernelBridge').replace('actual_polynomial_quotient_degree_bound','inverseMultiplier_actual_HasSum_and_absolute').replace('cac46e0ea0674bcd4b2dca543326ab2d9bdd3cd8a409cba8988bfea0130a556a','7a325b3866719750c31e66469399ab85f7c73d8c5c1376356ee1951b320d78b1').replace('lean\',35)','lean\',37)').replace('lean\',54)','lean\',56)').replace('records\':89','records\':93').replace('selected quotient-degree theorem','selected actual inverse HasSum theorem').replace('35 native author and 54 independent','37 native author and56 independent')
 (OUT/name).write_text(t,encoding='utf-8',newline='\n')
compile((OUT/'prepare_batch.py').read_text(encoding='utf-8'),str(OUT/'prepare_batch.py'),'exec')
print('KernelBridge master and independent-boundary replay generated; no Lean execution.')