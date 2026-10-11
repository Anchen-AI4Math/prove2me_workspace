"""Configure a new FS author batch from the immutable oracle-driven Reflection recipe."""
from pathlib import Path
import hashlib,json
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[2]
OLD=TASK/'formalization/platform/coefficient-map-reflection'
template=OLD/'prepare_batch.py'
s=template.read_text(encoding='utf-8-sig')
def replace(a,b):
 global s
 assert a in s,a
 s=s.replace(a,b)
replace('CoefficientMapReflection','CoefficientMapFiniteSum')
replace('coefficient-map-reflection','coefficient-map-finite-sum')
replace('zeta9ReflectionOfflineAuthor','zeta9FiniteSumOfflineAuthor')
a=s.index('EXPECTED=');b=s.index('\ndef sha',a)
s=s[:a]+'''EXPECTED={"CoefficientMap":"e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03","CoefficientMapJet":"e50e11c0afd2eaac1d5c58c412e5e59bc5c2068c9826063eacee8dc88fc1735a","CoefficientMapInjectivity":"ebe9b9c275a34fac348837e377e2e26246e9a762889c462420b43535e9055095","CoefficientMapPartialFractions":"eb0b8d54cd29ddaaa9404ee26a704bb6a47e8306741c49a6bba9b7232231f61a","CoefficientMapFiniteSum":"b3ede123541d6c0eb306915d93f743979b1090c34bc4df332ab6e9da07033f97"}
DEFS=["rho","constantTerm","finiteL","shiftedTail"]
TARGETS=["actual_finite_harmonic_identity","actual_grouped_finite_identity","harmonic_difference_eq_shifted"]
ARGS=["n T W hproper","n T W hproper","s T j"]
MATHLIB=["Mathlib.Algebra.BigOperators.Intervals"]
HARMONIC_SHA="5ff9d83ca177893db1eb149da985ff29b85dbe83614650a995e28066f9bd3e92"

'''+s[b:]
replace('env=os.environ.copy();env.pop("LEAN_PATH",None)','env=os.environ.copy();env.pop("LEAN_PATH",None);env["LEAN_NUM_THREADS"]="1"')
key='g=(JET / "extract_decl_graph.lean").read_text(encoding="utf-8-sig")'
replace(key,'''hrel="Definitions/Def_ZetaNine_HarmonicStability.lean"
assert sha(ROOT / hrel)==HARMONIC_SHA
write(PROJECT / hrel,(ROOT / hrel).read_bytes())
write(OUT / "dependencies" / hrel,(ROOT / hrel).read_bytes())
existing_defs.append({"root_relative":hrel,"sha256":HARMONIC_SHA,"task_relative":(OUT / "dependencies" / hrel).relative_to(TASK).as_posix()})

'''+key)
key='write(OUT / "extract_decl_graph.lean",g);write(PROJECT / "extract_decl_graph.lean",g)'
replace(key,'''assert g.count("fun m => projPrefix.isPrefixOf m")==1
g=g.replace("fun m => projPrefix.isPrefixOf m","fun m => projPrefix.isPrefixOf m || m == `Definitions.Def_ZetaNine_HarmonicStability")
'''+key)
key='write(OUT / "extract_header.lean",(JET / "extract_header.lean").read_bytes());'
replace(key,'''hcode=s.replace(old,"../HarmonicStability-oracle-input.lean")
write(OUT / "extract_HarmonicStability_sketch.lean",hcode);write(PROJECT / "extract_HarmonicStability_sketch.lean",hcode)
'''+key)
replace('run("build-native",["lake","--no-cache","build","missions.zeta9.formalization.CoefficientMapFiniteSum"])',
 '''run("build-native-HarmonicStability",["lake","--no-cache","build","Definitions.Def_ZetaNine_HarmonicStability"])
for module in EXPECTED:
    run("build-native-"+module,["lake","--no-cache","build","missions.zeta9.formalization."+module])''')
key='run("stage2-header",["lake","env","lean","--run","extract_header.lean","missions/zeta9/formalization/CoefficientMapFiniteSum.lean"],"header_info.jsonl")'
replace(key,'''run("stage2-HarmonicStability",["lake","env","lean","--run","extract_HarmonicStability_sketch.lean","Definitions/Def_ZetaNine_HarmonicStability.lean","ZetaNine"],"HarmonicStability-sketch_info.jsonl")
'''+key)
key='assert not any(g["kind"]=="axiom" for g in graph)'
replace(key,'''harmonic_source=(OUT / "HarmonicStability-oracle-input.lean").read_bytes()
assert harmonic_source==(ROOT / hrel).read_bytes() and digest(harmonic_source)==HARMONIC_SHA
harmonic_facts=rows(OUT / "HarmonicStability-sketch_info.jsonl")
assert len([f for f in harmonic_facts if f["kind"]=="decl"])==2
'''+key)
replace('len(core)==34 and sum(g["kind"]=="def" for g in core)==4 and sum(g["kind"]=="theorem" for g in core)==30',
 'len(core)==11 and sum(g["kind"]=="def" for g in core)==4 and sum(g["kind"]=="theorem" for g in core)==7')
replace('import Definitions.Def_ZetaNine_CoefficientMapPartialFractions\\n','import Definitions.Def_ZetaNine_CoefficientMapPartialFractions\\nimport Definitions.Def_ZetaNine_HarmonicStability\\n')
replace('["import missions.zeta9.formalization.CoefficientMapPartialFractions"]+["import "+m for m in MATHLIB]',
 '["import missions.zeta9.formalization.CoefficientMapPartialFractions","import Definitions.Def_ZetaNine_HarmonicStability"]+["import "+m for m in MATHLIB]')
replace('ZetaNine.CoefficientMapPartialFractions\\n','ZetaNine.CoefficientMapPartialFractions ZetaNine.HarmonicStability\\n')
replace('"source_defs":4,"source_proofs":30','"source_defs":4,"source_proofs":7')
replace('len(all_defs)==34','len(all_defs)==36')
replace('"source_declarations":34,"actual_defs":4,"original_proofs":30','"source_declarations":11,"actual_defs":4,"original_proofs":7')
replace('all five actual Lean parser/ref oracles','all five actual source parser/ref oracles plus the actual pure HarmonicStability Definition parser')
key='"sources_sha256":EXPECTED,"actual_source_position_authority"'
replace(key,'"sources_sha256":EXPECTED,"pure_HarmonicStability_sha256":HARMONIC_SHA,"pure_HarmonicStability_parser_decl_count":2,"actual_source_position_authority"')
a=s.index('origin=');b=s.index('\ntargets=[];',a)
s=s[:a]+r'''origin="Zeta(9) actual finite harmonic summation: missions/zeta9/research/coefficient-map-finite-sum-2026-10-03.md. Frozen missions/zeta9/formalization/CoefficientMapFiniteSum.lean SHA256 "+EXPECTED["CoefficientMapFiniteSum"]+". Coefficients are the actual weighted formal local jets of the p=9,q=1,m=n rational function, using the genuine finite global partial-fraction identity."
definition_nl=r"""For $n,T\ge0$ and $W\in\mathbb Q[X]$, use the actual coefficients $c^W_{n,j,s}$ of the genuine local series and the existing finite harmonic number $H_N^{(s)}=\sum_{k=1}^N k^{-s}$, also for $s=0$. Define

$$\rho_{n,s}(W)=\sum_{j=0}^n c^W_{n,j,s},\qquad B_n(W)=-\sum_{j=0}^n\sum_{s=1}^9 c^W_{n,j,s}H_j^{(s)}.$$

Define the actual finite rational sum $L_{n,T}(W)=\sum_{t=1}^T R_{n,W}(t)$ and the finite shifted tail

$$E_{n,T}(W)=\sum_{j=0}^n\sum_{s=1}^9c^W_{n,j,s}(H_{T+j}^{(s)}-H_T^{(s)}).$$

These are four genuine finite definitions. No coefficient cancellation, infinite sum, reflection or convergence is encoded as a premise. The existing harmonicPower definition is unchanged."""
dump(OUT / "definitions-request.json",[{"definition_name":"ZetaNine_CoefficientMapFiniteSum","definition_title":"Actual finite weighted rational sum, coefficient totals and harmonic tail","definition":definition,"natural_language_statement":definition_nl,"source":origin,"tags":["number-theory","finite-sums","harmonic-numbers","polynomials"],"env":REV,"private":False}])
titles=["Actual finite rational sum as a shifted harmonic double sum","Actual finite rational sum with all nine harmonic terms retained","Exact finite shifted harmonic difference for every natural order"]
naturals=[r"""Let $n,T$ be natural numbers and $W\in\mathbb Q[X]$. Assume the actual strict proper-degree condition $2n+2\operatorname{natdeg}W<9(n+1)$. Then

$$L_{n,T}(W)=\sum_{j=0}^n\sum_{s=1}^9c^W_{n,j,s}(H_{T+j}^{(s)}-H_j^{(s)}).$$

Every $c^W_{n,j,s}$ is extracted from the actual weighted local formal series. The genuine global rational partial fractions apply at every positive integer $t$, whose denominators $t+j$ are nonzero; only finite sums are exchanged. This includes $T=0$ and does not assume arbitrary coefficients, reflection, an infinite sum or convergence.""",r"""For natural $n,T$ and $W\in\mathbb Q[X]$, under the same actual strict proper condition $2n+2\operatorname{natdeg}W<9(n+1)$, the genuine finite sum satisfies

$$L_{n,T}(W)=B_n(W)+\sum_{s=1}^9\rho_{n,s}(W)H_T^{(s)}+E_{n,T}(W).$$

The simple-pole term $\rho_{n,1}(W)H_T^{(1)}$ is retained. No cancellation premise is introduced. For $n=0,W=X^4$, strict properness holds, $\rho_{0,1}=1$, $B_0=E_{0,T}=0$, and the actual finite sum is $H_T^{(1)}$. Therefore strict properness alone does not imply simple-pole cancellation or infinite L convergence. The separately conditional odd/no-simple wrappers are not submitted as public endpoints.""",r"""For every natural order $s$, cutoff $T$ and shift $j$, the existing actual finite harmonic numbers obey

$$H_{T+j}^{(s)}-H_T^{(s)}=\sum_{k=1}^j\frac1{(T+k)^s}.$$

There is no restriction $s\ge1$: this includes $s=0$, as well as $T=0$ and $j=0$. Empty finite intervals give zero and all terms use the existing rational harmonicPower definition. No properness, coefficient, reflection or convergence hypothesis is required.""" ]
'''+s[b:]
(OUT/'prepare_batch.py').write_text(s,encoding='utf-8',newline='\n')
(OUT/'recipe-provenance.json').write_text(json.dumps({'template_task_relative':template.relative_to(TASK).as_posix(),
 'template_sha256':hashlib.sha256(template.read_bytes()).hexdigest(),'old_recipe_modified':False,
 'fresh_project':True,'changes':'Five actual native sources plus the unchanged pure HarmonicStability Def; Stage1 module predicate explicitly includes that Def; six actual parser snapshots/header. Four source defs and seven full source proofs retained. Three finite endpoints keep rho1; sequential native/module builds.'},indent=2)+'\n',encoding='utf-8')
print('Configured new finite-sum author batch; no Lean started by configuration.')
