"""Configure this new offline author batch using the frozen PF recipe as code template."""
from pathlib import Path
import hashlib,json
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[2]
OLD=TASK / "formalization/platform/coefficient-map-partial-fractions"
original=(OLD / "prepare_batch.py").read_text(encoding="utf-8-sig")
s=original
def replace(a,b):
    global s
    assert a in s,a
    s=s.replace(a,b)
a=s.index('previous=json.loads');b=s.index('receipt={',a);s=s[:a]+s[b:]
a=s.index('    if label in previous_rows:');b=s.index('    p=subprocess.run',a);s=s[:a]+s[b:]
s=s.replace('receipt["retained_failed_attempt"]="retained-failed-attempt.json";receipt["resumed_same_project_successful_steps"]=list(previous_rows);','')
replace('CoefficientMapPartialFractions','CoefficientMapReflection')
replace('coefficient-map-partial-fractions','coefficient-map-reflection')
replace('zeta9PartialFractionsOfflineAuthor','zeta9ReflectionOfflineAuthor')
replace('INJ=TASK / "formalization/platform/coefficient-map-injectivity"','INJ=TASK / "formalization/platform/coefficient-map-injectivity"\nPF=TASK / "formalization/platform/coefficient-map-partial-fractions"')
a=s.index('EXPECTED=');b=s.index('\n\ndef sha',a)
s=s[:a]+'''EXPECTED={"CoefficientMap":"e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03","CoefficientMapJet":"e50e11c0afd2eaac1d5c58c412e5e59bc5c2068c9826063eacee8dc88fc1735a","CoefficientMapInjectivity":"ebe9b9c275a34fac348837e377e2e26246e9a762889c462420b43535e9055095","CoefficientMapPartialFractions":"eb0b8d54cd29ddaaa9404ee26a704bb6a47e8306741c49a6bba9b7232231f61a","CoefficientMapReflection":"8fbc53b9d9c33a61e1cf8208f89cd30dd3c6793fc32aad1cad1c51286747f707"}
DEFS=["reflectionVariable","rho","StrongProperMultiplier","partialBasis"]
TARGETS=["local_coefficient_reflection","rho_even_order_zero","rho_one_zero_of_strong_proper"]
ARGS=["n j s hn W hj hs1 hs9","n s hn W hs1 hs9 hs","n W hstrong"]
MATHLIB=[]
'''+s[b:]
replace('.one `missions.zeta9.formalization.CoefficientMapReflection]', '.one `missions.zeta9.formalization.CoefficientMapPartialFractions, .one `missions.zeta9.formalization.CoefficientMapReflection]')
replace('[(BASE,"CoefficientMap"),(JET,"CoefficientMapJet"),(INJ,"CoefficientMapInjectivity")]', '[(BASE,"CoefficientMap"),(JET,"CoefficientMapJet"),(INJ,"CoefficientMapInjectivity"),(PF,"CoefficientMapPartialFractions")]')
replace('    write(PROJECT / rel,(batch / "staged" / rel).read_bytes())', '''    assert sha(ROOT / rel)==sha(batch / "staged" / rel), "Installed actual Def differs from frozen stage."
    if name=="CoefficientMapPartialFractions":assert sha(ROOT / rel)=="74904aff5266f68b9d9f5c3013fb636f48d0cadda75e872093419845f9b666e5"
    write(PROJECT / rel,(batch / "staged" / rel).read_bytes())''')
replace('len(core)==32 and sum(g["kind"]=="def" for g in core)==5 and sum(g["kind"]=="theorem" for g in core)==27','len(core)==34 and sum(g["kind"]=="def" for g in core)==4 and sum(g["kind"]=="theorem" for g in core)==30')
replace('bridge="";bridge_facts=[];helper_names=[]','bridge="";bridge_facts=[];helper_names=[];bridge_open_context=[]')
replace('for module in ["CoefficientMap","CoefficientMapJet","CoefficientMapInjectivity"]:', 'for module in ["CoefficientMap","CoefficientMapJet","CoefficientMapInjectivity","CoefficientMapPartialFractions"]:')
replace('    for g in hs:\n', '''    first=min(g["startLine"] for g in graph if g["module"].endswith("."+module) and g["startLine"]>0)
    opens=[f for f in facts[module] if f["kind"]=="command" and f["syntaxKind"]=="Lean.Parser.Command.open" and f["span"]["end"]["line"]<first]
    # Exact parser-owned open spans restore each source's namespace resolution.
    for f in opens:
        bridge+=sources[module][f["span"]["start"]["offset"]:f["span"]["end"]["offset"]].decode()+"\\n"
        bridge_open_context.append({"module":module,"fact":f})
    if opens:bridge+="\\n"
    for g in hs:
''')
replace('import Definitions.Def_ZetaNine_CoefficientMapInjectivity\\n','import Definitions.Def_ZetaNine_CoefficientMapPartialFractions\\n')
replace('definition+="\\n\\n".join', '''first_def=min(f["declStart"]["offset"] for f in def_facts)
definition_open_context=[f for f in facts["CoefficientMapReflection"] if f["kind"]=="command" and f["syntaxKind"]=="Lean.Parser.Command.open" and f["span"]["end"]["offset"]<first_def]
definition+="\\n".join(source[f["span"]["start"]["offset"]:f["span"]["end"]["offset"]].decode() for f in definition_open_context)+"\\n\\n"
definition+="\\n\\n".join''')
replace('["import missions.zeta9.formalization.CoefficientMapInjectivity"]', '["import missions.zeta9.formalization.CoefficientMapPartialFractions"]')
replace('ZetaNine.CoefficientMapInjectivity\\n','ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions\\n')
replace('"source_defs":5,"source_proofs":27','"source_defs":4,"source_proofs":30')
replace('"bridge_sha256":digest(bridge.encode())', '"bridge_open_context_facts":bridge_open_context,"definition_open_context_facts":definition_open_context,"bridge_sha256":digest(bridge.encode())')
replace('assert len(all_defs)==30','assert len(all_defs)==34')
replace('all four actual Lean parser/ref oracles','all five actual Lean parser/ref oracles')
replace('"source_declarations":32,"actual_defs":5,"original_proofs":27','"source_declarations":34,"actual_defs":4,"original_proofs":30')
a=s.index('origin=');b=s.index('\ntargets=[];',a)
s=s[:a]+'''origin="Zeta(9) actual finite reflection and coefficient-total research: missions/zeta9/research/coefficient-map-reflection-2026-10-03.md. Frozen source missions/zeta9/formalization/CoefficientMapReflection.lean, SHA256 "+EXPECTED["CoefficientMapReflection"]+". This uses the actual finite product numerator/denominator, genuine weighted formal local coefficients and proved finite partial-fraction identity."
definition_nl=r"""For $n\\ge0$ and $W\\in\\mathbb Q[X]$, let $c^W_{n,j,s}$ be the actual local coefficient of the genuine shifted numerator/unit denominator quotient from the Base/Jet/Injectivity/PF definition chain. Define the reflection variable $V_n(X)=-X-n$ and the finite coefficient total $\\rho_{n,s}(W)=\\sum_{j=0}^{n}c^W_{n,j,s}$. Define

$$\\mathrm{StrongProper}(n,W)\\iff 2n+2\\operatorname{natdeg}W\\le9(n+1)-2.$$

Finally define the genuine partial basis $B_{n,j,s}=(\\prod_{0\\le k\\le n,\\ k\\ne j}(X+k))^9(X+j)^{9-s}$. These are four actual objects/conditions, not a reflection, cancellation or invertibility conclusion encoded as an assumption. StrongProper is stricter than the strict proper-degree condition."""
dump(OUT / "definitions-request.json",[{"definition_name":"ZetaNine_CoefficientMapReflection","definition_title":"Actual reflection variable, local coefficient totals and strong proper domain","definition":definition,"natural_language_statement":definition_nl,"source":origin,"tags":["number-theory","polynomials","formal-power-series","reflection"],"env":REV,"private":False}])
titles=["Actual local coefficient reflection at every pole for even n","Even-order actual local coefficient totals vanish for even n","The actual simple-pole total vanishes under the stronger degree bound"]
naturals=[r"""Let $n,j,s$ be natural numbers, assume $n$ is even, $j\\le n$, $1\\le s\\le9$, and take any $W\\in\\mathbb Q[X]$. The genuine local formal coefficients of the actual weighted rational function satisfy

$$c^W_{n,n-j,s}=(-1)^{s+1}c^W_{n,j,s}.$$

This follows from actual numerator/denominator reflection and the unit-denominator formal series identity, without properness, arbitrary coefficient data or a global coefficient-reflection hypothesis. The Even n condition is retained; no assertion for odd n is made.""",r"""Let $n,s$ be natural numbers with $n$ even, $s$ even and $1\\le s\\le9$, and take any $W\\in\\mathbb Q[X]$. The total of the actual local coefficients satisfies

$$\\rho_{n,s}(W)=\\sum_{j=0}^{n}c^W_{n,j,s}=0.$$

No properness premise is needed. This includes $s=2,4,6,8$ and $n=0$. For $n=0,W=X^4$ all four even-order totals vanish, but the actual simple-pole total is one; this theorem does not claim that it vanishes.""",r"""For any natural $n$ and $W\\in\\mathbb Q[X]$, assume the genuine stronger degree condition $2n+2\\operatorname{natdeg}W\\le9(n+1)-2$. Then the actual simple-pole coefficient total vanishes:

$$\\rho_{n,1}(W)=\\sum_{j=0}^{n}c^W_{n,j,1}=0.$$

This uses the actual finite global polynomial partial-fraction identity and its coefficient at degree $9n+8$. It does not require Even n: every rational quartic is StrongProper for $n\\ge1$, including $n=1$. Strict properness alone is insufficient: $n=0,W=X^4$ is proper but not StrongProper, with actual function $1/t$ and $\\rho_{0,1}=1$. No infinite L-sum, convergence or original five-dimensional aggregate F inverse follows from this finite theorem.""" ]
'''+s[b:]
(OUT / "prepare_batch.py").write_text(s,encoding="utf-8",newline="\n")
(OUT / "recipe-provenance.json").write_text(json.dumps({"configuration_template":(OLD / "prepare_batch.py").relative_to(TASK).as_posix(),"configuration_template_sha256":hashlib.sha256((OLD / "prepare_batch.py").read_bytes()).hexdigest(),"old_recipe_modified":False,"fresh_project":True,"changes":"Five actual source modules, four actual Def dependencies verified at installed root before copy, 4 genuine Reflection defs/30 proofs, 3 exact endpoints; source/parser spans exclusively from executed Lean oracles. Namespace open context copied from actual parser-owned command spans."},indent=2)+"\n",encoding="utf-8")
print("Configured new Reflection fresh offline author recipe.")
