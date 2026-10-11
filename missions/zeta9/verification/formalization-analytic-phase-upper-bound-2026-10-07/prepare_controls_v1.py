"""Prepare own native source-derived type, full-definition, kernel and boundary controls."""
import re,sys
sys.dont_write_bytecode=True
import prepare_native as p
from repair_base_v2 import prefixes

NS='ZetaNine.AnalyticPhase.'
IMPORT='''import missions.zeta9.formalization.AnalyticPhaseUpperBound
import Lean
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
noncomputable section
open Set
open ZetaNine.AnalyticPhase
open Lean Meta Elab Command
'''
EMITTER='''
private def apEmit (j : Json) : MetaM Unit := do
  liftIO <| IO.println ("AP_RECORD|" ++ j.compress)

private def apAxioms (n : Name) : MetaM Json := do
  let axs ← Lean.collectAxioms n
  for a in axs do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains a do
      throwError "Outside Std3: {n} -> {a}"
  return toJson (axs.map Name.toString)

private def apRecord (kind : String) (n : Name) : MetaM Unit := do
  let ci ← getConstInfo n
  let value := match ci.value? with
    | some e => Json.str (reprStr e)
    | none => Json.null
  apEmit <| Json.mkObj [("kind",toJson kind),("name",toJson n.toString),
    ("type_raw",toJson (reprStr ci.type)),("value_raw",value),
    ("levelParams",toJson (ci.levelParams.map Name.toString)),
    ("isProp",toJson (← isProp ci.type)),("axioms",← apAxioms n)]
'''

def quoted(names):return '#['+', '.join('``'+n for n in names)+']'

def args(prefix,name):
    tail=prefix[len('theorem '+name):];out=[];pos=0
    while True:
        while pos<len(tail) and tail[pos].isspace():pos+=1
        if tail[pos]==':':break
        opener=tail[pos];assert opener in '({'
        closer=')' if opener=='(' else '}';depth=1;end=pos+1
        while depth:
            if tail[end]==opener:depth+=1
            elif tail[end]==closer:depth-=1
            end+=1
        out+=tail[pos+1:end-1].split(':',1)[0].split();pos=end
    return ' '.join(out)

def main():
    sources=[(p.TASK/'formalization'/(n+'.lean')).read_text(encoding='utf-8-sig') for n in p.EXPECTED]
    theorem_prefixes={k:v for source in sources for k,v in prefixes(source).items()}
    assert len(theorem_prefixes)==34
    definitions={}
    for source in sources:
        for m in re.finditer(r'(?ms)^def (\w+)\b.*?(?=\n\n)',source):definitions[m.group(1)]=m.group(0)
    assert len(definitions)==7
    names=[NS+n for n in theorem_prefixes];defs=[NS+n for n in definitions]
    types=IMPORT+EMITTER+'''
run_cmd liftTermElabM do
  for n in '''+quoted(defs)+''' do apRecord "definition" n
  for n in '''+quoted(names)+''' do apRecord "theorem" n
  let env ← getEnv
  for i in [:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    if #[`missions.zeta9.formalization.AnalyticPhase,
          `missions.zeta9.formalization.AnalyticPhaseUpperBound].contains m then
      let data := env.header.moduleData[i]!
      apEmit <| Json.mkObj [("kind",toJson "module_inventory"),("module",toJson m.toString),
        ("constant_names",toJson (data.constNames.map Name.toString)),
        ("extra_names",toJson (data.extraConstNames.map Name.toString))]
      for n in data.constNames do apRecord "module_declaration" n
      for n in data.extraConstNames do
        if (env.find? n).isSome then apRecord "module_extra" n
'''
    kernel=IMPORT+EMITTER+'\nnamespace APOriginalDefs\n'
    for name,decl in definitions.items():
        head,body=decl.split(':=',1)
        for dep in definitions:body=re.sub(r'\b'+re.escape(dep)+r'\b',NS+dep,body)
        kernel+=head+':='+body+'\n\n'
    kernel+='end APOriginalDefs\n\n'
    for name in definitions:
        kernel+='theorem original_value_'+name+' : APOriginalDefs.'+name+' = '+NS+name+' := rfl\n'
    kernel+='\nnamespace APExpected\n'
    for name,prefix in theorem_prefixes.items():
        kernel+=prefix+' by\n  exact @'+NS+name+' '+args(prefix,name)+'\n\n'
    kernel+='''theorem exact_open_domain : ∀ x : ℝ, 1 < x →
    ZetaNine.AnalyticPhase.phase x ≤ (-2641 / 250 : ℝ) :=
  ZetaNine.AnalyticPhase.phase_global_upper_bound
end APExpected

private def apCompare (kind : String) (actual expected : Name) (requireValue : Bool) : MetaM Unit := do
  let a ← getConstInfo actual
  let b ← getConstInfo expected
  let typeEqual := Expr.equal a.type b.type
  let typeDefEq ← isDefEq a.type b.type
  unless typeDefEq do throwError "Type mismatch {actual} {expected}"
  let mut valueEqual := false
  let mut valueDefEq := false
  let mut va := Json.null
  let mut vb := Json.null
  if requireValue then
    let some av := a.value? | throwError "No actual definition value {actual}"
    let some bv := b.value? | throwError "No original definition value {expected}"
    valueEqual := Expr.equal av bv
    valueDefEq ← isDefEq av bv
    unless typeEqual && valueEqual && valueDefEq do
      throwError "Full definition mismatch {actual}"
    va := toJson (reprStr av)
    vb := toJson (reprStr bv)
  apEmit <| Json.mkObj [("kind",toJson kind),("actual",toJson actual.toString),
    ("expected",toJson expected.toString),("type_actual_raw",toJson (reprStr a.type)),
    ("type_expected_raw",toJson (reprStr b.type)),("type_exprEqual",toJson typeEqual),
    ("type_isDefEq",toJson typeDefEq),("value_actual_raw",va),("value_expected_raw",vb),
    ("value_exprEqual",toJson valueEqual),("value_isDefEq",toJson valueDefEq),
    ("actual_axioms",← apAxioms actual),("expected_axioms",← apAxioms expected)]

run_cmd liftTermElabM do
'''
    for name in definitions:
        kernel+='  apCompare "definition_compare" ``'+NS+name+' ``APOriginalDefs.'+name+' true\n'
        kernel+='  apRecord "definition_rfl" ``original_value_'+name+'\n'
    for name in theorem_prefixes:
        kernel+='  apCompare "theorem_compare" ``'+NS+name+' ``APExpected.'+name+' false\n'
    kernel+='  apCompare "exact_domain_compare" ``'+NS+'phase_global_upper_bound ``APExpected.exact_open_domain false\n'
    boundary=IMPORT+EMITTER+'''
namespace APBoundary
theorem phase_endpoint_one : phase 1 = 3 * Real.log 3 - 20 * Real.log 2 := phase_one_eq
theorem gap_endpoint_one : smoothPhaseGap 1 = 0 := smoothPhaseGap_one
theorem ratio_endpoint_one : smoothPhaseRatio 1 = (3 / 1024 : ℝ) := by norm_num [smoothPhaseRatio]
theorem slope_constant_exact : upperSlopeConstant =
    (33249125974877255751301 / 10763674952097696180200100 : ℝ) := upperSlopeConstant_eq
theorem slope_constant_small : 0 < upperSlopeConstant ∧ upperSlopeConstant < (1 / 100 : ℝ) := by
  constructor
  · exact upperSlopeConstant_pos
  · exact upperSlopeConstant_lt_rational.trans (by norm_num)
theorem universal_cap_attained : upperSlopeConstant *
    (1 + Real.log (upperSlopeConstant / upperSlopeConstant)) = upperSlopeConstant := by
  rw [div_self (ne_of_gt upperSlopeConstant_pos), Real.log_one]
  ring
theorem gap_endpoint_right : smoothPhaseGap (101 / 100) ≤ 0 := by
  exact smoothPhaseGap_le_zero (101 / 100) (by constructor <;> norm_num)
theorem phase_endpoint_right : phase (101 / 100) ≤ (-2641 / 250 : ℝ) :=
  phase_global_upper_bound (101 / 100) (by norm_num)
theorem phase_inside_left : phase (1003 / 1000) ≤ (-2641 / 250 : ℝ) :=
  phase_global_upper_bound (1003 / 1000) (by norm_num)
theorem phase_in_right : phase 2 ≤ (-2641 / 250 : ℝ) := phase_global_upper_bound 2 (by norm_num)
theorem phase_zero_exact : phase 0 = 2 * Real.log 2 := by norm_num [phase]
theorem phase_zero_exceeds_cap : (-2641 / 250 : ℝ) < phase 0 := by
  rw [phase_zero_exact]
  have h := log_two_lower_rational
  linarith
theorem excluded_endpoint_one : ¬ (1 : ℝ) < 1 := by norm_num
theorem excluded_zero : ¬ (1 : ℝ) < 0 := by norm_num
theorem global_stronger_margin : ∀ x : ℝ, 1 < x → phase x < (-10564011 / 1000000 : ℝ) :=
  phase_global_lt_certified
end APBoundary

run_cmd liftTermElabM do
'''
    boundary_names=re.findall(r'(?m)^theorem (\w+)',boundary)
    for name in boundary_names:boundary+='  apRecord "typed_boundary" ``APBoundary.'+name+'\n'
    for file,source in [('APTypes.lean',types),('APKernel.lean',kernel),('APBoundary.lean',boundary)]:
        p.write(p.PROJECT/file,source);p.write(p.OUT/'controls-v1'/file,source)
    p.dump(p.OUT/'controls-preparation-v1.json',dict(theorems=list(theorem_prefixes),definitions=list(definitions),
      typed_boundary_names=boundary_names,canonical_statement_source=[p.binding(p.TASK/'formalization'/(n+'.lean')) for n in p.EXPECTED],
      controls=[p.binding(p.PROJECT/n) for n in ['APTypes.lean','APKernel.lean','APBoundary.lean']],
      original_statement_prefixes_used_verbatim=True,original_definitions_values_reference_canonical_definitions=True,
      planned_actual_Expr_equal_and_isDefEq=True,compiled=False))
    print('Prepared exact-source-derived 34 theorem/7 full definition/15 boundary controls.',flush=True)
if __name__=='__main__':main()
