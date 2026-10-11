"""Retain raw helper-name differences; gate raw kernel equality and own full helper values."""
import sys
sys.dont_write_bytecode=True
import prepare_native as p

NORMALIZER='''
private def apProofHelpers (actual expected : Name) (av bv : Expr) : MetaM (Expr × Expr) := do
  let mut aa := av
  let mut bb := bv
  for _ in [:16] do
    let mut amap : Array (Name × Expr) := #[]
    let mut bmap : Array (Name × Expr) := #[]
    for n in aa.getUsedConstants do
      if n.getPrefix == actual && n.getString!.startsWith "_proof_" then
        let paired := Name.str expected n.getString!
        let a ← getConstInfo n
        let b ← getConstInfo paired
        unless (← isProp a.type) && (← isProp b.type) do
          throwError "Only proposition-valued compiler proof helpers can be expanded {n}"
        unless a.levelParams.isEmpty && b.levelParams.isEmpty do
          throwError "Unexpected helper universes {n}"
        let some va := a.value? true | throwError "Missing full helper proof value {n}"
        let some vb := b.value? true | throwError "Missing full helper proof value {paired}"
        let typeDefEq ← isDefEq a.type b.type
        let valueDefEq ← isDefEq va vb
        let actualValueTyped ← isDefEq (← inferType va) a.type
        let expectedValueTyped ← isDefEq (← inferType vb) b.type
        unless typeDefEq && valueDefEq && actualValueTyped && expectedValueTyped do
          throwError "Helper kernel mismatch {n} {paired}"
        apEmit <| Json.mkObj [("kind",toJson "definition_helper_compare"),
          ("actual",toJson n.toString),("expected",toJson paired.toString),
          ("type_actual_raw",toJson (reprStr a.type)),("type_expected_raw",toJson (reprStr b.type)),
          ("value_actual_raw",toJson (reprStr va)),("value_expected_raw",toJson (reprStr vb)),
          ("type_exprEqual",toJson (Expr.equal a.type b.type)),("value_exprEqual",toJson (Expr.equal va vb)),
          ("type_isDefEq",toJson typeDefEq),("value_isDefEq",toJson valueDefEq),
          ("actual_value_typed",toJson actualValueTyped),("expected_value_typed",toJson expectedValueTyped),
          ("actual_axioms",← apAxioms n),("expected_axioms",← apAxioms paired)]
        amap := amap.push (n,va)
        bmap := bmap.push (paired,vb)
    if amap.isEmpty then return (aa,bb)
    aa := aa.replace fun e => match e with
      | .const n [] => (amap.find? fun x => x.1 == n).map Prod.snd
      | _ => none
    bb := bb.replace fun e => match e with
      | .const n [] => (bmap.find? fun x => x.1 == n).map Prod.snd
      | _ => none
  throwError "Helper expansion did not terminate within the fixed bound"
'''

COMPARE='''private def apCompare (kind : String) (actual expected : Name) (requireValue : Bool) : MetaM Unit := do
  let a ← getConstInfo actual
  let b ← getConstInfo expected
  let typeEqual := Expr.equal a.type b.type
  let typeDefEq ← isDefEq a.type b.type
  unless typeDefEq do throwError "Type mismatch {actual} {expected}"
  let mut valueEqual := false
  let mut valueDefEq := false
  let mut normalizedEqual := false
  let mut normalizedDefEq := false
  let mut va := Json.null
  let mut vb := Json.null
  let mut normalizedA := Json.null
  let mut normalizedB := Json.null
  if requireValue then
    let some av := a.value? | throwError "No actual definition value {actual}"
    let some bv := b.value? | throwError "No original definition value {expected}"
    valueEqual := Expr.equal av bv
    valueDefEq ← isDefEq av bv
    va := toJson (reprStr av)
    vb := toJson (reprStr bv)
    let (na,nb) ← apProofHelpers actual expected av bv
    normalizedEqual := Expr.equal na nb
    normalizedDefEq ← isDefEq na nb
    normalizedA := toJson (reprStr na)
    normalizedB := toJson (reprStr nb)
  apEmit <| Json.mkObj [("kind",toJson kind),("actual",toJson actual.toString),
    ("expected",toJson expected.toString),("type_actual_raw",toJson (reprStr a.type)),
    ("type_expected_raw",toJson (reprStr b.type)),("type_exprEqual",toJson typeEqual),
    ("type_isDefEq",toJson typeDefEq),("value_actual_raw",va),("value_expected_raw",vb),
    ("value_exprEqual",toJson valueEqual),("value_isDefEq",toJson valueDefEq),
    ("normalized_value_actual_raw",normalizedA),("normalized_value_expected_raw",normalizedB),
    ("normalized_value_exprEqual",toJson normalizedEqual),("normalized_value_isDefEq",toJson normalizedDefEq),
    ("normalization",toJson "Only unfold all paired proposition-valued own compiler _proof_ helpers; no binder or metadata erasure"),
    ("actual_axioms",← apAxioms actual),("expected_axioms",← apAxioms expected)]
  if requireValue then
    unless valueDefEq && normalizedDefEq do throwError "Full definition kernel mismatch {actual}"
'''

def main():
    original=(p.OUT/'controls-v2/APKernel.lean').read_text(encoding='utf-8')
    start=original.index('private def apCompare');end=original.index('\nrun_cmd liftTermElabM do',start)
    source=original[:start]+NORMALIZER+'\n'+COMPARE+original[end:]
    p.write(p.OUT/'controls-v3/APKernel.lean',source);p.write(p.PROJECT/'APKernel.lean',source)
    p.dump(p.OUT/'controls-kernel-v3-repair.json',dict(reason='Own compiler proof helper names differ between canonical definitions and source-derived aliases',
      raw_false_not_changed_or_hidden=True,raw_full_values_retained=True,all_related_full_helper_types_values_Std3_checked=True,
      required_raw_full_type_isDefEq=True,required_raw_full_value_isDefEq=True,all7_actual_whole_function_rfl=True,
      normalization='Transparent expansion of paired own proposition-valued compiler helpers only',
      no_binder_or_metadata_erasure=True,canonical_sources_unchanged=True,
      failed_attempt_retained='actual-runs/control-kernel-v2-01',control=p.binding(p.PROJECT/'APKernel.lean')))
    print('Kernel V3 retains raw values and checks all paired own proof helpers.',flush=True)
if __name__=='__main__':main()
