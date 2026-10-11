"""Emit explicit constructor SOURCE; hygiene names are data, never quoted identifiers."""
import json, sys
import inspect_author as p

ENCODER=r'''import missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions
import Lean
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
open Lean Meta
private partial def encodeName : Name → String
  | .anonymous => "Lean.Name.anonymous"
  | .str parent part => "(Lean.Name.mkStr " ++ encodeName parent ++ " " ++ (Json.str part).compress ++ ")"
  | .num parent part => "(Lean.Name.mkNum " ++ encodeName parent ++ " " ++ toString part ++ ")"
private partial def encodeLevel : Level → MetaM String
  | .zero => pure "Lean.Level.zero"
  | .succ a => return "(Lean.Level.succ " ++ (← encodeLevel a) ++ ")"
  | .max a b => return "(Lean.Level.max " ++ (← encodeLevel a) ++ " " ++ (← encodeLevel b) ++ ")"
  | .imax a b => return "(Lean.Level.imax " ++ (← encodeLevel a) ++ " " ++ (← encodeLevel b) ++ ")"
  | .param name => pure ("(Lean.Level.param " ++ encodeName name ++ ")")
  | .mvar _ => throwError "Unclosed universe metavariable in selected Expr"
private def encodeBinder : BinderInfo → String
  | .default => "Lean.BinderInfo.default"
  | .implicit => "Lean.BinderInfo.implicit"
  | .strictImplicit => "Lean.BinderInfo.strictImplicit"
  | .instImplicit => "Lean.BinderInfo.instImplicit"
private partial def encodeExpr : Expr → MetaM String
  | .bvar index => pure ("(Lean.Expr.bvar " ++ toString index ++ ")")
  | .sort level => return "(Lean.Expr.sort " ++ (← encodeLevel level) ++ ")"
  | .const name levels => do
      let encoded ← levels.mapM encodeLevel
      return "(Lean.Expr.const " ++ encodeName name ++ " [" ++ String.intercalate ", " encoded ++ "])"
  | .app fn arg => return "(Lean.Expr.app " ++ (← encodeExpr fn) ++ " " ++ (← encodeExpr arg) ++ ")"
  | .lam name ty body bi => return "(Lean.Expr.lam " ++ encodeName name ++ " " ++ (← encodeExpr ty) ++ " " ++ (← encodeExpr body) ++ " " ++ encodeBinder bi ++ ")"
  | .forallE name ty body bi => return "(Lean.Expr.forallE " ++ encodeName name ++ " " ++ (← encodeExpr ty) ++ " " ++ (← encodeExpr body) ++ " " ++ encodeBinder bi ++ ")"
  | .letE name ty value body nondep => return "(Lean.Expr.letE " ++ encodeName name ++ " " ++ (← encodeExpr ty) ++ " " ++ (← encodeExpr value) ++ " " ++ (← encodeExpr body) ++ " " ++ (if nondep then "true" else "false") ++ ")"
  | .lit (.natVal value) => pure ("(Lean.Expr.lit (Lean.Literal.natVal " ++ toString value ++ "))")
  | .lit (.strVal value) => pure ("(Lean.Expr.lit (Lean.Literal.strVal " ++ (Json.str value).compress ++ "))")
  | .proj name index value => return "(Lean.Expr.proj " ++ encodeName name ++ " " ++ toString index ++ " " ++ (← encodeExpr value) ++ ")"
  | .mdata _ _ => throwError "Metadata needs a separate lossless encoding; selected Expr rejected"
  | .fvar _ => throwError "Unclosed free variable in selected Expr"
  | .mvar _ => throwError "Unclosed metavariable in selected Expr"
private def emitEncoded (name : Name) (definition : Bool) : MetaM Unit := do
  let info ← getConstInfo name
  let ty ← encodeExpr info.type
  let mut pairs := [("kind",Json.str "independent_lossless_constructor_SOURCE"),
    ("declaration",Json.str name.toString),("full_type_constructor_SOURCE",Json.str ty),
    ("full_type_raw_Expr",Json.str (reprStr info.type))]
  if definition then
    let .defnInfo actual := info | throwError "Expected selected definition"
    let val ← encodeExpr actual.value
    pairs := pairs ++ [("full_value_constructor_SOURCE",Json.str val),
      ("full_value_raw_Expr",Json.str (reprStr actual.value))]
  IO.println (Json.mkObj pairs).compress
run_meta do
'''

def main():
    sys.stdout.reconfigure(encoding='utf-8')
    selected=p.load(p.OUT/'own-native-graph-selection.json')
    source=ENCODER+''.join('  emitEncoded `'+n+' true\n' for n in selected['definitions'])
    source+=''.join('  emitEncoded `'+n+' false\n' for n in selected['proofs']+selected['generated'])
    path=p.PROJECT/'PFIndependentLosslessEncoderV1.lean'; assert not path.exists()
    path.write_text(source,encoding='utf-8'); (p.OUT/path.name).write_bytes(path.read_bytes())
    (p.OUT/'lossless-encoder-preparation.json').write_text(json.dumps(dict(source=p.bind(path),
        snapshot=p.bind(p.OUT/path.name),selection=p.bind(p.OUT/'own-native-graph-selection.json'),
        reason='reprStr quoted hygiene names are not valid SOURCE; explicit recursive Name constructors preserve all components',
        original_c047_whole_failure_preserved=True,Expr_roundtrip_not_yet_claimed=True),indent=2)+'\n',encoding='utf-8')

if __name__=='__main__':main()
