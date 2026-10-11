import Lean
import OAI.NumberTheory.PiExponent.Approximation.Sigma

open Lean Meta

namespace PiExponentInterfaceSnapshot

partial def levelJson : Level → Json
  | .zero => Json.arr #[toJson "zero"]
  | .succ u => Json.arr #[toJson "succ", levelJson u]
  | .max u v => Json.arr #[toJson "max", levelJson u, levelJson v]
  | .imax u v => Json.arr #[toJson "imax", levelJson u, levelJson v]
  | .param n => Json.arr #[toJson "param", toJson n.toString]
  | .mvar n => Json.arr #[toJson "mvar", toJson n.name.toString]

def binderTag : BinderInfo → String
  | .default => "explicit"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instance"

-- Keep binder information, constant names, universe levels and de Bruijn
-- indices. Binder display names and source metadata have no kernel meaning.
partial def exprJson : Expr → Json
  | .bvar i => Json.arr #[toJson "bvar", toJson i]
  | .fvar n => Json.arr #[toJson "fvar", toJson n.name.toString]
  | .mvar n => Json.arr #[toJson "mvar", toJson n.name.toString]
  | .sort u => Json.arr #[toJson "sort", levelJson u]
  | .const n us => Json.arr #[toJson "const", toJson n.toString,
      Json.arr (us.map levelJson).toArray]
  | .app f a => Json.arr #[toJson "app", exprJson f, exprJson a]
  | .lam _ t b bi => Json.arr #[toJson "lambda", toJson (binderTag bi), exprJson t, exprJson b]
  | .forallE _ t b bi => Json.arr #[toJson "forall", toJson (binderTag bi), exprJson t, exprJson b]
  | .letE _ t v b nondep => Json.arr #[toJson "let", exprJson t, exprJson v, exprJson b, toJson nondep]
  | .lit (.natVal n) => Json.arr #[toJson "natLiteral", toJson n]
  | .lit (.strVal s) => Json.arr #[toJson "stringLiteral", toJson s]
  | .mdata _ e => exprJson e
  | .proj n i e => Json.arr #[toJson "projection", toJson n.toString, toJson i, exprJson e]

def exportSnapshot (names : Array Name) (output : String) : MetaM Unit := do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for name in names do
    let some ci := env.find? name | throwError "Missing interface declaration: {name}"
    if ci.type.hasMVar || ci.type.hasFVar then
      throwError "The exported declaration type is not closed: {name}"
    let value := match ci with
      | .defnInfo d => some d.value
      | .thmInfo _ => none
      | _ => none
    let typeText ← ppExpr ci.type
    rows := rows.push <| Json.mkObj [
      ("name", toJson name.toString),
      ("levelParams", toJson (ci.levelParams.map Name.toString)),
      ("type", exprJson ci.type),
      ("value", value.map exprJson |>.getD Json.null),
      ("prettyType", toJson typeText.pretty)]
  IO.FS.writeFile output (Json.arr rows |>.compress)

end PiExponentInterfaceSnapshot

namespace ParameterSourceSnapshot
open Lean Meta
def refs (value : Expr) : Array String :=
  (value.getUsedConstants.map Name.toString).qsort (fun a b => a < b)
def exportSource (name : Name) (expectedModule output : String) : MetaM Unit := do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? name | throwError "source theorem is not imported"
  let some owner := env.header.moduleNames[idx.toNat]? | throwError "invalid module index"
  unless owner.toString == expectedModule do throwError "source theorem has wrong actual owner"
  let some ci := env.find? name | throwError "missing source theorem"
  let value ← match ci with | .thmInfo t => pure t.value | _ => throwError "source is not theorem CI"
  if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars || value.hasMVar || value.hasFVar || value.hasLooseBVars then throwError "source theorem CI is not closed"
  let axioms ← collectAxioms name
  unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do throwError "source theorem uses non-Std3 axiom"
  let row := Json.mkObj [("name", toJson name.toString), ("kind", toJson "theorem"), ("levelParams", toJson (ci.levelParams.map Name.toString)),
    ("closedType", toJson true), ("closedValue", toJson true), ("typeRefs", toJson (refs ci.type)),
    ("valueRefs", toJson (refs value)), ("axioms", toJson (axioms.map Name.toString)),
    ("owner", Json.mkObj [("kind", toJson "ImportedModule"), ("module", toJson owner.toString), ("index", toJson idx.toNat)])]
  IO.FS.writeFile output ((Json.mkObj [("schemaVersion", toJson 1), ("probeMainModule", toJson env.mainModule.toString), ("rows", Json.arr #[row])]).pretty)
end ParameterSourceSnapshot

set_option pp.universes true
set_option pp.fullNames true
set_option pp.explicit true
run_meta do
  PiExponentInterfaceSnapshot.exportSnapshot #[`OAI.PiExponent.exists_small_rational_sigma] "D:/users/self_projects/prove2me_workspace/missions/pi-irrationality-measure/verification/ap4/c3/source-type.json"
run_meta do
  ParameterSourceSnapshot.exportSource `OAI.PiExponent.exists_small_rational_sigma "OAI.NumberTheory.PiExponent.Approximation.Sigma" "D:/users/self_projects/prove2me_workspace/missions/pi-irrationality-measure/verification/ap4/c3/source-proof-references.json"
#print axioms OAI.PiExponent.exists_small_rational_sigma
