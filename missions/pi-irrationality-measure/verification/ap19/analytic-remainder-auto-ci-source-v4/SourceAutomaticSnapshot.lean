import Lean
import OAI.NumberTheory.PiExponent.Analysis.CollisionExponential

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

namespace AnalyticRemainderSourceAutomaticProbe
open Lean Meta
def exportAutomaticCIs (names : Array Name) (owner output : String) : MetaM Unit := do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for name in names do
    let some ci := env.find? name | throwError "Missing genuine source automatic CI: {name}"
    let .thmInfo thm := ci | throwError "Expected original source theorem CI: {name}"
    let actualOwner ← match env.getModuleIdxFor? name with
      | none => pure env.mainModule.toString
      | some idx => do
        let some m := env.header.moduleNames[idx.toNat]? | throwError "Invalid source auto-CI owner"
        pure m.toString
    unless actualOwner == owner do throwError "Original automatic CI owner differs: {name}"
    unless ← isProp ci.type do throwError "Source automatic CI is not Prop: {name}"
    if ci.type.hasMVar || ci.type.hasFVar || thm.value.hasMVar || thm.value.hasFVar then
      throwError "Unclosed original automatic CI: {name}"
    let ax := ((← Lean.collectAxioms name).map Name.toString).qsort (· < ·)
    rows := rows.push <| Json.mkObj [
      ("name", toJson name.toString), ("actualOwner", toJson actualOwner),
      ("privateUserName", toJson ((Lean.privateToUserName? name).map Name.toString)),
      ("kind", toJson "theorem"), ("levelParams", toJson (ci.levelParams.map Name.toString)),
      ("type", PiExponentInterfaceSnapshot.exprJson ci.type), ("value", Json.null),
      ("closedType", toJson true), ("closedValue", toJson true), ("isProp", toJson true),
      ("typeRefs", toJson ((ci.type.getUsedConstants.map Name.toString).qsort (· < ·))),
      ("valueRefs", toJson ((thm.value.getUsedConstants.map Name.toString).qsort (· < ·))),
      ("axioms", toJson ax)]
  IO.FS.writeFile output <| (Json.mkObj [
    ("schemaVersion", toJson (1 : Nat)), ("probeMainModule", toJson env.mainModule.toString),
    ("sourceModule", toJson owner), ("rawSourceAutomaticCIs", Json.arr rows)]).compress
end AnalyticRemainderSourceAutomaticProbe

run_meta do
  AnalyticRemainderSourceAutomaticProbe.exportAutomaticCIs #[`OAI.PiExponent.Collision.collisionRatio._proof_1, `OAI.PiExponent.Collision.collisionRemainder._proof_1] "OAI.NumberTheory.PiExponent.Analysis.CollisionExponential" "missions/pi-irrationality-measure/verification/ap19/analytic-remainder-auto-ci-source-v4/source-automatic-ci.json"
#print axioms OAI.PiExponent.Collision.collisionRatio._proof_1
#print axioms OAI.PiExponent.Collision.collisionRemainder._proof_1
