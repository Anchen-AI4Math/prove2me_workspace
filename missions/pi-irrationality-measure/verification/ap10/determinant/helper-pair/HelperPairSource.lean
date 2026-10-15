import Lean
import OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction

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
      | .thmInfo t => some t.value
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


open Lean Meta
namespace DeterminantDataHelperPair

def refs (e : Expr) : Array Name :=
  (e.getUsedConstants).qsort (fun a b => a.toString < b.toString)

def valueOf (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo d => some d.value
  | .thmInfo t => some t.value
  | _ => none

def ownerOf (env : Environment) (n : Name) : MetaM String := do
  let some idx := env.getModuleIdxFor? n | throwError "Actual CI has no imported owner: {n}"
  let some owner := env.header.moduleNames[idx.toNat]? | throwError "Invalid imported owner: {n}"
  pure owner.toString

def exportPairSide (side output helper importModule : String) : MetaM Unit := do
  let env ← getEnv
  let name := helper.toName
  let some ci := env.find? name | throwError "Actual referenced helper CI is absent: {name}"
  let some value := valueOf ci | throwError "Actual helper has no value: {name}"
  if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars ||
     value.hasMVar || value.hasFVar || value.hasLooseBVars then
    throwError "Actual helper type/value is not closed"
  unless (← isProp ci.type) do throwError "Differing numeral helper is not a proof of a proposition"
  unless (← ownerOf env name) == importModule do throwError "Actual helper has wrong module owner"
  let axioms ← Lean.collectAxioms name
  unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
    throwError "Actual helper uses axioms outside Std3"
  let mut parents : Array Json := #[]
  for n in #[`OAI.PiExponent.DeterminantContradiction.GlobalInterpolationStatement,
             `OAI.PiExponent.DeterminantContradiction.AnalyticAggregateStatement] do
    let some parent := env.find? n | throwError "Actual parent is missing"
    let some parentValue := valueOf parent | throwError "Actual parent has no value"
    unless (refs parentValue).contains name do throwError "Parent does not actually use the helper"
    parents := parents.push <| Json.mkObj [("name", toJson n.toString),
      ("owner", toJson (← ownerOf env n)),
      ("valueRefs", toJson ((refs parentValue).map Name.toString))]
  let kind := match ci with | .thmInfo _ => "theorem" | .defnInfo _ => "def" | _ => "other"
  let pretty ← ppExpr ci.type
  let row := Json.mkObj [("name", toJson name.toString), ("kind", toJson kind),
    ("levelParams", toJson (ci.levelParams.map Name.toString)),
    ("closedType", toJson true), ("closedValue", toJson true), ("isProp", toJson true),
    ("type", PiExponentInterfaceSnapshot.exprJson ci.type),
    ("value", PiExponentInterfaceSnapshot.exprJson value),
    ("prettyType", toJson pretty.pretty),
    ("typeRefs", toJson ((refs ci.type).map Name.toString)),
    ("valueRefs", toJson ((refs value).map Name.toString)),
    ("axioms", toJson ((axioms.map Name.toString).qsort (fun a b => a < b))),
    ("owner", toJson (← ownerOf env name))]
  let report := Json.mkObj [("schemaVersion", toJson (1 : Nat)), ("side", toJson side),
    ("probeMainModule", toJson env.mainModule.toString), ("importModule", toJson importModule),
    ("helper", row), ("actualParentReferences", Json.arr parents)]
  IO.FS.writeFile output report.compress
end DeterminantDataHelperPair

run_meta do
  DeterminantDataHelperPair.exportPairSide "source" "missions/pi-irrationality-measure/verification/ap10/determinant/helper-pair/source-helper.json" "OAI.PiExponent.DeterminantContradiction.collisionConstant._proof_1" "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction"
#print axioms OAI.PiExponent.DeterminantContradiction.collisionConstant._proof_1
