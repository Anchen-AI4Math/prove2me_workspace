import Lean
import OAI.NumberTheory.PiExponent.Analysis.CollisionCombinatorics

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

set_option pp.universes true
set_option pp.fullNames true
set_option pp.explicit true
run_meta do
  PiExponentInterfaceSnapshot.exportSnapshot #[`OAI.PiExponent.Collision.sum_weight_ge_of_low_count_le] "missions/pi-irrationality-measure/verification/nodes-isolated-preview/OAI_PiExponent_Collision_sum_weight_ge_of_low_count_le/original-type.json"
#print axioms OAI.PiExponent.Collision.sum_weight_ge_of_low_count_le

open Lean Meta in
run_meta do
  let requests : Array (String × String) := #[("OAI.PiExponent.Collision.cutoff_mul_high_count_le_sum", "OAI.NumberTheory.PiExponent.Analysis.CollisionCombinatorics")]
  let env ← Lean.getEnv
  let mut actualNames : Array Lean.Name := #[]
  for (sourceName, sourceModule) in requests do
    let candidates := env.constants.toList.filterMap fun (n, _) =>
      if n.toString == sourceName then some n else none
    unless candidates.length == 1 do
      throwError "Source helper name does not select one actual environment Name: {sourceName}"
    let actualName := candidates.head!
    let some idx := env.getModuleIdxFor? actualName | throwError "Source helper is not imported"
    let some owner := env.header.moduleNames[idx.toNat]? | throwError "Invalid source module index"
    unless owner.toString == sourceModule do
      throwError "Source helper belongs to the wrong module"
    let some ci := env.find? actualName | throwError "Missing source helper"
    match ci with
    | .thmInfo _ => pure ()
    | _ => throwError "Source helper is not a theorem"
    let axioms ← Lean.collectAxioms actualName
    unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
      throwError "Original helper has a nonstandard axiom"
    actualNames := actualNames.push actualName
  PiExponentInterfaceSnapshot.exportSnapshot actualNames "missions/pi-irrationality-measure/verification/nodes-isolated-preview/OAI_PiExponent_Collision_sum_weight_ge_of_low_count_le/original-inline-types.json"
