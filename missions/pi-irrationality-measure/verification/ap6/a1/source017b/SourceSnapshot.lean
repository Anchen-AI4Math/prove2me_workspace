import Lean
import OAI.NumberTheory.PiExponent.Main

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

set_option pp.universes true
set_option pp.fullNames true
set_option pp.explicit true
run_meta do
  PiExponentInterfaceSnapshot.exportSnapshot #[`OAI.PiExponent.interpolationSeparationConstant_pos, `OAI.PiExponent.weightErrorCoefficient_nonneg, `OAI.PiExponent.exists_initial_scale, `OAI.PiExponent.dimensionK_one_le, `OAI.PiExponent.dimensionW_pos, `OAI.PiExponent.dimensionV_pos, `OAI.PiExponent.dimension_volume, `OAI.PiExponent.dimension_volume_lt_one, `OAI.PiExponent.dimension_collision_identity, `OAI.PiExponent.exists_admissible_parameters] "missions/pi-irrationality-measure/verification/ap6/a1/source017b/source-type.json"
#print axioms OAI.PiExponent.interpolationSeparationConstant_pos
#print axioms OAI.PiExponent.weightErrorCoefficient_nonneg
#print axioms OAI.PiExponent.exists_initial_scale
#print axioms OAI.PiExponent.dimensionK_one_le
#print axioms OAI.PiExponent.dimensionW_pos
#print axioms OAI.PiExponent.dimensionV_pos
#print axioms OAI.PiExponent.dimension_volume
#print axioms OAI.PiExponent.dimension_volume_lt_one
#print axioms OAI.PiExponent.dimension_collision_identity
#print axioms OAI.PiExponent.exists_admissible_parameters
