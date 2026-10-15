import Lean
import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_no_fixed_data_of_interpolation_and_analytic_aggregate
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_tendsto_collisionRate_source017
import Theorems.Thm_OAI_PiExponent_InterpolationMatrix_exists_full_row_minor_of_surjective
import Theorems.Thm_OAI_PiExponent_determinant_bounds_inconsistent
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actualMean_bounds
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actual_minor_arithmetic_lower_bound_source017
import Solutions.Sol_OAI_PiExponent_DeterminantContradiction_no_fixed_data_five_children_v2

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

namespace SourceRootGraphSnapshot
open Lean Meta
def exportRows (names : Array Name) (owners : Array String) (output : String) (openTargets : Bool) : MetaM Unit := do
  let env ← getEnv
  unless names.size == owners.size do throwError "Snapshot owner domain differs"
  let mut rows : Array Json := #[]
  for i in [:names.size] do
    let name := names[i]!
    let some ci := env.find? name | throwError "Missing actual declaration: {name}"
    let .thmInfo info := ci | throwError "Expected theorem CI: {name}"
    if ci.type.hasMVar || ci.type.hasFVar || info.value.hasMVar || info.value.hasFVar then
      throwError "Unclosed theorem CI: {name}"
    unless ← isProp ci.type do throwError "The theorem type is not Prop: {name}"
    let owner ← match env.getModuleIdxFor? name with
      | none => pure env.mainModule.toString
      | some idx => do
        let some m := env.header.moduleNames[idx.toNat]? | throwError "Invalid CI owner: {name}"
        pure m.toString
    unless owner == owners[i]! do throwError "Actual declaration owner differs: {name}"
    let axioms ← Lean.collectAxioms name
    let axioms := (axioms.map Name.toString).qsort (· < ·)
    for a in axioms do
      unless a == "propext" || a == "Classical.choice" || a == "Quot.sound" || (openTargets && a == "sorryAx") do
        throwError "Unexpected theorem axiom: {a}"
    if openTargets && !axioms.contains "sorryAx" then throwError "Expected Open placeholder/sketch dependency"
    let typeRefs := (ci.type.getUsedConstants.map Name.toString).qsort (· < ·)
    let valueRefs := (info.value.getUsedConstants.map Name.toString).qsort (· < ·)
    rows := rows.push <| Json.mkObj [
      ("name", toJson name.toString), ("levelParams", toJson (ci.levelParams.map Name.toString)),
      ("type", PiExponentInterfaceSnapshot.exprJson ci.type), ("value", Json.null),
      ("closedType", toJson true), ("closedValue", toJson true), ("isProp", toJson true),
      ("actualOwner", toJson owner), ("axioms", toJson axioms),
      ("typeRefs", toJson typeRefs), ("valueRefs", toJson valueRefs),
      ("Open_sketch_type_check", toJson openTargets)]
  IO.FS.writeFile output (Json.arr rows |>.compress)
end SourceRootGraphSnapshot


run_meta do
  SourceRootGraphSnapshot.exportRows #[`OAI.PiExponent.AdmissibleParameters.total_error_lt_gap, `OAI.PiExponent.AdmissibleParameters.collision_exceeds_one_add_error, `OAI.PiExponent.AdmissibleParameters.error_sum_eq, `OAI.PiExponent.AdmissibleParameters.error_sum_lt_gap, `OAI.PiExponent.AdmissibleParameters.collision_exceeds_error_sum] #["Solutions.Sol_OAI_PiExponent_DeterminantContradiction_no_fixed_data_five_children_v2", "Solutions.Sol_OAI_PiExponent_DeterminantContradiction_no_fixed_data_five_children_v2", "Solutions.Sol_OAI_PiExponent_DeterminantContradiction_no_fixed_data_five_children_v2", "Solutions.Sol_OAI_PiExponent_DeterminantContradiction_no_fixed_data_five_children_v2", "Solutions.Sol_OAI_PiExponent_DeterminantContradiction_no_fixed_data_five_children_v2"] "missions/pi-irrationality-measure/verification/graph-no-fixed-data-route-20261011-v2/generated-five-helper-types-and-refs.json" false

#print axioms OAI.PiExponent.AdmissibleParameters.total_error_lt_gap
#print axioms OAI.PiExponent.AdmissibleParameters.collision_exceeds_one_add_error
#print axioms OAI.PiExponent.AdmissibleParameters.error_sum_eq
#print axioms OAI.PiExponent.AdmissibleParameters.error_sum_lt_gap
#print axioms OAI.PiExponent.AdmissibleParameters.collision_exceeds_error_sum
run_meta do
  SourceRootGraphSnapshot.exportRows #[`OAI.PiExponent.DeterminantContradiction.no_fixed_data_of_interpolation_and_analytic_aggregate, `OAI.PiExponent.DeterminantContradiction.tendsto_collisionRate_source017, `OAI.PiExponent.InterpolationMatrix.exists_full_row_minor_of_surjective, `OAI.PiExponent.determinant_bounds_inconsistent, `OAI.PiExponent.DeterminantContradiction.actualMean_bounds, `OAI.PiExponent.DeterminantContradiction.actual_minor_arithmetic_lower_bound_source017, `solution] #["Theorems.Thm_OAI_PiExponent_DeterminantContradiction_no_fixed_data_of_interpolation_and_analytic_aggregate", "Theorems.Thm_OAI_PiExponent_DeterminantContradiction_tendsto_collisionRate_source017", "Theorems.Thm_OAI_PiExponent_InterpolationMatrix_exists_full_row_minor_of_surjective", "Theorems.Thm_OAI_PiExponent_determinant_bounds_inconsistent", "Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actualMean_bounds", "Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actual_minor_arithmetic_lower_bound_source017", "Solutions.Sol_OAI_PiExponent_DeterminantContradiction_no_fixed_data_five_children_v2"] "missions/pi-irrationality-measure/verification/graph-no-fixed-data-route-20261011-v2/generated-seven-types-and-refs.json" true

#print axioms OAI.PiExponent.DeterminantContradiction.no_fixed_data_of_interpolation_and_analytic_aggregate
#print axioms OAI.PiExponent.DeterminantContradiction.tendsto_collisionRate_source017
#print axioms OAI.PiExponent.InterpolationMatrix.exists_full_row_minor_of_surjective
#print axioms OAI.PiExponent.determinant_bounds_inconsistent
#print axioms OAI.PiExponent.DeterminantContradiction.actualMean_bounds
#print axioms OAI.PiExponent.DeterminantContradiction.actual_minor_arithmetic_lower_bound_source017
#print axioms solution
