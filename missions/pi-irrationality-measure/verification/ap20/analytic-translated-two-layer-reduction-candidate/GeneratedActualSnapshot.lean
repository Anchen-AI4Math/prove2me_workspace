import Lean
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_actual_minor_analytic_bound
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_norm_actual_summand_le
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_actual_minor_expansion
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_card_choiceFamily_le
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_actualRowCount_pos
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_indexWeight_nonneg
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_rowWeight_le_indexWeight_of_ne_zero
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_sum_rowWeight_eq
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_low_transverse_capacity
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_lowIndexCount_pos
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_norm_scalar_product_le
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_norm_choiceMatrix_le
import Theorems.Thm_OAI_PiExponent_DeterminantAnalyticBound_log_norm_sum_le
import Theorems.Thm_OAI_PiExponent_DeterminantAnalyticBound_translated_summand_bound
import Solutions.Sol_OAI_PiExponent_LiteralAnalytic_actual_minor_analytic_bound_two_layer_graph_ap20

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


namespace AnalyticTranslatedOwnedInventory
open Lean Meta
def exportInventory (anchors : Array Name) (owners : Array String) (output : String) : MetaM Unit := do
  let env ← getEnv
  unless anchors.size == owners.size do throwError "Raw inventory anchor/owner domain differs"
  let mut indices : Std.HashSet Nat := {}
  for i in [:anchors.size] do
    let some idx := env.getModuleIdxFor? anchors[i]! | throwError "Raw inventory owner is not imported"
    unless env.header.moduleNames[idx.toNat]?.map Name.toString == some owners[i]! do throwError "Raw inventory owner differs"
    indices := indices.insert idx.toNat
  let mut found : Array (Name × ConstantInfo × Nat) := #[]
  for (name, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    if indices.contains idx.toNat then found := found.push (name,ci,idx.toNat)
  found := found.qsort (fun a b => a.1.toString < b.1.toString)
  let mut rows : Array Json := #[]
  for (name,ci,idx) in found do
    let value := match ci with | .thmInfo t => some t.value | .defnInfo d => some d.value | _ => none
    rows := rows.push <| Json.mkObj [
      ("name",toJson name.toString),("actualOwner",toJson ((env.header.moduleNames[idx]!).toString)),
      ("ownerModuleIndex",toJson idx),("privateUserName",toJson ((Lean.privateToUserName? name).map Name.toString)),
      ("kind",toJson (match ci with | .thmInfo _ => "theorem" | .defnInfo _ => "def" | _ => "other")),
      ("levelParams",toJson (ci.levelParams.map Name.toString)),("type",PiExponentInterfaceSnapshot.exprJson ci.type),("value",Json.null),
      ("closedType",toJson (!ci.type.hasMVar && !ci.type.hasFVar)),("closedValue",toJson (value.map (fun e => !e.hasMVar && !e.hasFVar))),
      ("isProp",toJson (← isProp ci.type)),("typeRefs",toJson ((ci.type.getUsedConstants.map Name.toString).qsort (· < ·))),
      ("valueRefs",toJson ((value.map (fun e => e.getUsedConstants.map Name.toString) |>.getD #[]).qsort (· < ·))),
      ("axioms",toJson ((← Lean.collectAxioms name).map Name.toString |>.qsort (· < ·)))]
  IO.FS.writeFile output <| (Json.mkObj [("schemaVersion",toJson (1 : Nat)),("probeMainModule",toJson env.mainModule.toString),
    ("ownerModules",toJson owners),("inventorySelection",toJson "all constants, imported ModuleIdx first"),("rawOwnedCIs",Json.arr rows)]).compress
end AnalyticTranslatedOwnedInventory

run_meta do
  AnalyticTranslatedOwnedInventory.exportInventory #[`OAI.PiExponent.LiteralAnalytic.actual_minor_analytic_bound, `OAI.PiExponent.LiteralAnalytic.norm_actual_summand_le, `OAI.PiExponent.LiteralAnalytic.actual_minor_expansion, `OAI.PiExponent.LiteralAnalytic.card_choiceFamily_le, `OAI.PiExponent.LiteralAnalytic.actualRowCount_pos, `OAI.PiExponent.LiteralAnalytic.indexWeight_nonneg, `OAI.PiExponent.LiteralAnalytic.rowWeight_le_indexWeight_of_ne_zero, `OAI.PiExponent.LiteralAnalytic.sum_rowWeight_eq, `OAI.PiExponent.LiteralAnalytic.low_transverse_capacity, `OAI.PiExponent.LiteralAnalytic.lowIndexCount_pos, `OAI.PiExponent.LiteralAnalytic.norm_scalar_product_le, `OAI.PiExponent.LiteralAnalytic.norm_choiceMatrix_le, `OAI.PiExponent.DeterminantAnalyticBound.log_norm_sum_le, `OAI.PiExponent.DeterminantAnalyticBound.translated_summand_bound, `solution] #["Theorems.Thm_OAI_PiExponent_LiteralAnalytic_actual_minor_analytic_bound", "Theorems.Thm_OAI_PiExponent_LiteralAnalytic_norm_actual_summand_le", "Theorems.Thm_OAI_PiExponent_LiteralAnalytic_actual_minor_expansion", "Theorems.Thm_OAI_PiExponent_LiteralAnalytic_card_choiceFamily_le", "Theorems.Thm_OAI_PiExponent_LiteralAnalytic_actualRowCount_pos", "Theorems.Thm_OAI_PiExponent_LiteralAnalytic_indexWeight_nonneg", "Theorems.Thm_OAI_PiExponent_LiteralAnalytic_rowWeight_le_indexWeight_of_ne_zero", "Theorems.Thm_OAI_PiExponent_LiteralAnalytic_sum_rowWeight_eq", "Theorems.Thm_OAI_PiExponent_LiteralAnalytic_low_transverse_capacity", "Theorems.Thm_OAI_PiExponent_LiteralAnalytic_lowIndexCount_pos", "Theorems.Thm_OAI_PiExponent_LiteralAnalytic_norm_scalar_product_le", "Theorems.Thm_OAI_PiExponent_LiteralAnalytic_norm_choiceMatrix_le", "Theorems.Thm_OAI_PiExponent_DeterminantAnalyticBound_log_norm_sum_le", "Theorems.Thm_OAI_PiExponent_DeterminantAnalyticBound_translated_summand_bound", "Solutions.Sol_OAI_PiExponent_LiteralAnalytic_actual_minor_analytic_bound_two_layer_graph_ap20"] "missions/pi-irrationality-measure/verification/ap20/analytic-translated-two-layer-reduction-candidate/generated-actual-owned-CIs.json"
  SourceRootGraphSnapshot.exportRows #[`OAI.PiExponent.LiteralAnalytic.actual_minor_analytic_bound, `OAI.PiExponent.LiteralAnalytic.norm_actual_summand_le, `OAI.PiExponent.LiteralAnalytic.actual_minor_expansion, `OAI.PiExponent.LiteralAnalytic.card_choiceFamily_le, `OAI.PiExponent.LiteralAnalytic.actualRowCount_pos, `OAI.PiExponent.LiteralAnalytic.indexWeight_nonneg, `OAI.PiExponent.LiteralAnalytic.rowWeight_le_indexWeight_of_ne_zero, `OAI.PiExponent.LiteralAnalytic.sum_rowWeight_eq, `OAI.PiExponent.LiteralAnalytic.low_transverse_capacity, `OAI.PiExponent.LiteralAnalytic.lowIndexCount_pos, `OAI.PiExponent.LiteralAnalytic.norm_scalar_product_le, `OAI.PiExponent.LiteralAnalytic.norm_choiceMatrix_le, `OAI.PiExponent.DeterminantAnalyticBound.log_norm_sum_le, `OAI.PiExponent.DeterminantAnalyticBound.translated_summand_bound, `solution] #["Theorems.Thm_OAI_PiExponent_LiteralAnalytic_actual_minor_analytic_bound", "Theorems.Thm_OAI_PiExponent_LiteralAnalytic_norm_actual_summand_le", "Theorems.Thm_OAI_PiExponent_LiteralAnalytic_actual_minor_expansion", "Theorems.Thm_OAI_PiExponent_LiteralAnalytic_card_choiceFamily_le", "Theorems.Thm_OAI_PiExponent_LiteralAnalytic_actualRowCount_pos", "Theorems.Thm_OAI_PiExponent_LiteralAnalytic_indexWeight_nonneg", "Theorems.Thm_OAI_PiExponent_LiteralAnalytic_rowWeight_le_indexWeight_of_ne_zero", "Theorems.Thm_OAI_PiExponent_LiteralAnalytic_sum_rowWeight_eq", "Theorems.Thm_OAI_PiExponent_LiteralAnalytic_low_transverse_capacity", "Theorems.Thm_OAI_PiExponent_LiteralAnalytic_lowIndexCount_pos", "Theorems.Thm_OAI_PiExponent_LiteralAnalytic_norm_scalar_product_le", "Theorems.Thm_OAI_PiExponent_LiteralAnalytic_norm_choiceMatrix_le", "Theorems.Thm_OAI_PiExponent_DeterminantAnalyticBound_log_norm_sum_le", "Theorems.Thm_OAI_PiExponent_DeterminantAnalyticBound_translated_summand_bound", "Solutions.Sol_OAI_PiExponent_LiteralAnalytic_actual_minor_analytic_bound_two_layer_graph_ap20"] "missions/pi-irrationality-measure/verification/ap20/analytic-translated-two-layer-reduction-candidate/generated-actual-types-and-refs.json" true
#print axioms OAI.PiExponent.LiteralAnalytic.actual_minor_analytic_bound
#print axioms OAI.PiExponent.LiteralAnalytic.norm_actual_summand_le
#print axioms OAI.PiExponent.LiteralAnalytic.actual_minor_expansion
#print axioms OAI.PiExponent.LiteralAnalytic.card_choiceFamily_le
#print axioms OAI.PiExponent.LiteralAnalytic.actualRowCount_pos
#print axioms OAI.PiExponent.LiteralAnalytic.indexWeight_nonneg
#print axioms OAI.PiExponent.LiteralAnalytic.rowWeight_le_indexWeight_of_ne_zero
#print axioms OAI.PiExponent.LiteralAnalytic.sum_rowWeight_eq
#print axioms OAI.PiExponent.LiteralAnalytic.low_transverse_capacity
#print axioms OAI.PiExponent.LiteralAnalytic.lowIndexCount_pos
#print axioms OAI.PiExponent.LiteralAnalytic.norm_scalar_product_le
#print axioms OAI.PiExponent.LiteralAnalytic.norm_choiceMatrix_le
#print axioms OAI.PiExponent.DeterminantAnalyticBound.log_norm_sum_le
#print axioms OAI.PiExponent.DeterminantAnalyticBound.translated_summand_bound
#print axioms solution
