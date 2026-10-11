import Lean
import OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation

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
  PiExponentInterfaceSnapshot.exportSnapshot #[`OAI.PiExponent.FormalLogTruncation.liftSeries_eq_toMvPowerSeries] "missions/pi-irrationality-measure/verification/formal-log-nodes-preview/nodes/OAI_PiExponent_FormalLogTruncation_liftSeries_eq_toMvPowerSeries/original-type.json"
#print axioms OAI.PiExponent.FormalLogTruncation.liftSeries_eq_toMvPowerSeries

open Lean Meta in
run_meta do
  let requests : Array (String × String × String) := #[]
  let env ← Lean.getEnv
  let mut actualNames : Array Lean.Name := #[]
  for (sourceName, sourceModule, expectedKind) in requests do
    let candidates := env.constants.toList.filterMap fun (n, _) =>
      if n.toString == sourceName then some n else none
    unless candidates.length == 1 do
      throwError "Source Graph name does not select exactly one actual environment Name: {sourceName}"
    let actualName := candidates.head!
    let some idx := env.getModuleIdxFor? actualName | throwError "Source private CI is not imported"
    unless env.header.moduleNames[idx.toNat]?.map Lean.Name.toString == some sourceModule do
      throwError "Source private CI belongs to the wrong module"
    let some ci := env.find? actualName | throwError "Missing source private CI"
    let (kind, value) ← match ci with
      | .thmInfo t => pure ("theorem", t.value)
      | .defnInfo d => pure ("def", d.value)
      | _ => throwError "Source private CI is neither theorem nor definition"
    unless kind == expectedKind do
      throwError "Source private CI kind differs from Graph"
    if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars ||
        value.hasMVar || value.hasFVar || value.hasLooseBVars then
      throwError "Source private CI type/value is not closed"
    let axioms ← Lean.collectAxioms actualName
    unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
      throwError "Source private CI has nonstandard axioms"
    actualNames := actualNames.push actualName
  PiExponentInterfaceSnapshot.exportSnapshot actualNames "missions/pi-irrationality-measure/verification/formal-log-nodes-preview/nodes/OAI_PiExponent_FormalLogTruncation_liftSeries_eq_toMvPowerSeries/original-inline-types.json"

open Lean Meta in
run_meta do
  let requests : Array (String × String) := #[]
  let env ← Lean.getEnv
  let mut actualNames : Array Lean.Name := #[]
  for (graphName, sourceModule) in requests do
    let names := env.constants.toList.filterMap fun (name, _) =>
      if name.toString == graphName then some name else none
    unless names.length == 1 do
      throwError "Expected one public inline CI for {graphName}, found {names.length}"
    let actualName := names.head!
    let some ci := env.find? actualName | throwError "Missing public inline CI"
    match ci with
    | .thmInfo _ => pure ()
    | _ => throwError "Public inline companion is not a theorem: {actualName}"
    if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars then
      throwError "Public inline type is not closed: {actualName}"

    let some idx := env.getModuleIdxFor? actualName
      | throwError "Original public helper is not imported: {actualName}"
    unless env.header.moduleNames[idx.toNat]?.map Lean.Name.toString == some sourceModule do
      throwError "Original public helper owner differs from graph module: {actualName}"

    let axioms ← Lean.collectAxioms actualName
    unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
      throwError "Public inline helper has nonstandard axioms: {actualName}"
    actualNames := actualNames.push actualName
  PiExponentInterfaceSnapshot.exportSnapshot actualNames "missions/pi-irrationality-measure/verification/formal-log-nodes-preview/nodes/OAI_PiExponent_FormalLogTruncation_liftSeries_eq_toMvPowerSeries/original-public-inline-types.json"
