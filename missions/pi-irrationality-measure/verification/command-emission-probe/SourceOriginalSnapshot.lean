import Lean
import OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer

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

namespace PiExponentCommandEmissionProbe
open Lean Meta

def owner (env : Environment) (name : Name) : Json :=
  match env.getModuleIdxFor? name with
  | some idx => Json.mkObj [
      ("kind", toJson "ImportedModule"), ("moduleIndex", toJson idx.toNat),
      ("module", toJson (env.header.moduleNames[idx.toNat]?.map Name.toString))]
  | none => Json.mkObj [("kind", toJson "OwnModule"), ("module", toJson env.mainModule.toString)]

def checkedCI (name : Name) : MetaM Json := do
  let ci ← getConstInfo name
  if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars then
    throwError "Command probe CI type is not closed: {name}"
  let (kind, value, safety) ← match ci with
    | .defnInfo d => pure ("def", some d.value, toJson (reprStr d.safety))
    | .thmInfo t => do
      if t.value.hasMVar || t.value.hasFVar || t.value.hasLooseBVars then
        throwError "Command probe theorem proof is not closed: {name}"
      pure ("theorem", none, Json.null)
    | _ => throwError "Command probe unsupported emitted CI kind: {name}"
  if value.any (fun e => e.hasMVar || e.hasFVar || e.hasLooseBVars) then
    throwError "Command probe CI value is not closed: {name}"
  let axioms ← collectAxioms name
  unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
    throwError "Command probe CI has nonstandard axioms: {name}"
  return Json.mkObj [
    ("actualName", toJson name.toString),
    ("privateUserName", toJson (privateToUserName? name |>.map Name.toString)),
    ("kind", toJson kind), ("safety", safety),
    ("levelParams", toJson (ci.levelParams.map Name.toString)),
    ("type", PiExponentInterfaceSnapshot.exprJson ci.type),
    ("value", value.map PiExponentInterfaceSnapshot.exprJson |>.getD Json.null),
    ("typeRefs", toJson (ci.type.getUsedConstants.map Name.toString)),
    ("valueRefs", toJson (value.map Expr.getUsedConstants |>.getD #[] |>.map Name.toString)),
    ("owner", owner (← getEnv) name),
    ("axioms", toJson (axioms.map Name.toString))]

def after (beforeNames : Std.HashSet Name)
    (expectedUser sourceCommandSHA sourceModule output : String) : MetaM Unit := do
  let env ← getEnv
  -- Compare actual Lean.Name values, not printed suffixes or private counters.
  let delta := env.constants.toList.filterMap fun (name, _) =>
    if beforeNames.contains name then none else some name
  let primary := delta.filter fun name =>
    ((privateToUserName? name).map Name.toString) == some expectedUser
  unless primary.length == 1 do
    throwError "Exact command did not emit one actual primary private binding"
  let mut rows : Array Json := #[]
  for name in delta do
    unless (env.getModuleIdxFor? name).isNone do
      throwError "Exact command delta contains an imported constant"
    rows := rows.push (← checkedCI name)
  let result := Json.mkObj [
    ("association", toJson "exact-parser-command-env-Name-set-delta"),
    ("sourceModule", toJson sourceModule), ("sourceCommandSHA256", toJson sourceCommandSHA),
    ("primaryActualName", toJson primary.head!.toString),
    ("primaryExpectedUserName", toJson expectedUser),
    ("beforeNameCount", toJson beforeNames.size),
    ("afterNameCount", toJson env.constants.toList.length),
    ("actualEmittedNames", toJson (delta.map Name.toString)),
    ("rows", Json.arr rows), ("probeMainModule", toJson env.mainModule.toString),
    ("theoremProofValuesExported", toJson false)]
  IO.FS.writeFile output result.compress

def sourceSnapshot (requests : Array (String × String)) (output : String) : MetaM Unit := do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for (graphName, expectedModule) in requests do
    let names := env.constants.toList.filterMap fun (name, _) =>
      if name.toString == graphName then some name else none
    unless names.length == 1 do
      throwError "Graph name does not select one original actual CI: {graphName}"
    let actualName := names.head!
    let some idx := env.getModuleIdxFor? actualName | throwError "Original CI is not imported"
    unless (env.header.moduleNames[idx.toNat]?.map Name.toString) == some expectedModule do
      throwError "Original actual CI owner differs from the graph module"
    rows := rows.push (← checkedCI actualName)
  IO.FS.writeFile output (Json.arr rows |>.compress)

end PiExponentCommandEmissionProbe

run_meta do
  PiExponentCommandEmissionProbe.sourceSnapshot #[("_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.higherCochainAddCommGroup", "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer"), ("_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.higherCochainAddCommGroup._aux_1", "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer"), ("_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.higherCochainAddCommGroup._aux_12", "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer"), ("_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.higherCochainAddCommGroup._aux_14", "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer"), ("_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.higherCochainAddCommGroup._aux_16", "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer"), ("_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.higherCochainAddCommGroup._aux_4", "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer"), ("_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.higherCochainAddCommGroup._aux_8", "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer"), ("_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.higherCochainAddCommGroup._proof_10", "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer"), ("_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.higherCochainAddCommGroup._proof_11", "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer"), ("_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.higherCochainAddCommGroup._proof_18", "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer"), ("_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.higherCochainAddCommGroup._proof_19", "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer"), ("_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.higherCochainAddCommGroup._proof_20", "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer"), ("_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.higherCochainAddCommGroup._proof_21", "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer"), ("_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.higherCochainAddCommGroup._proof_22", "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer"), ("_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.higherCochainAddCommGroup._proof_23", "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer"), ("_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.higherCochainAddCommGroup._proof_3", "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer"), ("_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.higherCochainAddCommGroup._proof_6", "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer"), ("_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.higherCochainAddCommGroup._proof_7", "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer"), ("_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.schemeFreeOpen", "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer")] "missions/pi-irrationality-measure/verification/command-emission-probe/original-command-closure.json"
