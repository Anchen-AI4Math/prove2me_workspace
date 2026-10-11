import Lean
import OAI.NumberTheory.PiExponent.Cohomology.CechOneConverse


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

def after (beforeNames : Std.HashSet Name) (prefixRequests : Array (String × String))
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
  let mut prefixRows : Array Json := #[]
  for (sourceGraphName, sourceUserName) in prefixRequests do
    let names := env.constants.toList.filterMap fun (name, _) =>
      if beforeNames.contains name && (env.getModuleIdxFor? name).isNone &&
          (((privateToUserName? name).map Name.toString) == some sourceUserName) then
        some name
      else none
    unless names.length == 1 do
      throwError "Copied-prefix private user-name is not one actual prior OwnModule CI: {sourceUserName}"
    prefixRows := prefixRows.push <| Json.mkObj [
      ("sourceGraphName", toJson sourceGraphName), ("sourceUserName", toJson sourceUserName),
      ("association", toJson "copied-prefix-actual-OwnModule-CI"),
      ("CI", ← checkedCI names.head!)]
  let result := Json.mkObj [
    ("association", toJson "exact-parser-command-env-Name-set-delta"),
    ("sourceModule", toJson sourceModule), ("sourceCommandSHA256", toJson sourceCommandSHA),
    ("primaryActualName", toJson primary.head!.toString),
    ("primaryExpectedUserName", toJson expectedUser),
    ("beforeNameCount", toJson beforeNames.size),
    ("afterNameCount", toJson env.constants.toList.length),
    ("actualEmittedNames", toJson (delta.map Name.toString)),
    ("rows", Json.arr rows), ("copiedPrefixMappings", Json.arr prefixRows),
    ("probeMainModule", toJson env.mainModule.toString),
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
namespace OAI

namespace PiExponent.GeometrySupport.CechH1Transfer
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace
open PiExponentSeshadri.ModuleFlasque
open CechOne CechHigher

universe u
variable {X Y : Scheme.{u}} {J : Type u}

private abbrev schemeFreeOpen (Z : Scheme.{u}) (U : Z.Opens) : Z.Modules :=
  freeOpen Z.ringCatSheaf U

private abbrev schemeUnit (Z : Scheme.{u}) : Z.Modules :=
  SheafOfModules.unit Z.ringCatSheaf

@[instance_reducible] private def freeOpenHomAddCommGroup
    (Z : Scheme.{u}) (U : Z.Opens) (M : Z.Modules) :
    AddCommGroup (freeOpen Z.ringCatSheaf U ⟶ M) :=
  inferInstanceAs (AddCommGroup (schemeFreeOpen Z U ⟶ M))


run_cmd do
  let envBefore ← Lean.getEnv
  let beforeNames := envBefore.constants.toList.foldl (fun names item => names.insert item.1) ({} : Std.HashSet Lean.Name)
  let commandText : String := "@[instance_reducible] private def higherCochainAddCommGroup\r\n    (Z : Scheme.{u}) (U : J → Z.Opens) (M : Z.Modules) (q : ℕ) :\r\n    AddCommGroup (CechHigher.Cochain Z.ringCatSheaf U M q) :=\r\n  inferInstanceAs (AddCommGroup (∀ t : Fin (q + 1) → J,\r\n    schemeFreeOpen Z (intersection U t) ⟶ M))"
  let commandSyntax ← match Lean.Parser.runParserCategory envBefore (Lean.Name.mkSimple "command") commandText "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:25" with
    | .ok parsedCommand => pure parsedCommand
    | .error message => throwError "Exact source command parse failed: {message}"
  unless commandSyntax.getKind.toString == "Lean.Parser.Command.declaration" do
    throwError "Parsed command kind differs from the authoritative source AST"
  Lean.Elab.Command.elabCommand commandSyntax
  Lean.Elab.Command.liftTermElabM do
    PiExponentCommandEmissionProbe.after beforeNames #[("_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.freeOpenHomAddCommGroup", "OAI.PiExponent.GeometrySupport.CechH1Transfer.freeOpenHomAddCommGroup"), ("_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.freeOpenHomAddCommGroup._aux_1", "OAI.PiExponent.GeometrySupport.CechH1Transfer.freeOpenHomAddCommGroup._aux_1"), ("_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.freeOpenHomAddCommGroup._aux_12", "OAI.PiExponent.GeometrySupport.CechH1Transfer.freeOpenHomAddCommGroup._aux_12"), ("_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.freeOpenHomAddCommGroup._aux_14", "OAI.PiExponent.GeometrySupport.CechH1Transfer.freeOpenHomAddCommGroup._aux_14"), ("_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.freeOpenHomAddCommGroup._aux_16", "OAI.PiExponent.GeometrySupport.CechH1Transfer.freeOpenHomAddCommGroup._aux_16"), ("_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.freeOpenHomAddCommGroup._aux_4", "OAI.PiExponent.GeometrySupport.CechH1Transfer.freeOpenHomAddCommGroup._aux_4"), ("_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.freeOpenHomAddCommGroup._aux_8", "OAI.PiExponent.GeometrySupport.CechH1Transfer.freeOpenHomAddCommGroup._aux_8"), ("_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.freeOpenHomAddCommGroup._proof_10", "OAI.PiExponent.GeometrySupport.CechH1Transfer.freeOpenHomAddCommGroup._proof_10"), ("_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.freeOpenHomAddCommGroup._proof_11", "OAI.PiExponent.GeometrySupport.CechH1Transfer.freeOpenHomAddCommGroup._proof_11"), ("_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.freeOpenHomAddCommGroup._proof_18", "OAI.PiExponent.GeometrySupport.CechH1Transfer.freeOpenHomAddCommGroup._proof_18"), ("_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.freeOpenHomAddCommGroup._proof_19", "OAI.PiExponent.GeometrySupport.CechH1Transfer.freeOpenHomAddCommGroup._proof_19"), ("_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.freeOpenHomAddCommGroup._proof_20", "OAI.PiExponent.GeometrySupport.CechH1Transfer.freeOpenHomAddCommGroup._proof_20"), ("_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.freeOpenHomAddCommGroup._proof_21", "OAI.PiExponent.GeometrySupport.CechH1Transfer.freeOpenHomAddCommGroup._proof_21"), ("_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.freeOpenHomAddCommGroup._proof_22", "OAI.PiExponent.GeometrySupport.CechH1Transfer.freeOpenHomAddCommGroup._proof_22"), ("_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.freeOpenHomAddCommGroup._proof_23", "OAI.PiExponent.GeometrySupport.CechH1Transfer.freeOpenHomAddCommGroup._proof_23"), ("_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.freeOpenHomAddCommGroup._proof_3", "OAI.PiExponent.GeometrySupport.CechH1Transfer.freeOpenHomAddCommGroup._proof_3"), ("_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.freeOpenHomAddCommGroup._proof_6", "OAI.PiExponent.GeometrySupport.CechH1Transfer.freeOpenHomAddCommGroup._proof_6"), ("_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.freeOpenHomAddCommGroup._proof_7", "OAI.PiExponent.GeometrySupport.CechH1Transfer.freeOpenHomAddCommGroup._proof_7"), ("_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.schemeFreeOpen", "OAI.PiExponent.GeometrySupport.CechH1Transfer.schemeFreeOpen"), ("_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.schemeUnit", "OAI.PiExponent.GeometrySupport.CechH1Transfer.schemeUnit")] "OAI.PiExponent.GeometrySupport.CechH1Transfer.higherCochainAddCommGroup" "96eb3e677ec1e4774a63c9afc3eafaef9dea580381e77cff7ca9a6c8f2034050" "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer" "missions/pi-irrationality-measure/verification/command-emission-probe/command-emitted.json"
end
end CechH1Transfer
end GeometrySupport
end PiExponent
end OAI
