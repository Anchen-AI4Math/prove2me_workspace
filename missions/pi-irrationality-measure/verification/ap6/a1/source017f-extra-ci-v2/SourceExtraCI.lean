import Lean
import OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters
import OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension

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

namespace A1FExtraCI

def refs (value : Expr) : Array Name :=
  (value.getUsedConstants).qsort (fun a b => a.toString < b.toString)

def declarationValue (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo d => some d.value
  | .thmInfo t => some t.value
  | _ => none

def actualOwner (env : Environment) (name : Name) : MetaM Json := do
  let some index := env.getModuleIdxFor? name
    | throwError "Declaration has no actual module index: {name}"
  let some owner := env.header.moduleNames[index.toNat]?
    | throwError "Invalid actual owner module index for {name}"
  pure <| Json.mkObj [
    ("moduleIndex", toJson index.toNat),
    ("module", toJson owner.toString)]

def fullCI (name : Name) : MetaM Json := do
  let env ← getEnv
  let some ci := env.find? name | throwError "Missing actual CI: {name}"
  let some value := declarationValue ci | throwError "CI has no actual value: {name}"
  if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars then
    throwError "CI type is not closed: {name}"
  if value.hasMVar || value.hasFVar || value.hasLooseBVars then
    throwError "CI value is not closed: {name}"
  let axioms ← Lean.collectAxioms name
  unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
    throwError "CI uses axioms outside Std3: {name}"
  let owner ← actualOwner env name
  let typeText ← ppExpr ci.type
  pure <| Json.mkObj [
    ("name", toJson name.toString),
    ("kind", toJson (match ci with | .thmInfo _ => "theorem" | .defnInfo _ => "definition" | _ => "other")),
    ("levelParams", toJson (ci.levelParams.map Name.toString)),
    ("closedType", toJson true),
    ("closedValue", toJson true),
    ("type", PiExponentInterfaceSnapshot.exprJson ci.type),
    ("value", PiExponentInterfaceSnapshot.exprJson value),
    ("prettyType", toJson typeText.pretty),
    ("typeRefs", toJson ((refs ci.type).map Name.toString)),
    ("valueRefs", toJson ((refs value).map Name.toString)),
    ("axioms", toJson ((axioms.map Name.toString).qsort (fun a b => a < b))),
    ("owner", owner)]

def exportActual (side output : String) : MetaM Unit := do
  let env ← getEnv
  let mut parentRows : Array Json := #[]
  let mut allHelpers : Array Name := #[]
  for parentName in #[
      `OAI.PiExponent.interpolationSeparationConstant,
      `OAI.PiExponent.weightErrorCoefficient,
      `OAI.PiExponent.dimension_volume_lt_one] do
    let some ci := env.find? parentName | throwError "Missing source parent: {parentName}"
    let some value := declarationValue ci | throwError "Parent lacks value: {parentName}"
    let prefix := parentName.toString ++ "._proof_"
    let immediate := (refs value).filter (fun n => n.toString.startsWith prefix)
    if parentName != `OAI.PiExponent.dimension_volume_lt_one then
      let expected := if parentName == `OAI.PiExponent.interpolationSeparationConstant then
        #[`OAI.PiExponent.interpolationSeparationConstant._proof_1]
        else #[`OAI.PiExponent.weightErrorCoefficient._proof_1,
               `OAI.PiExponent.weightErrorCoefficient._proof_2]
      unless immediate == expected do
        throwError "Exact immediate helper names differ for parent {parentName}: {immediate}"
    else
      unless !immediate.isEmpty do
        throwError "Source parent has no immediate auto-proof CI: {parentName}"
    let parentCI ← fullCI parentName
    let mut helperRows : Array Json := #[]
    for helperName in immediate do
      allHelpers := allHelpers.push helperName
      helperRows := helperRows.push (← fullCI helperName)
    parentRows := parentRows.push <| Json.mkObj [
      ("parent", parentCI),
      ("immediateAutoProofRefs", toJson (immediate.map Name.toString)),
      ("helpers", Json.arr helperRows)]
  let result := Json.mkObj [
    ("schemaVersion", toJson (1 : Nat)),
    ("artifactKind", toJson "admissible-parent-auto-ci-paired-probe"),
    ("side", toJson side),
    ("probeMainModule", toJson env.mainModule.toString),
    ("sourceParents", Json.arr parentRows),
    ("dynamicallyDiscoveredHelperNames", toJson ((allHelpers.map Name.toString).qsort (fun a b => a < b))),
    ("std3AllowedAxioms", toJson (["propext", "Classical.choice", "Quot.sound"] : List String))]
  IO.FS.writeFile output result.compress

end A1FExtraCI

run_meta do
  A1FExtraCI.exportActual "source" "missions/pi-irrationality-measure/verification/ap6/a1/source017f-extra-ci-v2/source-extra.json"

