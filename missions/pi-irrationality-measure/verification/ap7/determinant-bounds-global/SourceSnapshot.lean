import Lean
import OAI.NumberTheory.PiExponent.Approximation.Comparison

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
run_meta do
  PiExponentInterfaceSnapshot.exportSnapshot #[`OAI.PiExponent.determinant_bounds_inconsistent] "missions/pi-irrationality-measure/verification/ap7/determinant-bounds-global/source-type.json"
#print axioms OAI.PiExponent.determinant_bounds_inconsistent

open Lean Meta

namespace DeterminantBoundsSnapshot

def refs (e : Expr) : Array Name :=
  (e.getUsedConstants).qsort (fun a b => a.toString < b.toString)

def valueOf (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo d => some d.value
  | .thmInfo t => some t.value
  | _ => none

def ownerOf (env : Environment) (name : Name) : MetaM Json := do
  match env.getModuleIdxFor? name with
  | none => pure <| Json.mkObj [("kind", toJson "OwnModule"),
      ("moduleIndex", Json.null), ("module", toJson env.mainModule.toString)]
  | some i =>
    let some owner := env.header.moduleNames[i.toNat]? | throwError "Invalid module owner index: {name}"
    pure <| Json.mkObj [("kind", toJson "ImportedModule"),
      ("moduleIndex", toJson i.toNat), ("module", toJson owner.toString)]

def exportEvidence (side output name : String) : MetaM Unit := do
  let env ← getEnv
  let declName := name.toName
  let some ci := env.find? declName | throwError "Missing theorem CI: {declName}"
  let some value := valueOf ci | throwError "Theorem CI has no proof value: {declName}"
  if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars then
    throwError "Theorem type is not closed"
  if value.hasMVar || value.hasFVar || value.hasLooseBVars then
    throwError "Theorem value is not closed"
  let axioms ← Lean.collectAxioms declName
  unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
    throwError "Proof has axioms outside Std3"
  let used := refs value
  let helperPrefix := declName.toString ++ "._proof_"
  let helpers := used.filter (fun n => n.toString.startsWith helperPrefix)
  let mut helperRows : Array Json := #[]
  for helperName in helpers do
    let some helperCI := env.find? helperName | throwError "Missing inline proof CI: {helperName}"
    let some helperValue := valueOf helperCI | throwError "Inline proof CI has no value: {helperName}"
    if helperCI.type.hasMVar || helperCI.type.hasFVar || helperCI.type.hasLooseBVars ||
       helperValue.hasMVar || helperValue.hasFVar || helperValue.hasLooseBVars then
      throwError "Inline proof CI is not closed: {helperName}"
    let helperAxioms ← Lean.collectAxioms helperName
    unless helperAxioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
      throwError "Inline proof uses axioms outside Std3: {helperName}"
    let helperOwner ← ownerOf env helperName
    helperRows := helperRows.push <| Json.mkObj [
      ("name", toJson helperName.toString),
      ("levelParams", toJson (helperCI.levelParams.map Name.toString)),
      ("closedType", toJson true), ("closedValue", toJson true),
      ("type", PiExponentInterfaceSnapshot.exprJson helperCI.type),
      ("value", PiExponentInterfaceSnapshot.exprJson helperValue),
      ("typeRefs", toJson ((refs helperCI.type).map Name.toString)),
      ("valueRefs", toJson ((refs helperValue).map Name.toString)),
      ("axioms", toJson ((helperAxioms.map Name.toString).qsort (fun a b => a < b))),
      ("owner", helperOwner)]
  let owner ← ownerOf env declName
  let row := Json.mkObj [
    ("name", toJson declName.toString),
    ("levelParams", toJson (ci.levelParams.map Name.toString)),
    ("closedType", toJson true), ("closedValue", toJson true),
    ("type", PiExponentInterfaceSnapshot.exprJson ci.type),
    ("value", PiExponentInterfaceSnapshot.exprJson value),
    ("typeRefs", toJson ((refs ci.type).map Name.toString)),
    ("valueRefs", toJson (used.map Name.toString)),
    ("axioms", toJson ((axioms.map Name.toString).qsort (fun a b => a < b))),
    ("owner", owner), ("automaticInlineHelpers", Json.arr helperRows)]
  let report := Json.mkObj [
    ("schemaVersion", toJson (1 : Nat)), ("side", toJson side),
    ("probeMainModule", toJson env.mainModule.toString), ("theorem", row)]
  IO.FS.writeFile output report.compress

end DeterminantBoundsSnapshot

run_meta do
  DeterminantBoundsSnapshot.exportEvidence "source" "missions/pi-irrationality-measure/verification/ap7/determinant-bounds-global/source-proof-references.json" "OAI.PiExponent.determinant_bounds_inconsistent"
