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

open Lean Meta

namespace FullRowMinorProofSnapshot

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
    let some owner := env.header.moduleNames[i.toNat]? | throwError "Invalid owner: {name}"
    pure <| Json.mkObj [("kind", toJson "ImportedModule"),
      ("moduleIndex", toJson i.toNat), ("module", toJson owner.toString)]

def ownerModule (env : Environment) (name : Name) : MetaM String := do
  match env.getModuleIdxFor? name with
  | none => pure env.mainModule.toString
  | some i =>
    let some owner := env.header.moduleNames[i.toNat]? | throwError "Invalid owner: {name}"
    pure owner.toString

def ciRow (name : Name) (helper : Bool) : MetaM (List (String × Json)) := do
  let env ← getEnv
  let some ci := env.find? name | throwError "Missing actual CI: {name}"
  let some value := valueOf ci | throwError "No proof value: {name}"
  if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars ||
     value.hasMVar || value.hasFVar || value.hasLooseBVars then
    throwError "Actual CI is not closed: {name}"
  let axioms ← Lean.collectAxioms name
  unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
    throwError "Actual proof CI has axioms outside Std3: {name}"
  let allUsedConstants := refs (mkApp ci.type value)
  let owner ← ownerOf env name
  let common := [
    ("name", toJson name.toString),
    ("levelParams", toJson (ci.levelParams.map Name.toString)),
    ("closedType", toJson true), ("closedValue", toJson true),
    ("typeRefs", toJson ((refs ci.type).map Name.toString)),
    ("valueRefs", toJson ((refs value).map Name.toString)),
    ("allUsedConstants", toJson (allUsedConstants.map Name.toString)),
    ("axioms", toJson ((axioms.map Name.toString).qsort (fun a b => a < b))),
    ("owner", owner)]
  pure <| if helper then
    common ++ [("type", PiExponentInterfaceSnapshot.exprJson ci.type)] else common

def exportEvidence (side output name importModule : String) : MetaM Unit := do
  let env ← getEnv
  let declName := name.toName
  unless (← ownerModule env declName) == importModule do
    throwError "Theorem is not from expected actual imported OLean: {declName}"
  let some ci := env.find? declName | throwError "Missing actual theorem: {declName}"
  let some value := valueOf ci | throwError "Missing actual theorem proof: {declName}"
  let mut pending := (refs value).toList
  let mut seen : Array Name := #[declName]
  let mut helpers : Array Name := #[]
  -- Discover helpers by actual module ownership, including genuine private CI;
  -- never manufacture names from a presumed _proof_ numbering convention.
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    if !seen.contains n then
      seen := seen.push n
      if (← ownerModule env n) == importModule then
        helpers := helpers.push n
        let some helperCI := env.find? n | throwError "Missing actual helper: {n}"
        let some helperValue := valueOf helperCI | throwError "Actual helper lacks value: {n}"
        pending := pending ++ (refs helperValue).toList
  helpers := helpers.qsort (fun a b => a.toString < b.toString)
  let helperRows ← helpers.mapM (fun n => do pure <| Json.mkObj (← ciRow n true))
  let theoremRow ← ciRow declName false
  let report := Json.mkObj [
    ("schemaVersion", toJson (1 : Nat)), ("side", toJson side),
    ("probeMainModule", toJson env.mainModule.toString),
    ("importModule", toJson importModule),
    ("theorem", Json.mkObj (theoremRow ++ [("automaticInlineHelpers", Json.arr helperRows)]))]
  IO.FS.writeFile output report.compress

end FullRowMinorProofSnapshot


namespace SelectedMinorProofSnapshot
open Lean Meta FullRowMinorProofSnapshot
def exportBundle (side output : String) (roots : Array Name) (owners boundary : Array String) : MetaM Unit := do
  let env ← getEnv
  let mut pending := roots.toList
  let mut seen : Array Name := #[]
  let mut found : Array Name := #[]
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    if !seen.contains n && !boundary.contains n.toString then
      seen := seen.push n
      if owners.contains (← ownerModule env n) then
        found := found.push n
        let some ci := env.find? n | throwError "Missing actual proof CI: {n}"
        let some value := valueOf ci | throwError "Missing actual proof value: {n}"
        pending := pending ++ (refs (mkApp ci.type value)).toList
  for root in roots do
    unless found.contains root do throwError "Actual proof root was not exported: {root}"
  found := found.qsort (fun a b => a.toString < b.toString)
  let rows ← found.mapM (fun n => do pure <| Json.mkObj (← ciRow n true))
  IO.FS.writeFile output (Json.mkObj [
    ("schemaVersion",toJson (1 : Nat)),("side",toJson side),
    ("probeMainModule",toJson env.mainModule.toString),
    ("rootNames",toJson (roots.map Name.toString)),
    ("boundaryNames",toJson boundary),("rows",Json.arr rows)] |>.compress)
end SelectedMinorProofSnapshot

run_meta do
  let roots := #[`OAI.PiExponent.Collision.cutoff_mul_high_count_le_sum, `OAI.PiExponent.Collision.sum_weight_ge_of_low_count_le]
  PiExponentInterfaceSnapshot.exportSnapshot roots "missions/pi-irrationality-measure/verification/ap18/sum-weight-child-mirror-v5/source-types.json"
  SelectedMinorProofSnapshot.exportBundle "source" "missions/pi-irrationality-measure/verification/ap18/sum-weight-child-mirror-v5/source-proof-references.json" roots #["OAI.NumberTheory.PiExponent.Analysis.CollisionCombinatorics"] #[]
#print axioms OAI.PiExponent.Collision.sum_weight_ge_of_low_count_le
