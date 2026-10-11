import Lean
import OAI.NumberTheory.PiExponent.Approximation.Parameters

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

run_meta do
  PiExponentInterfaceSnapshot.exportSnapshot #[`OAI.PiExponent.exists_eta_preserving_exponent_gap, `OAI.PiExponent.exists_parameters] "D:/users/self_projects/prove2me_workspace/missions/pi-irrationality-measure/verification/ap6/c5/source-type.json"

open Lean Meta in
run_meta do
  let env ← Lean.getEnv
  let mut rows : Array Lean.Json := #[]
  let name : Lean.Name := `OAI.PiExponent.exists_eta_preserving_exponent_gap
  let some idx := env.getModuleIdxFor? name | throwError "expected imported theorem"
  let some owner := env.header.moduleNames[idx.toNat]? | throwError "bad imported owner index"
  unless owner.toString == "OAI.NumberTheory.PiExponent.Approximation.Parameters" do throwError "wrong actual imported theorem owner"
  let some ci := env.find? name | throwError "missing imported theorem"
  let value ← match ci with | .thmInfo t => pure t.value | _ => throwError "expected theorem CI"
  if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars || value.hasMVar || value.hasFVar || value.hasLooseBVars then throwError "open theorem CI"
  let axioms ← collectAxioms name
  unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do throwError "nonstandard axiom"
  rows := rows.push <| Lean.Json.mkObj [("name", toJson name.toString), ("kind", toJson "theorem"),
    ("levelParams", toJson (ci.levelParams.map Lean.Name.toString)),
    ("closedType", toJson true), ("closedValue", toJson true),
    ("typeRefs", toJson ((ci.type.getUsedConstants.map Lean.Name.toString).qsort (fun a b => a < b))),
    ("valueRefs", toJson ((value.getUsedConstants.map Lean.Name.toString).qsort (fun a b => a < b))),
    ("axioms", toJson (axioms.map Lean.Name.toString)),
    ("owner", Lean.Json.mkObj [("kind", toJson "ImportedModule"), ("module", toJson owner.toString), ("index", toJson idx.toNat)])]
  let name : Lean.Name := `OAI.PiExponent.exists_parameters
  let some idx := env.getModuleIdxFor? name | throwError "expected imported theorem"
  let some owner := env.header.moduleNames[idx.toNat]? | throwError "bad imported owner index"
  unless owner.toString == "OAI.NumberTheory.PiExponent.Approximation.Parameters" do throwError "wrong actual imported theorem owner"
  let some ci := env.find? name | throwError "missing imported theorem"
  let value ← match ci with | .thmInfo t => pure t.value | _ => throwError "expected theorem CI"
  if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars || value.hasMVar || value.hasFVar || value.hasLooseBVars then throwError "open theorem CI"
  let axioms ← collectAxioms name
  unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do throwError "nonstandard axiom"
  rows := rows.push <| Lean.Json.mkObj [("name", toJson name.toString), ("kind", toJson "theorem"),
    ("levelParams", toJson (ci.levelParams.map Lean.Name.toString)),
    ("closedType", toJson true), ("closedValue", toJson true),
    ("typeRefs", toJson ((ci.type.getUsedConstants.map Lean.Name.toString).qsort (fun a b => a < b))),
    ("valueRefs", toJson ((value.getUsedConstants.map Lean.Name.toString).qsort (fun a b => a < b))),
    ("axioms", toJson (axioms.map Lean.Name.toString)),
    ("owner", Lean.Json.mkObj [("kind", toJson "ImportedModule"), ("module", toJson owner.toString), ("index", toJson idx.toNat)])]
  IO.FS.writeFile "D:/users/self_projects/prove2me_workspace/missions/pi-irrationality-measure/verification/ap6/c5/source-proof-references.json" ((Lean.Json.mkObj [("schemaVersion", toJson 1), ("probeMainModule", toJson env.mainModule.toString), ("rows", Lean.Json.arr rows)]).pretty)
#print axioms OAI.PiExponent.exists_eta_preserving_exponent_gap
#print axioms OAI.PiExponent.exists_parameters
