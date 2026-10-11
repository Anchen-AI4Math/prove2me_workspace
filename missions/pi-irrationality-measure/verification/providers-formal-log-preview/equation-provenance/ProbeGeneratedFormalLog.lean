import Lean
import Lean.Meta.Eqns
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_FormalLogTruncation

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

namespace PiExponentEquationProvenanceProbe
open Lean Meta

def ownership (env : Environment) (name : Name) : Json :=
  match env.getModuleIdxFor? name with
  | some idx => Json.mkObj [
      ("kind", toJson "ImportedModule"), ("index", toJson idx.toNat),
      ("module", toJson (env.header.moduleNames[idx.toNat]?.map Name.toString))]
  | none => Json.mkObj [("kind", toJson "OwnModule"), ("module", toJson env.mainModule.toString)]

def checkedCI (name : Name) : MetaM Json := do
  let ci ← getConstInfo name
  if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars then
    throwError "Equation probe type is not closed: {name}"
  let value := match ci with
    | .defnInfo d => some d.value
    | _ => none
  if value.any (fun e => e.hasMVar || e.hasFVar || e.hasLooseBVars) then
    throwError "Equation probe definition value is not closed: {name}"
  let kind ← match ci with
    | .defnInfo _ => pure "def"
    | .thmInfo _ => pure "theorem"
    | _ => throwError "Equation probe found unsupported constant kind: {name}"
  let axioms ← collectAxioms name
  unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
    throwError "Equation probe nonstandard axiom: {name}"
  return Json.mkObj [
    ("actualName", toJson name.toString),
    ("userName", toJson (privateToUserName name).toString),
    ("levelParams", toJson (ci.levelParams.map Name.toString)),
    ("kind", toJson kind),
    ("type", PiExponentInterfaceSnapshot.exprJson ci.type),
    ("value", value.map PiExponentInterfaceSnapshot.exprJson |>.getD Json.null),
    ("owner", ownership (← getEnv) name),
    ("axioms", toJson (axioms.map Name.toString))]

def exportEquationSnapshot (primary : Name) (expectedModule output side : String) : MetaM Unit := do
  let envBefore ← getEnv
  let ci ← getConstInfo primary
  match ci with
  | .defnInfo _ => pure ()
  | _ => throwError "Primary source binding is not a definition"
  let some idx := envBefore.getModuleIdxFor? primary
    | throwError "Primary must belong to the imported source/provider module"
  unless envBefore.header.moduleNames[idx.toNat]?.map Name.toString == some expectedModule do
    throwError "Primary binding belongs to an unexpected module"
  let equations? ← Lean.Meta.getEqnsFor? primary
  let unfolding? ← Lean.Meta.getUnfoldEqnFor? primary
  let mut equations : Array Json := #[]
  for name in equations?.getD #[] do
    let parent? ← Lean.Meta.isEqnThm? name
    unless parent? == some primary do
      throwError "getEqnsFor? result lacks its exact inverse primary relation: {name}"
    equations := equations.push <| Json.mkObj [
      ("getter", toJson "Lean.Meta.getEqnsFor?"),
      ("inversePrimary", toJson (parent?.map Name.toString)),
      ("CI", ← checkedCI name)]
  let unfolding ← match unfolding? with
    | some name => pure <| Json.mkObj [
        ("getter", toJson "Lean.Meta.getUnfoldEqnFor?"), ("CI", ← checkedCI name)]
    | none => pure Json.null
  let result := Json.mkObj [
    ("side", toJson side), ("expectedModule", toJson expectedModule),
    ("primaryBinding", ← checkedCI primary),
    ("getEqnsForReturnedSome", toJson equations?.isSome),
    ("actualEquationNames", toJson (equations?.map (·.map Name.toString))),
    ("equations", Json.arr equations), ("unfolding", unfolding),
    ("probeMainModule", toJson (← getEnv).mainModule.toString),
    ("theoremProofValuesExported", toJson false)]
  IO.FS.writeFile output result.compress

end PiExponentEquationProvenanceProbe

run_meta do
  PiExponentEquationProvenanceProbe.exportEquationSnapshot `OAI.PiExponent.FormalLogTruncation.shiftMap "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_FormalLogTruncation" "missions/pi-irrationality-measure/verification/providers-formal-log-preview/equation-provenance/generated.json" "generated"
