import Lean
import OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction
import OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand

set_option maxRecDepth 100000

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


namespace IndexWeightActualCI
open Lean Meta

def owner (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => (env.header.moduleNames[i.toNat]?.getD env.mainModule).toString
  | none => env.mainModule.toString

def valueOf (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo d => some d.value
  | .thmInfo t => some t.value
  | .opaqueInfo o => some o.value
  | _ => none

def refs (e : Expr) : Array String :=
  (e.getUsedConstants.map Name.toString).qsort (· < ·)

def row (n : Name) : MetaM Json := do
  let ci ← getConstInfo n
  let v := valueOf ci
  let tr := refs ci.type
  let vr := v.map refs |>.getD #[]
  let used := ((tr ++ vr).toList.eraseDups.toArray).qsort (· < ·)
  let kind := match ci with
    | .defnInfo _ => "def"
    | .thmInfo _ => "theorem"
    | .opaqueInfo _ => "opaque"
    | .ctorInfo _ => "constructor"
    | .inductInfo _ => "inductive"
    | .recInfo _ => "recursor"
    | .axiomInfo _ => "axiom"
    | .quotInfo _ => "quotient"
  return Json.mkObj [
    ("name",toJson n.toString),("actualOwner",toJson (owner (← getEnv) n)),
    ("privateUserName",toJson ((privateToUserName? n).map Name.toString)),
    ("kind",toJson kind),("levelParams",toJson (ci.levelParams.map Name.toString)),
    ("type",PiExponentInterfaceSnapshot.exprJson ci.type),
    ("value",if kind == "def" then v.map PiExponentInterfaceSnapshot.exprJson |>.getD Json.null else Json.null),
    ("closedType",toJson (!ci.type.hasMVar && !ci.type.hasFVar && !ci.type.hasLooseBVars)),
    ("closedValue",toJson (!v.any (fun e => e.hasMVar || e.hasFVar || e.hasLooseBVars))),
    ("isProp",toJson (← isProp ci.type)),("typeRefs",toJson tr),("valueRefs",toJson vr),
    ("allUsedConstants",toJson used),
    ("axioms",toJson ((← collectAxioms n).map Name.toString |>.qsort (· < ·)))]

def inventory (anchors : Array Name) (output : String) : MetaM (Array Name) := do
  let env ← getEnv
  let mut indices : Std.HashSet Nat := {}
  for n in anchors do
    let some i := env.getModuleIdxFor? n | throwError "Inventory anchor has no actual imported owner: {n}"
    indices := indices.insert i.toNat
  let mut names : Array Name := #[]
  -- Inspect every constant. Only matching ModuleIdx entries incur name/type work.
  for (n, _) in env.constants.toList do
    if let some i := env.getModuleIdxFor? n then
      if indices.contains i.toNat then names := names.push n
  names := names.qsort (fun a b => a.toString < b.toString)
  let mut rows : Array Json := #[]
  for n in names do rows := rows.push (← row n)
  IO.FS.writeFile output <| (Json.mkObj [("schemaVersion",toJson (1 : Nat)),
    ("probeMainModule",toJson env.mainModule.toString),("inventorySelection",toJson "all constants, imported ModuleIdx first"),
    ("anchorNames",toJson (anchors.map Name.toString)),("rawOwnedNames",toJson (names.map Name.toString)),
    ("rawOwnedCIs",Json.arr rows)]).compress
  return names

def proofClosure (roots boundaries : Array Name) : MetaM (Array Json) := do
  let env ← getEnv
  let mut owned : Std.HashSet Nat := {}
  for n in roots do
    if let some i := env.getModuleIdxFor? n then owned := owned.insert i.toNat
  let mut queue := roots
  let mut seen : Std.HashSet Name := {}
  let mut result : Array Json := #[]
  while !queue.isEmpty do
    let n := queue.back!
    queue := queue.pop
    if seen.contains n then continue
    seen := seen.insert n
    let ci ← getConstInfo n
    let .thmInfo t := ci | throwError "Proof closure root is not an actual theorem: {n}"
    result := result.push (← row n)
    for r in ci.type.getUsedConstants ++ t.value.getUsedConstants do
      if boundaries.contains r then continue
      let project := (privateToUserName r).toString.startsWith "OAI."
      let localOwner := (env.getModuleIdxFor? r).any (fun i => owned.contains i.toNat)
      if project || localOwner then
        if let some (.thmInfo _) := env.find? r then queue := queue.push r
  return result.qsort (fun a b =>
    (a.getObjValAs? String "name").toOption.getD "" < (b.getObjValAs? String "name").toOption.getD "")

def exportSource (roots boundaries : Array Name) (inventoryPath output : String) : MetaM Unit := do
  let _ ← inventory roots inventoryPath
  let rows ← proofClosure roots boundaries
  IO.FS.writeFile output <| (Json.mkObj [("schemaVersion",toJson (1 : Nat)),("side",toJson "source"),
    ("probeMainModule",toJson (← getEnv).mainModule.toString),("rootNames",toJson (roots.map Name.toString)),("boundaryNames",toJson (boundaries.map Name.toString)),
    ("rows",Json.arr rows)]).compress

def exportGenerated (helpers boundaries : Array Name) (inventoryPath output : String) : MetaM Unit := do
  let names ← inventory #[`solution] inventoryPath
  let mut roots : Array Name := #[]
  for helper in helpers do
    let actual := names.filter (fun n => privateToUserName? n == some helper)
    unless actual.size == 1 do throwError "Private helper has no unique actual compiler CI: {helper}"
    roots := roots.push actual[0]!
  roots := roots.push `solution
  let rows ← proofClosure roots boundaries
  IO.FS.writeFile output <| (Json.mkObj [("schemaVersion",toJson (1 : Nat)),("side",toJson "generated"),
    ("probeMainModule",toJson (← getEnv).mainModule.toString),("rootNames",toJson (roots.map Name.toString)),("boundaryNames",toJson (boundaries.map Name.toString)),
    ("sourceHelperNames",toJson (helpers.map Name.toString)),("rows",Json.arr rows),
    ("comparatorCI",← row `OAI.PiExponent.LiteralAnalytic.indexWeight_nonneg)]).compress
end IndexWeightActualCI

run_meta do
  IndexWeightActualCI.exportSource #[`OAI.PiExponent.DeterminantContradiction.logWeights_eq, `OAI.PiExponent.LiteralAnalytic.fixedWeights_pos, `OAI.PiExponent.LiteralAnalytic.indexWeight_nonneg] #[`OAI.PiExponent.AdmissibleParameters, `OAI.PiExponent.AdmissibleParameters.m, `OAI.PiExponent.AdmissibleParameters.q, `OAI.PiExponent.AdmissibleParameters.x, `OAI.PiExponent.AdmissibleParameters.x_log, `OAI.PiExponent.AdmissibleParameters.x_one_le, `OAI.PiExponent.Arithmetic.lcmConstant, `OAI.PiExponent.DeterminantContradiction.FixedData, `OAI.PiExponent.DeterminantContradiction.collisionConstant, `OAI.PiExponent.DeterminantContradiction.finiteDenominators, `OAI.PiExponent.LiteralAnalytic.Transverse, `OAI.PiExponent.LiteralAnalytic.fixedWeights, `OAI.PiExponent.LiteralAnalytic.indexWeight, `OAI.PiExponent.MatrixArithmetic.logWeights, `OAI.PiExponent.MatrixTranslation.transverseIndices, `OAI.PiExponent.MatrixTranslationBounds.weight, `OAI.PiExponent.realWeightedSimplex] "missions/pi-irrationality-measure/verification/ap21/index-weight-nonneg-node/source-owned-CI-inventory.json" "missions/pi-irrationality-measure/verification/ap21/index-weight-nonneg-node/source-actual-CIs.json"
#print axioms OAI.PiExponent.DeterminantContradiction.logWeights_eq
#print axioms OAI.PiExponent.LiteralAnalytic.fixedWeights_pos
#print axioms OAI.PiExponent.LiteralAnalytic.indexWeight_nonneg
