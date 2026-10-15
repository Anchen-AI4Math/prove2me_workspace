import Lean
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData

/-
Copyright (c) OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Schema-v2 interface exporter for atomic structure declarations.  Unlike the
older shared-source snapshot schema, this records every kernel-relevant field
of InductiveVal, ConstructorVal, and RecursorVal.  In particular, recursor
rules include both `nfields` and the complete reduction-rule RHS expression;
comparing only a recursor's type does not establish identical iota reduction.

The caller must import `Lean` and the module being inspected.  Requests are
public exact Names.  No private numeric Name is reconstructed or guessed.
-/

open Lean Meta

namespace PiExponentStructuralKernelSnapshot

structure StructuralRequest where
  sourceName : String
  expectedPublicName : String
  expectedModule : String
  graphKind : String
  declGraphSha256 : String
  declGraphRowSha256 : String
  ownerKind : String
  ownerId : String
  commandUnit : String
  familyRoot : String

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

partial def exprNames : Expr → List Name
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ => []
  | .const n _ => [n]
  | .app f a => exprNames f ++ exprNames a
  | .lam _ t b _ | .forallE _ t b _ => exprNames t ++ exprNames b
  | .letE _ t v b _ => exprNames t ++ exprNames v ++ exprNames b
  | .mdata _ e => exprNames e
  | .proj n _ e => n :: exprNames e

def envKind : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"
  | .quotInfo _ => "quot"

def moduleFor? (env : Environment) (name : Name) : Option Name :=
  match env.getModuleIdxFor? name with
  | some idx => env.header.moduleNames[idx.toNat]?
  | none => none

def isClosed (e : Expr) : Bool :=
  !e.hasMVar && !e.hasFVar && !e.hasLooseBVars

def hasNoFreeOrMetaVars (e : Expr) : Bool :=
  !e.hasMVar && !e.hasFVar

def uniqueSortedNames (names : List Name) : List Name :=
  let unique := names.foldl (fun seen name =>
    if seen.contains name then seen else name :: seen) []
  unique.mergeSort (fun a b => compare a.toString b.toString == .lt)

def isFamilyName (root : String) (name : Name) : Bool :=
  let value := name.toString
  value == root || value.startsWith (root ++ ".")

def directStructuralNames : ConstantInfo → List Name
  | .inductInfo i => i.all ++ i.ctors
  | .ctorInfo c => [c.induct]
  | .recInfo r => r.all ++ r.rules.map (fun rule => rule.ctor)
  | _ => []

partial def structuralClosure
    (env : Environment) (pending : List Name) (seen : List Name := []) : List Name :=
  match pending with
  | [] => uniqueSortedNames seen
  | name :: rest =>
      if seen.contains name then
        structuralClosure env rest seen
      else
        let next := match env.find? name with
          | some ci => directStructuralNames ci
          | none => []
        structuralClosure env (next ++ rest) (name :: seen)

def recursorRulesJson (r : RecursorVal) : Json :=
  Json.arr <| (r.rules.map fun rule : RecursorRule => Json.mkObj [
    ("ctor", toJson rule.ctor.toString),
    ("nfields", toJson rule.nfields),
    ("rhs", exprJson rule.rhs)]).toArray

def completeKernelMetadata : ConstantInfo → Json
  | .thmInfo _ => Json.mkObj [("proofValueExported", toJson false)]
  | .defnInfo d => Json.mkObj [
      ("valueExported", toJson true),
      ("safety", toJson (reprStr d.safety))]
  | .axiomInfo a => Json.mkObj [("isUnsafe", toJson a.isUnsafe)]
  | .opaqueInfo o => Json.mkObj [
      ("valueExported", toJson false),
      ("isUnsafe", toJson o.isUnsafe)]
  | .inductInfo i => Json.mkObj [
      ("numParams", toJson i.numParams),
      ("numIndices", toJson i.numIndices),
      ("all", toJson (i.all.map Name.toString)),
      ("constructors", toJson (i.ctors.map Name.toString)),
      ("numNested", toJson i.numNested),
      ("isRecursive", toJson i.isRec),
      ("isUnsafe", toJson i.isUnsafe),
      ("isReflexive", toJson i.isReflexive)]
  | .ctorInfo c => Json.mkObj [
      ("inductive", toJson c.induct.toString),
      ("constructorIndex", toJson c.cidx),
      ("numParams", toJson c.numParams),
      ("numFields", toJson c.numFields),
      ("isUnsafe", toJson c.isUnsafe)]
  | .recInfo r => Json.mkObj [
      ("all", toJson (r.all.map Name.toString)),
      ("numParams", toJson r.numParams),
      ("numIndices", toJson r.numIndices),
      ("numMotives", toJson r.numMotives),
      ("numMinors", toJson r.numMinors),
      ("rules", recursorRulesJson r),
      ("supportsK", toJson r.k),
      ("isUnsafe", toJson r.isUnsafe)]
  | .quotInfo _ => Json.mkObj []

def publicName? (value : String) : Option Name :=
  let parts := value.splitOn "."
  if parts.isEmpty || !parts.all (fun part => !part.isEmpty && part.toList.all (fun c =>
      (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
      (c >= '0' && c <= '9') || c == '_' || c == '\'')) then
    none
  else
    let name := parts.foldl Name.str Name.anonymous
    if name.toString == value then some name else none

def resolvePublicRequest (env : Environment) (request : StructuralRequest) : MetaM Name := do
  let some name := publicName? request.expectedPublicName |
    throwError "Structural snapshot rejects an ambiguous public Name: {request.expectedPublicName}"
  unless (Lean.privateToUserName? name).isNone do
    throwError "Structural snapshot resolved a private kernel Name: {name}"
  let some _ := env.find? name |
    throwError "Structural snapshot declaration is absent: {name}"
  let some moduleName := moduleFor? env name |
    throwError "Structural snapshot declaration has no module owner: {name}"
  unless moduleName.toString == request.expectedModule do
    throwError "Structural snapshot declaration has the wrong module owner: {name}"
  return name

def familyReferencesJson
    (env : Environment) (request : StructuralRequest) (ci : ConstantInfo) : MetaM Json := do
  let mut names := exprNames ci.type
  if let .recInfo r := ci then
    for rule in r.rules do
      names := exprNames rule.rhs ++ names
  let familyNames := uniqueSortedNames <| names.filter (isFamilyName request.familyRoot)
  let mut rows : Array Json := #[]
  for name in familyNames do
    let some refCi := env.find? name |
      throwError "Structural family reference is absent: {name}"
    let some moduleName := moduleFor? env name |
      throwError "Structural family reference has no module owner: {name}"
    unless moduleName.toString == request.expectedModule do
      throwError "Structural family reference has the wrong module owner: {name}"
    rows := rows.push <| Json.mkObj [
      ("name", toJson name.toString),
      ("module", toJson moduleName.toString),
      ("envKind", toJson (envKind refCi))]
  return Json.arr rows

def transitiveStructuralNamesJson
    (env : Environment) (request : StructuralRequest) (name : Name)
    (ci : ConstantInfo) : MetaM Json := do
  let names := if (directStructuralNames ci).isEmpty then []
    else structuralClosure env (name :: directStructuralNames ci)
  let mut rows : Array Json := #[]
  for refName in names do
    let some refCi := env.find? refName |
      throwError "Transitive structural declaration is absent: {refName}"
    let some moduleName := moduleFor? env refName |
      throwError "Transitive structural declaration has no module owner: {refName}"
    unless moduleName.toString == request.expectedModule do
      throwError "Transitive structural declaration has the wrong module owner: {refName}"
    rows := rows.push <| Json.mkObj [
      ("name", toJson refName.toString),
      ("module", toJson moduleName.toString),
      ("envKind", toJson (envKind refCi))]
  return Json.arr rows

def exportStructuralSnapshotJsonl
    (requests : Array StructuralRequest) (output : String) : MetaM Unit := do
  let env ← getEnv
  let handle ← IO.FS.Handle.mk output .write
  for request in requests do
    let name ← resolvePublicRequest env request
    let some ci := env.find? name |
      throwError "Resolved structural snapshot declaration is absent: {name}"
    let actualKind := envKind ci
    unless actualKind == request.graphKind do
      throwError "Structural snapshot kind mismatch for {name}: graph={request.graphKind}, env={actualKind}"
    unless isClosed ci.type do
      throwError "Structural snapshot type is not closed: {name}"
    let value := match ci with
      | .defnInfo d => some d.value
      | _ => none
    if let some v := value then
      unless isClosed v do
        throwError "Structural snapshot definition value is not closed: {name}"
    if let .recInfo r := ci then
      for rule in r.rules do
        unless hasNoFreeOrMetaVars rule.rhs do
          throwError "Structural snapshot recursor rule has a free or metavariable: {name}"
    let axioms ← Lean.collectAxioms name
    let axiomNames := axioms.toList.map Name.toString
      |>.mergeSort (fun a b => compare a b == .lt)
    let familyReferences ← familyReferencesJson env request ci
    let transitiveNames ← transitiveStructuralNamesJson env request name ci
    let row := Json.mkObj [
      ("schemaVersion", toJson 2),
      ("kernelMetadataSchema", toJson "lean-4.33.1-ConstantInfo-complete-v1"),
      ("sourceName", toJson request.sourceName),
      ("resolvedName", toJson name.toString),
      ("sourceModule", toJson request.expectedModule),
      ("declGraphSha256", toJson request.declGraphSha256),
      ("declGraphRowSha256", toJson request.declGraphRowSha256),
      ("graphKind", toJson request.graphKind),
      ("envKind", toJson actualKind),
      ("ownerKind", toJson request.ownerKind),
      ("ownerId", toJson request.ownerId),
      ("commandUnit", toJson request.commandUnit),
      ("familyRoot", toJson request.familyRoot),
      ("levelParams", toJson (ci.levelParams.map Name.toString)),
      ("closedType", toJson true),
      ("closedValue", value.map (fun _ => toJson true) |>.getD Json.null),
      ("type", exprJson ci.type),
      ("value", value.map exprJson |>.getD Json.null),
      ("axioms", toJson axiomNames),
      ("kindMetadata", completeKernelMetadata ci),
      ("familyReferences", familyReferences),
      ("transitiveNames", transitiveNames)]
    handle.putStrLn row.compress
  handle.flush

end PiExponentStructuralKernelSnapshot
/- Pure future-provider probe specification. No Lean invocation has validated this file yet. -/
namespace LiteralAnalyticInterfaceOwnedInventory
open Lean Meta PiExponentStructuralKernelSnapshot

def exportInventory (anchor : Name) (moduleName output : String) : MetaM Unit := do
  let env ← getEnv
  let some wantedIndex := env.getModuleIdxFor? anchor
    | throwError "Interface data anchor does not have an imported provider owner"
  unless env.header.moduleNames[wantedIndex.toNat]?.map Name.toString == some moduleName do
    throwError "Interface data anchor imported owner differs from the exact provider"
  -- Every constant is enumerated. Only the owner index is inspected before
  -- filtering; name strings and expressions are exported only for matches.
  let mut found : Array (Name × ConstantInfo) := #[]
  for (name, ci) in env.constants.toList do
    if env.getModuleIdxFor? name == some wantedIndex then
      found := found.push (name, ci)
  found := found.qsort (fun a b => a.1.toString < b.1.toString)
  let mut rows : Array Json := #[]
  for (name, ci) in found do
    let value := match ci with
      | .defnInfo d => some d.value
      | .thmInfo t => some t.value
      | _ => none
    rows := rows.push <| Json.mkObj [
      ("name",toJson name.toString),("owner",toJson moduleName),
      ("ownerModuleIndex",toJson wantedIndex.toNat),
      ("privateUserName",toJson ((Lean.privateToUserName? name).map Name.toString)),
      ("kind",toJson (envKind ci)),("levelParams",toJson (ci.levelParams.map Name.toString)),
      ("closedType",toJson (isClosed ci.type)),("closedValue",toJson (value.map isClosed)),
      ("isProp",toJson (← isProp ci.type)),("type",exprJson ci.type),
      ("value",value.map exprJson |>.getD Json.null),
      ("typeRefs",toJson ((uniqueSortedNames (exprNames ci.type)).map Name.toString)),
      ("valueRefs",toJson ((uniqueSortedNames (value.map exprNames |>.getD [])).map Name.toString)),
      ("axioms",toJson ((← Lean.collectAxioms name).toList.map Name.toString
        |>.mergeSort (fun a b => compare a b == .lt)))]
  IO.FS.writeFile output <| (Json.mkObj [("schemaVersion",toJson (1 : Nat)),
    ("probeMainModule",toJson env.mainModule.toString),("providerModule",toJson moduleName),
    ("anchor",toJson anchor.toString),("providerModuleIndex",toJson wantedIndex.toNat),
    ("inventorySelection",toJson "all constants, exact imported owner index before name conversion"),
    ("rawOwnedCIs",Json.arr rows)]).compress

end LiteralAnalyticInterfaceOwnedInventory


namespace LiteralInterfaceUsedProofInventory
open Lean Meta PiExponentStructuralKernelSnapshot
def exportUsedProofs (roots : Array Name) (allowedOwners : Array String) (output : String) : MetaM Unit := do
  let env ← getEnv
  let mut todo : List Name := []
  for name in roots do
    let ci ← getConstInfo name
    let value := match ci with
      | .defnInfo d => some d.value
      | .thmInfo t => some t.value
      | _ => none
    todo := exprNames ci.type ++ (value.map exprNames |>.getD []) ++ todo
  let mut seen : List Name := []
  let mut rows : Array Json := #[]
  while !todo.isEmpty do
    let name := todo.head!
    todo := todo.tail!
    if seen.contains name then continue
    seen := name :: seen
    let some ci := env.find? name | continue
    let some owner := moduleFor? env name | continue
    if !allowedOwners.contains owner.toString then continue
    let .thmInfo t := ci | continue
    todo := exprNames ci.type ++ exprNames t.value ++ todo
    rows := rows.push <| Json.mkObj [
      ("name",toJson name.toString),("owner",toJson owner.toString),
      ("privateUserName",toJson ((Lean.privateToUserName? name).map Name.toString)),
      ("kind",toJson (envKind ci)),("levelParams",toJson (ci.levelParams.map Name.toString)),
      ("closedType",toJson (isClosed ci.type)),("closedValue",toJson (isClosed t.value)),
      ("isProp",toJson (← isProp ci.type)),("type",exprJson ci.type),("value",exprJson t.value),
      ("typeRefs",toJson ((uniqueSortedNames (exprNames ci.type)).map Name.toString)),
      ("valueRefs",toJson ((uniqueSortedNames (exprNames t.value)).map Name.toString)),
      ("axioms",toJson ((← Lean.collectAxioms name).toList.map Name.toString |>.mergeSort (fun a b => compare a b == .lt)))]
  IO.FS.writeFile output <| (Json.mkObj [("schemaVersion",toJson (1 : Nat)),
    ("probeMainModule",toJson env.mainModule.toString),("roots",toJson (roots.toList.map Name.toString)),
    ("allowedOwners",toJson allowedOwners),("actualUsedProofCIs",Json.arr rows)]).compress
end LiteralInterfaceUsedProofInventory

open PiExponentStructuralKernelSnapshot
def literalInterfaceRequests : Array StructuralRequest := #[
    { sourceName := "OAI.PiExponent.LiteralAnalytic.beta", expectedPublicName := "OAI.PiExponent.LiteralAnalytic.beta", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData", graphKind := "def", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "608a25b1ec2f80f2ed343b0eb1db098bef35ff22803ddac1f2e05e9d7b294e0c", ownerKind := "definition", ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:603", commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:603", familyRoot := "OAI.PiExponent.LiteralAnalytic.beta" },
    { sourceName := "OAI.PiExponent.LiteralAnalytic.fixedWeights", expectedPublicName := "OAI.PiExponent.LiteralAnalytic.fixedWeights", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData", graphKind := "def", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "4b29a7f620bcd45892c06cb30f7df96611add4d42f724b410a65cb7b0848218d", ownerKind := "definition", ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:337", commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:337", familyRoot := "OAI.PiExponent.LiteralAnalytic.fixedWeights" },
    { sourceName := "OAI.PiExponent.MatrixTranslation.periodCoordinate", expectedPublicName := "OAI.PiExponent.MatrixTranslation.periodCoordinate", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData", graphKind := "def", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "25cf7e497f7a9c8bd12da4dad7c421acf2fdc2ff3617a728a93ef1e7a8ce9325", ownerKind := "definition", ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:264", commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:264", familyRoot := "OAI.PiExponent.MatrixTranslation.periodCoordinate" },
    { sourceName := "OAI.PiExponent.MatrixTranslation.transverseIndices", expectedPublicName := "OAI.PiExponent.MatrixTranslation.transverseIndices", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData", graphKind := "def", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "c6cfe56913921e51b061d1b65d25f7fb23a4d9fd4e04b5a47b355592b769ef8f", ownerKind := "definition", ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:2572", commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:2572", familyRoot := "OAI.PiExponent.MatrixTranslation.transverseIndices" },
    { sourceName := "OAI.PiExponent.MatrixTranslationBounds.weight", expectedPublicName := "OAI.PiExponent.MatrixTranslationBounds.weight", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData", graphKind := "def", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "bb82124642a4b1d3a2c91747b2d4afc1e30c257bc433bb99e07766057dcde619", ownerKind := "definition", ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds:316", commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds:316", familyRoot := "OAI.PiExponent.MatrixTranslationBounds.weight" },
    { sourceName := "OAI.PiExponent.RowTranslation.RowChoices", expectedPublicName := "OAI.PiExponent.RowTranslation.RowChoices", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData", graphKind := "def", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "98def1acefd799e100d4889e9d9f1fa635991d2726dd3f4bfa52ea6ce4936bfb", ownerKind := "definition", ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:10668", commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:10668", familyRoot := "OAI.PiExponent.RowTranslation.RowChoices" },
    { sourceName := "OAI.PiExponent.RowTranslation.rowScalar", expectedPublicName := "OAI.PiExponent.RowTranslation.rowScalar", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData", graphKind := "def", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "25e6fd5a6123637169e5cbf6ce748019c0a0e5bae583742016ef7ce609548f84", ownerKind := "definition", ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:7272", commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:7272", familyRoot := "OAI.PiExponent.RowTranslation.rowScalar" },
    { sourceName := "OAI.PiExponent.RowTranslation.tail", expectedPublicName := "OAI.PiExponent.RowTranslation.tail", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData", graphKind := "def", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "864a826c6d1078095926e1c88bdca809500d27fb0702b18adfd18fc633157061", ownerKind := "definition", ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:12851", commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:12851", familyRoot := "OAI.PiExponent.RowTranslation.tail" },
    { sourceName := "OAI.PiExponent.logarithmicPeriod", expectedPublicName := "OAI.PiExponent.logarithmicPeriod", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData", graphKind := "def", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "865991db65d4ff0e74db78071749ee0e0524912f3fc1167b50a4ce88d6b58d70", ownerKind := "definition", ownerId := "OAI.NumberTheory.PiExponent.Approximation.ApproximationCenters:809", commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ApproximationCenters:809", familyRoot := "OAI.PiExponent.logarithmicPeriod" },
    { sourceName := "OAI.PiExponent.LiteralAnalytic.RowChoice", expectedPublicName := "OAI.PiExponent.LiteralAnalytic.RowChoice", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData", graphKind := "def", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "f6a1aac4ada433b06f78455a6aac6bade0262fc0e5fa7e7d49b5f923523dd191", ownerKind := "definition", ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:769", commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:769", familyRoot := "OAI.PiExponent.LiteralAnalytic.RowChoice" },
    { sourceName := "OAI.PiExponent.LiteralAnalytic.Transverse", expectedPublicName := "OAI.PiExponent.LiteralAnalytic.Transverse", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData", graphKind := "def", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "7aea9a44c618ec4631fe725aef3c4f83d6426ac872d6611cbcb590c9c8d2ee52", ownerKind := "definition", ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:476", commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:476", familyRoot := "OAI.PiExponent.LiteralAnalytic.Transverse" },
    { sourceName := "OAI.PiExponent.LiteralAnalytic.rowWeight", expectedPublicName := "OAI.PiExponent.LiteralAnalytic.rowWeight", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData", graphKind := "def", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "0f58ced87748ddf24c170db5e3c3720941ffe7a3c96ad374d10f677490aeae56", ownerKind := "definition", ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:1231", commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:1231", familyRoot := "OAI.PiExponent.LiteralAnalytic.rowWeight" },
    { sourceName := "OAI.PiExponent.MatrixTranslation.periodMonomial", expectedPublicName := "OAI.PiExponent.MatrixTranslation.periodMonomial", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData", graphKind := "def", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "00f510252ddb80f83f5274bf860cdd2cab858352b1ba8b60d63131111a111d39", ownerKind := "definition", ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:400", commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:400", familyRoot := "OAI.PiExponent.MatrixTranslation.periodMonomial" },
    { sourceName := "OAI.PiExponent.LiteralAnalytic.ChoiceFamily", expectedPublicName := "OAI.PiExponent.LiteralAnalytic.ChoiceFamily", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData", graphKind := "def", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "b7b1350437fa43d4ab26e3ed927378f14bc9c91d45704e1b313e594ad3de8b84", ownerKind := "definition", ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:958", commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:958", familyRoot := "OAI.PiExponent.LiteralAnalytic.ChoiceFamily" },
    { sourceName := "OAI.PiExponent.LiteralAnalytic.choiceScalar", expectedPublicName := "OAI.PiExponent.LiteralAnalytic.choiceScalar", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData", graphKind := "def", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "507a33206cb63d56844c4a38759a210534ae125391cc9bbf7c419fdac9d9316f", ownerKind := "definition", ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:1398", commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:1398", familyRoot := "OAI.PiExponent.LiteralAnalytic.choiceScalar" },
    { sourceName := "OAI.PiExponent.LiteralAnalytic.indexWeight", expectedPublicName := "OAI.PiExponent.LiteralAnalytic.indexWeight", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData", graphKind := "def", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "bb47aeb8669913e86bc7c043796eda1d557392970f58669d029e4ddae37f2a8e", ownerKind := "definition", ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:1060", commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:1060", familyRoot := "OAI.PiExponent.LiteralAnalytic.indexWeight" },
    { sourceName := "OAI.PiExponent.LiteralAnalytic.choiceMatrix", expectedPublicName := "OAI.PiExponent.LiteralAnalytic.choiceMatrix", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData", graphKind := "def", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "c4a7b640b29655532e726da4123b2de64473dc4b6632e1f9ce521b88b818f7f9", ownerKind := "definition", ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:1862", commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:1862", familyRoot := "OAI.PiExponent.LiteralAnalytic.choiceMatrix" }
]

run_meta do
  LiteralAnalyticInterfaceOwnedInventory.exportInventory `OAI.PiExponent.LiteralAnalytic.choiceMatrix "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData" "missions/pi-irrationality-measure/verification/ap20/literal-interface-data/actual-owned-CI-inventory.json"
  LiteralInterfaceUsedProofInventory.exportUsedProofs #[`OAI.PiExponent.LiteralAnalytic.beta, `OAI.PiExponent.LiteralAnalytic.fixedWeights, `OAI.PiExponent.MatrixTranslation.periodCoordinate, `OAI.PiExponent.MatrixTranslation.transverseIndices, `OAI.PiExponent.MatrixTranslationBounds.weight, `OAI.PiExponent.RowTranslation.RowChoices, `OAI.PiExponent.RowTranslation.rowScalar, `OAI.PiExponent.RowTranslation.tail, `OAI.PiExponent.logarithmicPeriod, `OAI.PiExponent.LiteralAnalytic.RowChoice, `OAI.PiExponent.LiteralAnalytic.Transverse, `OAI.PiExponent.LiteralAnalytic.rowWeight, `OAI.PiExponent.MatrixTranslation.periodMonomial, `OAI.PiExponent.LiteralAnalytic.ChoiceFamily, `OAI.PiExponent.LiteralAnalytic.choiceScalar, `OAI.PiExponent.LiteralAnalytic.indexWeight, `OAI.PiExponent.LiteralAnalytic.choiceMatrix] #["Definitions.Def_OAI_NumberTheory_PiExponent_Ampleness_NefAmple", "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData", "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticCollision", "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_Collision", "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_CollisionCombinatorics_Multiplicity", "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_FormalLogTruncation", "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData", "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LogTailAnalytic", "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_AdmissibleParameters", "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Arithmetic", "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CollisionConstant", "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData", "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_CoreData", "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_Domains", "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_MatrixArithmetic_CoreData", "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_MatrixArithmetic_ScalesCosts", "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Parameters", "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_RowTranslation_CoreData", "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_SuccessiveApproximations", "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_WeightSeparation", "Definitions.Def_OAI_NumberTheory_PiExponent_Jets_FormalJetDerivatives", "Definitions.Def_OAI_NumberTheory_PiExponent_Jets_FormalLogJet", "Definitions.Def_OAI_NumberTheory_PiExponent_Jets_JetGeometry", "Definitions.Def_OAI_NumberTheory_PiExponent_LocalAlgebra_Dimension", "Definitions.Def_OAI_NumberTheory_PiExponent_LocalAlgebra_LocalizedComponent", "Definitions.Def_OAI_NumberTheory_PiExponent_LocalAlgebra_QuotientLengthEquivalence", "Definitions.Def_OAI_NumberTheory_PiExponent_LocalAlgebra_RegularDegreePositivity", "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_PolynomialFrame", "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_PolynomialFrameDegree", "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexCounting_WeightedDomains", "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexFloor", "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexUnweighted"] "missions/pi-irrationality-measure/verification/ap20/literal-interface-data/generated-used-proof-CIs.json"
  exportStructuralSnapshotJsonl literalInterfaceRequests "missions/pi-irrationality-measure/verification/ap20/literal-interface-data/generated-full-ci.jsonl"

#print axioms OAI.PiExponent.LiteralAnalytic.beta
#print axioms OAI.PiExponent.LiteralAnalytic.fixedWeights
#print axioms OAI.PiExponent.MatrixTranslation.periodCoordinate
#print axioms OAI.PiExponent.MatrixTranslation.transverseIndices
#print axioms OAI.PiExponent.MatrixTranslationBounds.weight
#print axioms OAI.PiExponent.RowTranslation.RowChoices
#print axioms OAI.PiExponent.RowTranslation.rowScalar
#print axioms OAI.PiExponent.RowTranslation.tail
#print axioms OAI.PiExponent.logarithmicPeriod
#print axioms OAI.PiExponent.LiteralAnalytic.RowChoice
#print axioms OAI.PiExponent.LiteralAnalytic.Transverse
#print axioms OAI.PiExponent.LiteralAnalytic.rowWeight
#print axioms OAI.PiExponent.MatrixTranslation.periodMonomial
#print axioms OAI.PiExponent.LiteralAnalytic.ChoiceFamily
#print axioms OAI.PiExponent.LiteralAnalytic.choiceScalar
#print axioms OAI.PiExponent.LiteralAnalytic.indexWeight
#print axioms OAI.PiExponent.LiteralAnalytic.choiceMatrix
