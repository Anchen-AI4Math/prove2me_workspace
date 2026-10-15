import Lean
import OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction

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

open PiExponentStructuralKernelSnapshot

def weightedDomainRequests : Array StructuralRequest := #[
    { sourceName := "OAI.PiExponent.DeterminantContradiction.FixedData", expectedPublicName := "OAI.PiExponent.DeterminantContradiction.FixedData", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction", graphKind := "def", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "121224e4a278e93b89f07eebcde883b9f77b943b3aceef201dd82c735f11504b", ownerKind := "definition", ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:677", commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:677", familyRoot := "OAI.PiExponent.DeterminantContradiction.FixedData" },
    { sourceName := "OAI.PiExponent.DeterminantContradiction.finiteNumerators", expectedPublicName := "OAI.PiExponent.DeterminantContradiction.finiteNumerators", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction", graphKind := "def", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "881d847e91466f3a5e9d02b59051247374f1ba923f2b2a731d861488931a6110", ownerKind := "definition", ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:776", commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:776", familyRoot := "OAI.PiExponent.DeterminantContradiction.finiteNumerators" },
    { sourceName := "OAI.PiExponent.DeterminantContradiction.finiteDenominators", expectedPublicName := "OAI.PiExponent.DeterminantContradiction.finiteDenominators", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction", graphKind := "def", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "07144205a73259ce61ef5436ceafade674483476fe4e75c2f61202ce36998ade", ownerKind := "definition", ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:887", commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:887", familyRoot := "OAI.PiExponent.DeterminantContradiction.finiteDenominators" },
    { sourceName := "OAI.PiExponent.DeterminantContradiction.Row", expectedPublicName := "OAI.PiExponent.DeterminantContradiction.Row", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction", graphKind := "def", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "bd10ee494ae0d521d267cc74ad5168ac0bcde905a98dffe617198da4ffb4cee7", ownerKind := "definition", ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:1321", commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:1321", familyRoot := "OAI.PiExponent.DeterminantContradiction.Row" },
    { sourceName := "OAI.PiExponent.DeterminantContradiction.Column", expectedPublicName := "OAI.PiExponent.DeterminantContradiction.Column", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction", graphKind := "def", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "d254537eeec190a12d8ff0ce95e052da1f9a345a68563291203cd32d1183cf36", ownerKind := "definition", ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:1487", commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:1487", familyRoot := "OAI.PiExponent.DeterminantContradiction.Column" },
    { sourceName := "OAI.PiExponent.DeterminantContradiction.actualMatrix", expectedPublicName := "OAI.PiExponent.DeterminantContradiction.actualMatrix", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction", graphKind := "def", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "c596b19a391f6687196e929f09f6f23874aaee52b5c16552ba7a24037956af5c", ownerKind := "definition", ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:1637", commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:1637", familyRoot := "OAI.PiExponent.DeterminantContradiction.actualMatrix" },
    { sourceName := "OAI.PiExponent.DeterminantContradiction.actualMinor", expectedPublicName := "OAI.PiExponent.DeterminantContradiction.actualMinor", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction", graphKind := "def", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "a28bf2bbe2b0e0f95c74f5a963edb00130a88fb224af1797083b0bf5a059a47f", ownerKind := "definition", ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:2042", commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:2042", familyRoot := "OAI.PiExponent.DeterminantContradiction.actualMinor" },
    { sourceName := "OAI.PiExponent.DeterminantContradiction.actualMean", expectedPublicName := "OAI.PiExponent.DeterminantContradiction.actualMean", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction", graphKind := "def", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "a6f2fbaca54c085fa54fb9973ba9b8a2eeb74448de555ce17d611b4a24cbe42f", ownerKind := "definition", ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:2320", commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:2320", familyRoot := "OAI.PiExponent.DeterminantContradiction.actualMean" },
    { sourceName := "OAI.PiExponent.DeterminantContradiction.actualRowCount", expectedPublicName := "OAI.PiExponent.DeterminantContradiction.actualRowCount", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction", graphKind := "def", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "fc4e13f893e5ea9a1732519e8ea9cdce538421d7c2144c95b981b41f3b0f3329", ownerKind := "definition", ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:2482", commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:2482", familyRoot := "OAI.PiExponent.DeterminantContradiction.actualRowCount" },
    { sourceName := "OAI.PiExponent.DeterminantContradiction.lowIndexCount", expectedPublicName := "OAI.PiExponent.DeterminantContradiction.lowIndexCount", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction", graphKind := "def", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "eb03d7e80ca2a1823b7b96c2950a8bd2f905759f858124a87c92c25c762e329b", ownerKind := "definition", ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:2593", commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:2593", familyRoot := "OAI.PiExponent.DeterminantContradiction.lowIndexCount" },
    { sourceName := "OAI.PiExponent.DeterminantContradiction.collisionRate", expectedPublicName := "OAI.PiExponent.DeterminantContradiction.collisionRate", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction", graphKind := "def", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "1f70e5d4eb8de11f7c1960a315425afb988ce51775deb690dc5c0918c57cac46", ownerKind := "definition", ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:2788", commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:2788", familyRoot := "OAI.PiExponent.DeterminantContradiction.collisionRate" },
    { sourceName := "OAI.PiExponent.DeterminantContradiction.collisionLimit", expectedPublicName := "OAI.PiExponent.DeterminantContradiction.collisionLimit", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction", graphKind := "def", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "fbf7d66e807b98c2e715deb8230c9208758198cc7902864abce81c926c009172", ownerKind := "definition", ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:2978", commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:2978", familyRoot := "OAI.PiExponent.DeterminantContradiction.collisionLimit" },
    { sourceName := "OAI.PiExponent.DeterminantContradiction.GlobalInterpolationStatement", expectedPublicName := "OAI.PiExponent.DeterminantContradiction.GlobalInterpolationStatement", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction", graphKind := "def", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "e631ecae0b10fd1511cd84cc1be084d3af8290c040ecfcfe3c84c4e65b48f642", ownerKind := "definition", ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:4399", commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:4399", familyRoot := "OAI.PiExponent.DeterminantContradiction.GlobalInterpolationStatement" },
    { sourceName := "OAI.PiExponent.DeterminantContradiction.AnalyticAggregateStatement", expectedPublicName := "OAI.PiExponent.DeterminantContradiction.AnalyticAggregateStatement", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction", graphKind := "def", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "7ff3637cf679513fca377c20a6da7b76705a89d07054edb7118e964250f295c2", ownerKind := "definition", ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:4587", commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:4587", familyRoot := "OAI.PiExponent.DeterminantContradiction.AnalyticAggregateStatement" }
  ]

run_meta do
  exportStructuralSnapshotJsonl weightedDomainRequests "missions/pi-irrationality-measure/verification/ap10/determinant/source-full-ci.jsonl"

#print axioms OAI.PiExponent.DeterminantContradiction.FixedData
#print axioms OAI.PiExponent.DeterminantContradiction.finiteNumerators
#print axioms OAI.PiExponent.DeterminantContradiction.finiteDenominators
#print axioms OAI.PiExponent.DeterminantContradiction.Row
#print axioms OAI.PiExponent.DeterminantContradiction.Column
#print axioms OAI.PiExponent.DeterminantContradiction.actualMatrix
#print axioms OAI.PiExponent.DeterminantContradiction.actualMinor
#print axioms OAI.PiExponent.DeterminantContradiction.actualMean
#print axioms OAI.PiExponent.DeterminantContradiction.actualRowCount
#print axioms OAI.PiExponent.DeterminantContradiction.lowIndexCount
#print axioms OAI.PiExponent.DeterminantContradiction.collisionRate
#print axioms OAI.PiExponent.DeterminantContradiction.collisionLimit
#print axioms OAI.PiExponent.DeterminantContradiction.GlobalInterpolationStatement
#print axioms OAI.PiExponent.DeterminantContradiction.AnalyticAggregateStatement
