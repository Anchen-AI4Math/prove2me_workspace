import Lean
import OAI.NumberTheory.PiExponent.Main

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
  Json.arr <| r.rules.map (fun rule => Json.mkObj [
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
  let names := uniqueSortedNames <| names.filter (isFamilyName request.familyRoot)
  let mut rows : Array Json := #[]
  for name in names do
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

def structuralSourceRequests : Array StructuralRequest := #[
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "inductive",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0fe91777471b27fdcbaa7b95e79c76540e1450df365beac95969f9a316b777a4",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.F0",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.F0",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6e07a788a03a732dc4d1e040955770fd5dce26eb544acb52f9d2baf8fd80b4e9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.F0_large",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.F0_large",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a63277f0cc4969bcdeddd96ec0aff89d63ec48e4c08b128d189d4f479de88688",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.F0_pos",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.F0_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "553f377f8fd6260a4647d1fde5b80befc341fd529bd0639649274dea377aee03",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.K",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.K",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2c50c7f2a73bb2f01dd7ee4d82c998476d96cdf82131cccbaa649a9563a1a536",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.K_eq",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.K_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d833b53cf385eb31443810a0560999e1cbd3b2b4d9cb974dc64ca988f3f85ad1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.K_pos",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.K_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "216944eb3c56c3614cd00d008cd63591465c2efce4e273c78b5076f0942d0c1d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.approximations",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.approximations",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aaf73660ca7aea3de373bc2aea43f228eb9b222afa662a5985f31ad91181d76f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.base",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.base",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0870767dac60e9e015d91e1c6914268fc5a75193947844383f584e4e3c3db6ff",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.casesOn",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.casesOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fb122f4f0b80a12f44aed313a371e2c56be9d5ba5dc4d3df903cf2b680cfc844",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.collision_margin",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.collision_margin",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "84bfa8e68dd1fbbf7f77c61a6f9bce064330677ec6dab08880f47f592dd34a85",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.dimension_margin",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.dimension_margin",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3d7c12295ae9dd15a57f1098be6fa89b7e2e995b6f2a9f9de6dfedcc5e05272e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.epsilon",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.epsilon",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "997dda484fc9c6c4df59258ead4b0ff48858ffe1475a073e41c0cd72252b4f58",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.epsilon_le_half",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.epsilon_le_half",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "756dbf6888b3abca3143363014fc938bd426f0f2868d9a863a1aed944a8c038d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.epsilon_lt_gap",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.epsilon_lt_gap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7a52307cc27628e9b08d4d04119a3177104542c20f1044410cc57345606b7659",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.epsilon_pos",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.epsilon_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5f557f266f5920f3d5fc0707f350aeb0a5b3efe05f752ec73db0e8bb017a5ad0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.initial_margin",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.initial_margin",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f4484806a112aacdf4dab4967f6b000a7d9903322fc1701926a072aec2a7d0ac",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.m",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.m",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d4e9015c664f68ec0c8f884e95478c645cc4ef2efa5bd838abfe68a26fd517b2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.m_pos",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.m_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e49fec9450acb197928cf9bc6fca97d2cb0d30e439d5535a37dcbaf14688fe15",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.mk",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.mk",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "ctor",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b6aa2511d0b6f5dbb66c13f080c9c0590a22109e32b6e0247172b69926d230d0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.mk.noConfusion",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.mk.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f0a96c772cb0ab288855a6f878530c95d700c41b0512fb76e1fa67a2353ab193",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.noConfusion",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aa7fdd7013b61ead06aac1f276f8e2efdbdd2de06fe6888ea9736f5c2e4b165c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.p",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.p",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "24ae95a144f64ded836576d32841423aed8e60ca95849a20a64a4cf3510d88a5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.q",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.q",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8a274dd3132e9589f81d6918a3b40b4f60926b66d529ff5a107c6f86e86cc07e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.rec",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.rec",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "rec",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "461cc675fd598d7e69d803076ca99f3af3bef39f77604eef020d5756f667f3cb",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.recOn",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.recOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a2cb066747349fec5c889a6cd3cca90bc9336979714dc20a5b940f39fc13cab9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.sigma",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.sigma",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "62d01aef6f0c6b7ee934e98163dce70b2e73f7d31d485b9c49c9629d032228b2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.sigma_centers",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.sigma_centers",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "49aab0fe8796f41c5417ffe2d03b4acfb3c47412d09c32ea7dd8446a040c1923",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.sigma_pos",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.sigma_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fe2038c34541e78771cb77ebb9e21ea1241e5739b2fa077d48e26c0a59439612",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.sigma_theta",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.sigma_theta",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0226d22e7ed13f7ef3eba3181f4e544bef4747356320d6208f56550107d4d475",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.sigma_volume",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.sigma_volume",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "50b588c2a26c3cf930f6a70903644004bcf3249dc762be28e6b93facf61e72a2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.v0",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.v0",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "32e60970381f16d5084a46d2a82245aae8f8d640737814caf25112d4313e4eef",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.v0_eq",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.v0_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b12ef1a233b168f1cb12db4527acbdf2645a6262ff279decefee033976ee5eba",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.v0_pos",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.v0_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8bf95ea99a27be454eaa8d8814c0764bb6889a9de310911208f5afe60f297f00",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.volume_eq",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.volume_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b694ea149bbe3bbd21c7c0714a8a75bea8ab7fb0097b3903b89be3d065b42684",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.volume_lt_one",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.volume_lt_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fc991d23bfad19356d4212f994b5c778a3d378a0321ce6707b77e9bfbe4eb29a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.w0",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.w0",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cbfb437ac6f8bf3a8b1bb4d016b3f1e7d32ee189902b03e47a98de53c350476a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.w0_eq",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.w0_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e5ed5c83295b807cc0fff10f1627802ebb10e8dafed9b9f98a17a4d8e667f1f9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.w0_pos",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.w0_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4327cae9ef0fec5683a994f6356f67d795d6d4037e20fc0600a3777b20dc027e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.weight_growth",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.weight_growth",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b70db00109afdf3108de8a0373186561041683d8a5f744aabb9227dd5fb30c10",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.weight_margin",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.weight_margin",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "82ff198ada4b33c69b15be674e29b6cc3b960abfb7cafcf500ca829c8f75cd48",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.wstar",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.wstar",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f46018696e8cc4bb9d9fa60c4bfe11903d42a69bc02a72a9f6cae52ec6585737",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.wstar_attained",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.wstar_attained",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ae3b89dd0a91d663f9c7c60d7a9ad66729ca607ed5ec6ab7d7d8a5ce15495f9d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.wstar_lower",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.wstar_lower",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b8962fd7410292f589961d06a99202a07da45f196583ee3ec28702888ddba6ff",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.wstar_pos",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.wstar_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c303662deee1ea3a9d16246be9f19130a51f8b418777f342701cdd4714d76697",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.x",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.x",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3d2fb4c0ac87c30c17e50e74f7a3511ca4fc004fa976b575df9c80edccd60540",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.x_log",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.x_log",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b91a285cb298905184148e0e3eec7df492fb5ad914a0c0df2a8b915d6783e61b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.x_one_le",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.x_one_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "60716a30d4c06faa34f980b218a5b69cefe2538b9fd24218ab7f730572c2f912",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.x_zero",
      expectedPublicName := "OAI.PiExponent.AdmissibleParameters.x_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1a3642ca8c261b85a664a129811d130c65c7971b4d5820ce584f94db33942d69",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      familyRoot := "OAI.PiExponent.AdmissibleParameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters",
      expectedPublicName := "OAI.PiExponent.Parameters",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "inductive",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1959ebb3f2aea65f610a6dccebb1d76370724d77f59615a8613f6fde38207407",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.A",
      expectedPublicName := "OAI.PiExponent.Parameters.A",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a4b59a8b4862dd1436e6b185c6ad40d37c8a10bf6b7128048cbdff8c4ba8d1c5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.A_lt_B",
      expectedPublicName := "OAI.PiExponent.Parameters.A_lt_B",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "104640a061689cc71fe999651e3c55424ecf9a4e77ecd24cc21c0769b0f4970c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.A_pos",
      expectedPublicName := "OAI.PiExponent.Parameters.A_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e48c067080464a6cdb88ca55f08a0eb904b2d7cc9fe26638ff1062af38950cb6",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:5380",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:5380",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.B",
      expectedPublicName := "OAI.PiExponent.Parameters.B",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ce4bf30b3ed54f9be5151c2a8405547f6049288790361cbc1dcbf2fca8ece291",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.B_lt_C_theta",
      expectedPublicName := "OAI.PiExponent.Parameters.B_lt_C_theta",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8321e192bb45c64f18380c423651fdaf474e0ebcc1e0d827e539199d8c59592f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.B_lt_inv_C",
      expectedPublicName := "OAI.PiExponent.Parameters.B_lt_inv_C",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "93c64801fdd7a5307b83f52be8c091143d8da52d2d5b9011a879767655e555c1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.B_lt_one",
      expectedPublicName := "OAI.PiExponent.Parameters.B_lt_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "692e10f8930e2164c2799f0e0b4727a1fee6feb0770a8ec33e6bf53ca834a61f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.C",
      expectedPublicName := "OAI.PiExponent.Parameters.C",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "78f8bfd96546f52acaa6ecc5403daacbd937489beb030bcd3667d170ea4230c9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.C_theta_lt_one",
      expectedPublicName := "OAI.PiExponent.Parameters.C_theta_lt_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9c1e892f80d53d1583368c914bd05959fba4da7100a7c59b921c4ed990099270",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.approximation_gap",
      expectedPublicName := "OAI.PiExponent.Parameters.approximation_gap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fd561b73e671cc3c7dec530c3242cbcd45a158917a9a2427bfb700951d1a8206",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.casesOn",
      expectedPublicName := "OAI.PiExponent.Parameters.casesOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "414e266917c5ab0795344618c5171503fbe89f8fd4de3f4c795e862355a05d13",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.eta",
      expectedPublicName := "OAI.PiExponent.Parameters.eta",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "91809a058c30f17b25f47973836bfcb627bbf45aa2b5d7a58df2b495bc848f0a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.eta_lt_one",
      expectedPublicName := "OAI.PiExponent.Parameters.eta_lt_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "083f67995d6b489dd477f85539829ae0f909e017b7b2ae98d79c97d17bc86a1b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.eta_pos",
      expectedPublicName := "OAI.PiExponent.Parameters.eta_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b7ad4122c2a230b73caa0b6389cc6104fb061ab5dfefa3e9b39bc3605a8f3628",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.gap_pos",
      expectedPublicName := "OAI.PiExponent.Parameters.gap_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "df664f2d63b6b8c38fc17236e4ce5feafffd4c8434f85135c3d44d2f63d9c3e3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.mk",
      expectedPublicName := "OAI.PiExponent.Parameters.mk",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "ctor",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "96d047fab06b0c5b26def512360adacb9bb5b285bede888273d0adac5e69b4c8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.mk.noConfusion",
      expectedPublicName := "OAI.PiExponent.Parameters.mk.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5117ffeec9d4cc0dc67cba1eee378f06f6fd17e0dd45e3de66fac5f2bedb08eb",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.noConfusion",
      expectedPublicName := "OAI.PiExponent.Parameters.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ca392e756dc60c8923068c5514391b33470b162a7fa98ddc6dfc600189b73e01",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.one_lt_C",
      expectedPublicName := "OAI.PiExponent.Parameters.one_lt_C",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "08c66cfec231332f79f5b9beafcd9b4ea3c7a3cae7659f61081d63a749aa054b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.rec",
      expectedPublicName := "OAI.PiExponent.Parameters.rec",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "rec",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2bc2f50c6fc2cd9b3b010eb22618c5ccda2dbeb9f070da768579876195eebb37",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.recOn",
      expectedPublicName := "OAI.PiExponent.Parameters.recOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "55b2878abd89a225fa453669d093e9984dc054e329e650f35e579ed91ebc1c53",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.theta",
      expectedPublicName := "OAI.PiExponent.Parameters.theta",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "31398ad0ca6bea5cd9f9a5281e73a6e514e34bfa9d100ab9b0137324edb592a5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.theta_lt_A",
      expectedPublicName := "OAI.PiExponent.Parameters.theta_lt_A",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d4abb8c9fb3d254317e4b080b65a01f32f13042a1beccbbb9bc66c8dbe48cac3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.theta_pos",
      expectedPublicName := "OAI.PiExponent.Parameters.theta_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "72465333cd1627e9ed4b04f240468bea82c752fa5eef9be02d37292c22a7a2bf",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    }
  ]

run_meta do
  exportStructuralSnapshotJsonl structuralSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/structural-kernel-74/StructuralKernelSource_000.jsonl"
