import Lean
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Parameters

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

def structuralGeneratedRequests : Array StructuralRequest := #[
    {
      sourceName := "OAI.PiExponent.Parameters.approximation_gap",
      expectedPublicName := "OAI.PiExponent.Parameters.approximation_gap",
      expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fd561b73e671cc3c7dec530c3242cbcd45a158917a9a2427bfb700951d1a8206",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.one_lt_C",
      expectedPublicName := "OAI.PiExponent.Parameters.one_lt_C",
      expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "08c66cfec231332f79f5b9beafcd9b4ea3c7a3cae7659f61081d63a749aa054b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.C",
      expectedPublicName := "OAI.PiExponent.Parameters.C",
      expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "78f8bfd96546f52acaa6ecc5403daacbd937489beb030bcd3667d170ea4230c9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.mk",
      expectedPublicName := "OAI.PiExponent.Parameters.mk",
      expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Parameters",
      graphKind := "ctor",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "96d047fab06b0c5b26def512360adacb9bb5b285bede888273d0adac5e69b4c8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.B_lt_C_theta",
      expectedPublicName := "OAI.PiExponent.Parameters.B_lt_C_theta",
      expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8321e192bb45c64f18380c423651fdaf474e0ebcc1e0d827e539199d8c59592f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.eta",
      expectedPublicName := "OAI.PiExponent.Parameters.eta",
      expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "91809a058c30f17b25f47973836bfcb627bbf45aa2b5d7a58df2b495bc848f0a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.B",
      expectedPublicName := "OAI.PiExponent.Parameters.B",
      expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ce4bf30b3ed54f9be5151c2a8405547f6049288790361cbc1dcbf2fca8ece291",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.B_lt_inv_C",
      expectedPublicName := "OAI.PiExponent.Parameters.B_lt_inv_C",
      expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "93c64801fdd7a5307b83f52be8c091143d8da52d2d5b9011a879767655e555c1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.eta_pos",
      expectedPublicName := "OAI.PiExponent.Parameters.eta_pos",
      expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b7ad4122c2a230b73caa0b6389cc6104fb061ab5dfefa3e9b39bc3605a8f3628",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.rec",
      expectedPublicName := "OAI.PiExponent.Parameters.rec",
      expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Parameters",
      graphKind := "rec",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2bc2f50c6fc2cd9b3b010eb22618c5ccda2dbeb9f070da768579876195eebb37",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters",
      expectedPublicName := "OAI.PiExponent.Parameters",
      expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Parameters",
      graphKind := "inductive",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1959ebb3f2aea65f610a6dccebb1d76370724d77f59615a8613f6fde38207407",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.recOn",
      expectedPublicName := "OAI.PiExponent.Parameters.recOn",
      expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "55b2878abd89a225fa453669d093e9984dc054e329e650f35e579ed91ebc1c53",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.casesOn",
      expectedPublicName := "OAI.PiExponent.Parameters.casesOn",
      expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "414e266917c5ab0795344618c5171503fbe89f8fd4de3f4c795e862355a05d13",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.eta_lt_one",
      expectedPublicName := "OAI.PiExponent.Parameters.eta_lt_one",
      expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "083f67995d6b489dd477f85539829ae0f909e017b7b2ae98d79c97d17bc86a1b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.A_lt_B",
      expectedPublicName := "OAI.PiExponent.Parameters.A_lt_B",
      expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "104640a061689cc71fe999651e3c55424ecf9a4e77ecd24cc21c0769b0f4970c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.noConfusion",
      expectedPublicName := "OAI.PiExponent.Parameters.noConfusion",
      expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ca392e756dc60c8923068c5514391b33470b162a7fa98ddc6dfc600189b73e01",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.C_theta_lt_one",
      expectedPublicName := "OAI.PiExponent.Parameters.C_theta_lt_one",
      expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9c1e892f80d53d1583368c914bd05959fba4da7100a7c59b921c4ed990099270",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.theta_pos",
      expectedPublicName := "OAI.PiExponent.Parameters.theta_pos",
      expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "72465333cd1627e9ed4b04f240468bea82c752fa5eef9be02d37292c22a7a2bf",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.A",
      expectedPublicName := "OAI.PiExponent.Parameters.A",
      expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a4b59a8b4862dd1436e6b185c6ad40d37c8a10bf6b7128048cbdff8c4ba8d1c5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.gap_pos",
      expectedPublicName := "OAI.PiExponent.Parameters.gap_pos",
      expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "df664f2d63b6b8c38fc17236e4ce5feafffd4c8434f85135c3d44d2f63d9c3e3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.theta_lt_A",
      expectedPublicName := "OAI.PiExponent.Parameters.theta_lt_A",
      expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d4abb8c9fb3d254317e4b080b65a01f32f13042a1beccbbb9bc66c8dbe48cac3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.theta",
      expectedPublicName := "OAI.PiExponent.Parameters.theta",
      expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "31398ad0ca6bea5cd9f9a5281e73a6e514e34bfa9d100ab9b0137324edb592a5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.B_lt_one",
      expectedPublicName := "OAI.PiExponent.Parameters.B_lt_one",
      expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "692e10f8930e2164c2799f0e0b4727a1fee6feb0770a8ec33e6bf53ca834a61f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.mk.noConfusion",
      expectedPublicName := "OAI.PiExponent.Parameters.mk.noConfusion",
      expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5117ffeec9d4cc0dc67cba1eee378f06f6fd17e0dd45e3de66fac5f2bedb08eb",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      familyRoot := "OAI.PiExponent.Parameters"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.A_pos",
      expectedPublicName := "OAI.PiExponent.Parameters.A_pos",
      expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e48c067080464a6cdb88ca55f08a0eb904b2d7cc9fe26638ff1062af38950cb6",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:5380",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:5380",
      familyRoot := "OAI.PiExponent.Parameters"
    }
  ]

run_meta do
  exportStructuralSnapshotJsonl structuralGeneratedRequests "missions/pi-irrationality-measure/verification/providers-complete-preview/all-shared-safe-leaves/snapshots/Def_OAI_NumberTheory_PiExponent_Approximation_Parameters/structural-generated.jsonl"
