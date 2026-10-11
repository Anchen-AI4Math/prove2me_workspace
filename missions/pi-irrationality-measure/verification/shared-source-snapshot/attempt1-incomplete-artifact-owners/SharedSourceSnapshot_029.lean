import Lean
import OAI.NumberTheory.PiExponent.Main

open Lean Meta

namespace PiExponentSharedSourceSnapshot

/- A request is text-backed on purpose.  The exporter resolves sourceName by
walking Environment.constants and retaining the actual Name object.  In
particular, private numeric Name components are never reconstructed from a
printed string. -/
structure SourceRequest where
  sourceName : String
  expectedModule : String
  graphKind : String
  declGraphSha256 : String
  declGraphRowSha256 : String
  ownerKind : String
  ownerId : String
  commandUnit : String

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

-- This is the same kernel-relevant Expr encoding used by TypedSnapshotCore.
-- Binder display names and source metadata intentionally do not occur in it.
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

def envKind : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"
  | .quotInfo _ => "quot"

def kindMetadata : ConstantInfo → Json
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
      ("ruleConstructors", toJson (r.rules.map (fun rule => rule.ctor.toString))),
      ("supportsK", toJson r.k),
      ("isUnsafe", toJson r.isUnsafe)]
  | .quotInfo _ => Json.mkObj []

def moduleFor? (env : Environment) (name : Name) : Option Name :=
  match env.getModuleIdxFor? name with
  | some idx => env.header.moduleNames[idx.toNat]?
  | none => none

def isClosed (e : Expr) : Bool :=
  !e.hasMVar && !e.hasFVar && !e.hasLooseBVars

def actualNameIndex (env : Environment) : MetaM (Std.HashMap String Name) := do
  let mut index : Std.HashMap String Name := {}
  for (name, _) in env.constants.toList do
    let key := name.toString
    if let some prior := index.get? key then
      unless prior == name do
        throwError "Environment Name.toString collision: {key}"
    else
      index := index.insert key name
  return index

/- Stream one compact object per line.  Only DefinitionVal values are emitted.
Theorem proof terms are deliberately absent; theorem rows certify their types,
module ownership, kinds and axioms. -/
def exportSourceSnapshotJsonl (requests : Array SourceRequest) (output : String) : MetaM Unit := do
  let env ← getEnv
  let index ← actualNameIndex env
  let handle ← IO.FS.Handle.mk output .write
  for request in requests do
    let some name := index.get? request.sourceName
      | throwError "Source declaration string is absent from Environment.constants: {request.sourceName}"
    let some ci := env.find? name
      | throwError "Resolved source declaration is absent from the environment: {name}"
    let some actualModule := moduleFor? env name
      | throwError "Source declaration has no imported module owner: {name}"
    unless actualModule.toString == request.expectedModule do
      throwError "Source module mismatch for {name}: graph={request.expectedModule}, env={actualModule}"
    let actualKind := envKind ci
    unless actualKind == request.graphKind do
      throwError "Source kind mismatch for {name}: graph={request.graphKind}, env={actualKind}"
    unless isClosed ci.type do
      throwError "Source declaration type is not closed: {name}"
    let value := match ci with
      | .defnInfo d => some d.value
      | _ => none
    if let some v := value then
      unless isClosed v do
        throwError "Source definition value is not closed: {name}"
    let axioms ← Lean.collectAxioms name
    let axiomNames := axioms.toList.map Name.toString
      |>.mergeSort (fun a b => compare a b == .lt)
    let row := Json.mkObj [
      ("schemaVersion", toJson 1),
      ("sourceName", toJson name.toString),
      ("sourceModule", toJson actualModule.toString),
      ("declGraphSha256", toJson request.declGraphSha256),
      ("declGraphRowSha256", toJson request.declGraphRowSha256),
      ("graphKind", toJson request.graphKind),
      ("envKind", toJson actualKind),
      ("ownerKind", toJson request.ownerKind),
      ("ownerId", toJson request.ownerId),
      ("commandUnit", toJson request.commandUnit),
      ("levelParams", toJson (ci.levelParams.map Name.toString)),
      ("closedType", toJson true),
      ("closedValue", value.map (fun _ => toJson true) |>.getD Json.null),
      ("type", exprJson ci.type),
      ("value", value.map exprJson |>.getD Json.null),
      ("axioms", toJson axiomNames),
      ("kindMetadata", kindMetadata ci)]
    handle.putStrLn row.compress
  handle.flush

end PiExponentSharedSourceSnapshot

open PiExponentSharedSourceSnapshot

def sharedSourceRequests : Array SourceRequest := #[
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleFrameCocycle.isoSheaf",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5075504ca94bef1347e306ae5ee76591b1d63cd9f01d31129802fa82e67019ff",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle:7332"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleFrameCocycle.ofFrames",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8bb5ea7a9653d7baea9f73a527f3626096882363ca590a599450c2d0369500e5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle:1786"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleFrameCocycle.presheafHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "07804a36c81bc7f19368762dc67486f45b83708253dc844b32bd88778daf06ce",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle:4716"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleFrameCocycle.restrict_presheafHom_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "221e25590a4d18e749bd674336b53dea885557ca5528c38794db35e4367f7c20",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle:6056"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleFrameCocycle.sheafification_presheafHom_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7ad9f400e1e11ca56500feb0e1937784ed643acb92284d9d7882eaf94cf07bcc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle:6610"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleFrameCocycle.toSections",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2204eb39eb99d044ca7d3d3721f74ee869f672305f6af120f8b6473b7d9509ed",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle:3268"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleFrameCocycle.toSections_bijective",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "923b5a5573222a5d4b30d9414ff447a8804ed49716ede880ed355036104a2894",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle:4147"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleFrameCocycle.transition",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cc7281fda29b3d447b9c84eb75ae410c3bf13357b4513955c178d338eb4a894e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle:1296"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.Cocycle",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "inductive",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4ce83aa53d14c8b6d42924f8dff98042af52fbde79e3c5d1b32dc6bc8c83dc99",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:323"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.Cocycle.casesOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "30de84dde6d6afbfb8432b88a0f0e9c054121750b3282f5cc0d4e30f9e8e6438",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:323"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.Cocycle.cocycle",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "69b0d99e1d22405aabdd9571f1e513ccd83b91383a3e0d5c3f083877a9aeed18",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:323"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.Cocycle.identity",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6920553deaad2db98676b598af526619a9b5452b3db11e71ee56b169eb454f3d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:323"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.Cocycle.inverse",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f397d393211df946331cd8559cd18da33a24f18a5db10819315beedc5e67e053",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor:603"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.Cocycle.mk",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "ctor",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c128790d3c41a5ceae3c9606061e5e5ffe098b763906190510a1ea6e2da62312",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:323"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.Cocycle.mk.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b1b89b78ef431290635294dfde1d5e7e4a2154e055ee2d05e6051b6d5439daf0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:323"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.Cocycle.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "feec5b3919ff152721a288d650c378a72a9c90686e7df63785403891e594b48a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:323"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.Cocycle.one",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6c5c3af12bb9b4eb13300715839f628d49474a0932991467f5e3359260c9c350",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor:438"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.Cocycle.rec",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "rec",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7fedccf01004778b228e5a1070f5c18d8a7c6ef65c7553b23b49e5a7886f6104",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:323"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.Cocycle.recOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c229208ed7012ad65724a666f40fa0684798a0acc5626df6ea8605030630b97f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:323"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.Cocycle.restriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a88d0a1b9a0830e50f7b6d82570fc892ac2979a3e85ba64acadf059e840319c6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:323"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.Cocycle.transition",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "58fef111c60ccef2c0f8871aba0260089dfed7cb9959e6f580bbb0d0abc242af",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:323"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.Family",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "53f935b0e3a680ecbfaed7afa83de1b6f973d071c3e1c77c9ab27cec7a1e4ff2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:1001"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.LocalIndex",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ab1aeb6304ee708c67d6e11d72de9f1fa33aab0197b178d3d5a9cba4cdd5080a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:916"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.chartEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a7207abb5eaa606c0b0929006cb3237d1ff1103e1aaf9207a72c6af9b12f8c05",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:5637"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.chartEquiv_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "850a8122e43a5e8eef976481e1b7147144db3e5445133169fee714f63b737139",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:6545"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.chartPresheafFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "df2c8973d8459407aefcc60198c8d44e36ec906ff52e7d88e53a8be4f2ff091f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:7577"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.cocycleTensorComparison",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensorIso",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a76d7da605db75eb460d4ffc5fc0e26c2c1506f0788094d210d2ae60f54eeea8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensorIso",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensorIso:1451"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.cocycleUnit_restrict_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "25be5cc9377bf8e970065562961e048ef8fff009950dc16c974d64330b376b51",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor:3393"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.familyModule",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "58f1e1c88559240bd978bb33a07bc8c707621fe4d071c1121ceb59fab72daf44",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:1258"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.fromChart",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c56ec9b06c00656a4ae7d2755afac02ca37a4d6d2fc27a58baa20428b15af428",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:4642"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.globalSection",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluingSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "58b67ca65d1a126861190b9f7e728a6b981804d2b249febebeb2ff025e3a578b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluingSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluingSections:490"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.globalSection_app_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluingSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f1599d1fc6ce7adb863fdf3127f0d4a194fefc9eeed9044030322baa8a531f51",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluingSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluingSections:3546"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.globalSection_coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluingSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "057a5d448ed6dc89744cfa886225adb1b457159545c4c2efeee9a72c21d2e06b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluingSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluingSections:4450"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.inverseProduct",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a1845d2be64b853f03593fa22fd33be2afb23132373d62ff1881cb40f1ee3e87",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor:1129"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.inverseProductMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b0cd0663a5a2841f3334232ab9f4c2da4bf660d8d92b379e725984a1d7f67689",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor:1814"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.inverseProductMap_frame",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e4b755ea4d1cca707bc53c986fd401c966d32e9c89879d4429693c8053bdbdb4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor:6114"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.inverseProductMap_restrict_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "43e439e53baf60831ebc4f64a163570a3fe1c1192c37176e63070f10b613783a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor:7755"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.lineBundle",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0875daed064d0927bc38f74f85cc9169d8a5c87d88b7f110890139a41a3b3740",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:8407"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.localModule",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "117c23b7ac99129be4f330afe4128a4dd506eb70f444c9fd002125bbd744e76b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:1073"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.openFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a9271270c293c5ffa11c4a32018043f329b611151853f24545364d4a2f8d907f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:7885"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.openFrame_unit",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluingSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3a23dab0a3941ef160ad704d8edbe629a9bbc8dc72322c556d75cd8b64a921ee",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluingSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluingSections:1741"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.openFrame_unit_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluingSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0cd52e821f8042329c346894631bcc5dddd9b98356b3a4b3f9ba2489c7bc2b79",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluingSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluingSections:3054"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.openPresheafFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e89c9e9ae2aa893b65c69ed15df217f76eb9cf1ea08d08bcac1961e2b7ce643d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:7047"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.presheaf",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "39945193115da6e62ed509c2ec65f0905b7a6dceea0fc921cabf798230c9b7b4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:4136"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ff008bc926711b468186a74fd23e60fd402b3375c5a1d6f44ac0beb349e2fab8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:3301"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.restrictUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "585a1a08a3d5a726b2c2b13408d2c53e14af8d1a605a6b1a72cbc2166d69d8db",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:8810"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.restrict_smul",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d5711433a9f3b61d7db3e332d10312b56a4ef70e748091e2125e393b2b21d734",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:3661"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.sections",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "07c83313700ad9a5d62e8e98880bdaeb24da32525d8b1f71ce14693996cdf22f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:1471"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.sheaf",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "faa384516d5c7f0d8f30eb6dffd523cf6d1a22da7abe401dbb4f706b0fbb13b5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:7776"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.sheafification_isIso_of_chart",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fb88cd433f66f357cb884735baa99981cb6a421e6b52a982381a7133f925a550",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor:8782"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.sheafification_unit_counit_map",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluingSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "472afcfb19c0f9105e16ff3d398ad060443a3c1c072a6a267ffd052e8eda4318",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluingSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluingSections:740"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.tensorHom_restrict_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensorIso",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d5256e071d92900b4508ec972e63bebe2fa48f86c164cfe00a5ba2400e15f713",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensorIso",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensorIso:357"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.tensorInverseIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensorIso",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fc05fb5762c269bca820bfc47a768c3ad5a932a03c0e34c720ec870dd490bc59",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensorIso",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensorIso:2794"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.trivialCoefficientMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "661f3e979b2fd6195448996fd0b87ca100ed3dc28dbf27d235df7ecee11e5ac5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor:2453"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.trivialCoefficientMap_frame",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b3a6bb78b064951cf46ed71ae12e558dd6ac203845d5dcbdf8259fc87f708b51",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor:4557"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.trivialCoefficientMap_restrict_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0f69999c33590bae7bf3ca80a5677aee11b8542095330cdecc42c793841e4301",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor:5097"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.trivialSheafIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensorIso",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ddbd49993e6bf71a592287333c3996ea202089e4f8fd3cc419d50a22fb9b3edd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensorIso",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensorIso:2269"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineClosedUnit.epi",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LineClosedUnit",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "641397ee6e4bbb01a0d1b953923d49e0744bc6d70e827c7c5a5994d5fd15c3c3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LineClosedUnit",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LineClosedUnit:2673"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineClosedUnit.frame",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LineClosedUnit",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1eef08555b9af0c4e74b25ae4ceb4f41c9754b6c179b65d87eeea46ad96f9cca",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LineClosedUnit",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LineClosedUnit:683"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineClosedUnit.framed_map",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LineClosedUnit",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "382eab93030aaa0746a1ce917dafebb180851d0f679a750445e1efb60f5ab736",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LineClosedUnit",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LineClosedUnit:1193"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineClosedUnit.map",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LineClosedUnit",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7da85a8e7ae07199939648706de26574ea379524c0717c13743b454c9fc39fdb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LineClosedUnit",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LineClosedUnit:485"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleFlasque.freeMap_mono",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e0df1a07ede1efe21327f8622fcb625490c68286e8ab7fc3a737c82dd83e70b1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:27913"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleFlasque.freeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "edc130e2dd23d27993c4413f7099da152be645ef6951a49300dde44104644d75",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:27543"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleFlasque.freeOpenEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c8138b0e61a1bca9d6060055a4a292974cc5fb5c7e3776ea8f4bf7317e88fd8a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:28443"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleFlasque.freeOpenEquiv_naturality",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8ca03bca23c0c75a84258a70cd99bd2f9fc971a4fb8fd5bd82aadeedaeed4beb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:29268"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleFlasque.freeOpenMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "37463e021b64efe86b3c7137301e99fe511b5e29c9e1241fa6383e409fa18fe6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:27714"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleFlasque.freeOpenMap_mono",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "96f9a4f30c55bcf79740594204790e4c84dbf768ead236aaf1009473da14c14f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:28272"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleFlasque.freeYoneda_naturality",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6a12d509a6820aa7ea283253be421e6ca420ca14cfa2d7c59146e5f2243c838e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:28661"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a3ac774f397c86b828ee53213f2469f2f8fd01ba996048284d8eae05aa7bbeef",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:30235"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleFlasque.restriction_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9488889fbb732c673eacb1cdd133afa9fbe91207f6355745c54d6aed741c99b5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:29832"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleGrothendieck.enoughInjectives",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5da0db3fc6bf93c25d6c44d55240e6c4235666da4154a73dd19e56b6950e740c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:27237"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleGrothendieck.freeSheafSeparating",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d129ef989e6b7b09df67558f938b1e0ac801c3061616ceca0807dae2e03e960e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:26182"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9e752be90f64f70c840b6770e5786c33d179d7ce07b69e999e210e4a7512a9fa",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:25426"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d5c11a2b0a76391c2ba2499d1743921e9d08bbbec7f1969beeb52bc1597a8480",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:25817"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "85ac0b1a9781c14829d06915e1d842aa4f8ab9b393d2562641fff75fd0812e5c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:25596"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ae26632efb60f3654db8fea98875080b7e20d91de6bb4c0761657bbff6bcaa97",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:26017"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4000fe54190285811e5cf18f1a555a0c7450ee5f25f9cbc7820d0dfc13d4e8e1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:27150"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a6492a0837fd4eac30e1ba2bd80c8d65361ed50d3d657b0459980d880751d9ba",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:26884"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleMayerVietoris.freeOpenFunctor",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fad84b33161f4fb9884c4cd519cac88efcb9c2c0a6687b4dab0e8d49e3f590f5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:50867"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleMayerVietoris.freeOpen_isPushout",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b8cefa55acb602f6643a212a14dc8d81563629ffff439efc54b59ee1bcc05304",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:51021"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleMayerVietoris.shortComplex",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6c8a9d39746bd608bd48c9f6b58dd10bebfe5fc4783788539eb0b99fabd54253",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:51662"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleMayerVietoris.shortComplex_mono",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4f09a21cbc49dd960bc2e5131d2c97f8b4853bd4afdd7f792a3697ccde32b5ca",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:52162"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleMayerVietoris.shortComplex_shortExact",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "19b4a55896ab76d82b239215b80beb2cc1064623bb0146a1f973c6a09232542a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:52419"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleMayerVietoris.union_ext_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "03231c63c9d673aa16bfce74c069ff8eb20aa94159f419b73cef8faf2ecc6b19",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:52801"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModulePresheaf.pushforwardCongr",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "33dcff42f2d6f557466de35d4c8d9eec2a8b24a57057e23bb280db0722270376",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:1829"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModulePresheaf.pushforwardNatTrans",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e75fa90c847133475c381dcc18d5f47d65b24b10302031abd77996ba9214f3b1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:2355"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModulePresheaf.pushforwardPushforwardAdj",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b4c39eb7e16646f2da13155c881fef87de6d95425f9c72bdb2cd9b4e50a138c5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:3479"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleSheafExact.shortExact_map",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "36b0422604885ef69a8a4618886ae0770290e1558907c3bd796be5c0e946e932",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:31997"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1c34bc088618113472de696906f541b155289dfd8ba2c829cfca0cafc4eb06cd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:30871"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dbf137dd72511ef42b52da42f0c994cd723e5655225dc5766eff55719d68bf30",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:31824"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.OpenBaseChange.hom",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.OpenBaseChange",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d21d83c99b38329cd9c9f451a244d3daf845b2548d52eb4e641a3676450499a1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.OpenBaseChange",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.OpenBaseChange:1445"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.OpenBaseChange.hom_app",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c2ce2cb30f14f41fb02bc8e1c4dd9c2270d198221466fe8632865629c037965b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange:3452"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.OpenBaseChange.hom_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.OpenBaseChange",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5aac6f37be81a102144b6b380ae46fce1e5e193cbf39f92c9f4392f9c87ab7c1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.OpenBaseChange",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.OpenBaseChange:2036"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.OpenBaseChange.iso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.OpenBaseChange",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7e5fee3a4cc160eb126a7fedca7c3d5afd71bd1ec4136d13bd48e80226405e70",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.OpenBaseChange",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.OpenBaseChange:2697"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.OpenBaseChange.leftSquare",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "067ab4637116f46d9840e91118847ba1831f3853a60580c02f74eb4e2aae94e3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange:439"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.OpenBaseChange.naturality",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7e3eb7df556b705d183bb40a892b496478eb5ca4e6be6bca858a9e3868d84195",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange:7365"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.OpenBaseChange.naturality_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1727cf2be91c8a8ee138553320a8b04061cd7914452fbaa61d75d3e3de22b995",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange:7365"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.OpenBaseChange.restrict_unit_app",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.OpenBaseChange",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5fd6bb85dc6ff3cfa8c13fb96824da7f5b6f506f84de58942d4e596ff46396df",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.OpenBaseChange",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.OpenBaseChange:284"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.OpenBaseChange.restrict_unit_app_iso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.OpenBaseChange",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4f7088838715c95abe9a2797353c86ddea24b57c3d93e574f3f09871f51d11dc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.OpenBaseChange",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.OpenBaseChange:531"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.OpenBaseChange.rightSquare",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.OpenBaseChange",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "978407671920e5a11b3ef796db1a17c68b84e2afe24375d03ed1e991b3851e2e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.OpenBaseChange",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.OpenBaseChange:1084"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.OpenBaseChange.tensor_pure",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2897ca7396a3160d0e7ec821d80c7903f21eeabe14757cbc3fee61c96f921fc6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange:4524"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.OpenBaseChange.tensor_square",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c03ceec53c81965c8a8c05ffc6cbbc98b209b16c4e3683bde634d88157e0f61b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange:5450"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.OpenBaseChange.unit_compatibility",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ab80428cb5ec590083b3892dcd3bd0ffdb6c6b8c9cb728b98c82a4fd233692f8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange:918"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PrincipalSequence.end_regular_of_mono",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PrincipalCartierSequence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3b214d29d68f287efc044bc71af11fe82e085686c9f3c7e6ce2e26a29d5c225e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PrincipalCartierSequence",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PrincipalCartierSequence:493"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PrincipalSequence.exact",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PrincipalCartierSequence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1fdff1f25881053194a6b6d6d548c2bbd1532a5b8b08a4941f0480b72512286e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PrincipalCartierSequence",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PrincipalCartierSequence:935"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PrincipalSequence.scalarEnd_eq_multiply",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PrincipalCartierSequence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c1e07828d54b46cc03dcff32d542202f3f46f130806e0ce6ac87105e3c1b2f4f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PrincipalCartierSequence",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PrincipalCartierSequence:400"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjBase.basicOpenToSpec_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0aa208a46d882e7e5aeafc672e3363b094a5dba33c565361137d2ece504d233c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:1145"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjBase.basicOpenToSpec_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cfb731ea1bfc80cdf7be0fc03def74733ba5b195082230c10d3efda227e6598b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:1506"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjBase.toSpecZero_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c44814b7a2e4476ccb87ae0c7ad5ee18dadc318c7f860000c673687f4b9dc0a4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:2007"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.ChartVariables",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "03b5a4a594dbdc697ca1e582ca3dbc2da620a8ebccd99ed7e21772d42f9a3a3b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:1175"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.CoordinateAtlas",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "inductive",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c3ec0d7e6a6470183f411773c42d69b069c829717c56200a3a349644a2cd9efd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.CoordinateAtlas.casesOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1a085443879a1d090b1423aefac6a6abb9ce2c8d0c4ef0857e68b43b3fcf2684",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.CoordinateAtlas.compatible",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a1546ca382683afd85455bb716431443aeb9fcb84d9b4009c804fc963e3ee8b2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:10538"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.CoordinateAtlas.coordinateOverlap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ca484722d97d62b45a863deafefc8a02bd244aac753d26aebb4bf0b765659117",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.CoordinateAtlas.coordinates",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2fcdebe15ccb7c4d5cf0b9092c774370d2961f775a41e74634d220fbe69953bd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.CoordinateAtlas.cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "40f289845036291b464f6fcc703008d2da5c4e7c4d8563ba3d7da459bc383b65",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.CoordinateAtlas.cover_morphism",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5f76c168f22b1acf597d9373f252aa9f4f21617fbb3dd653d3f82a5f28dde1f1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:11281"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.CoordinateAtlas.cover_morphism_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "97560ec793ad3c50b11e99e71c79cb10d77644535f6fdec063fc5f8ad2f75710",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:11281"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.CoordinateAtlas.index",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "657299de1b7363e30294539c2ce5236adeb61f47edfd53687874e6ff992df6a6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.CoordinateAtlas.localMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "35edd56a019e325a95bdf8997c65837902a768dbf4808dffbf99b706581f7386",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:10347"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.CoordinateAtlas.mk",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "ctor",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "64bdc8f1d85b18a807a22c99c6da8cc93a5355240bdc729623a98789881155dd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.CoordinateAtlas.mk.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cd0602b6d6c26d0bb2e4b3d6d0164356ebcc78e830b78ff0768602bb8afc1305",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.CoordinateAtlas.morphism",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "98acd4d0585281abea377c87044e8c9abb9fb39d3c772aa43e2ea7904b2cbabe",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:11156"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.CoordinateAtlas.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ee315122887e8e5de2a19de2db412da36634b69634de49a545a53c67727e4e33",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.CoordinateAtlas.normalized",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d85bb690eaedf26017149b874f6f41155a73a8ee61828d5b2de0fce8dfa0166c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.CoordinateAtlas.rec",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "rec",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "97f5ec9dca40281a1903db33e15824d9deea1973bb7e0c63d9a827096082782f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.CoordinateAtlas.recOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7d7cb5853104894925abdc66a1ad7a3a8e1e0a3a45e006162adc365183797e0a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.CoordinateAtlas.scalarOverlap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "30ad7d00a6a24a7f7a2829d714197eda4b9a94e260a377a00f8c6a8ee11b6656",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_029.jsonl"
