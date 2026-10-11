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
      sourceName := "OAI.PiExponentSeshadri.Geometry.modulePow",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d0b18ac58312eb305fbe26240ab5bb929b67b19189492f0e5772489630e25db9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:786",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:786"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.modulePowFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7dfa81a236638f9c05df8f007893b71c9a3f94da6a686272557cc24d5961e302",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:9329",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:9329"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.modulePowFunctor",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dc7c099b36dd02101f97f2ed9d25ead0af0db63bea84c5e2e56324ed7e6610bb",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:12718",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:12718"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.modulePowMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4328fdec54281c1d345f2a49ed3b8ea93bbb67a082075e70236012838973f512",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:11488",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:11488"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.modulePowMap_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ec3507302250be22140dbbb9b4cd10f854ca888a8ca09411fe0b4ba399b6ccb7",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:11974",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:11974"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.modulePowMap_comp_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2526236228df0e3ca0b5e90cbce72e49fc6d970b89caf517ea600d748ebc3a2c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:11974",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:11974"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.modulePowMap_id",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e2af1de3e75295b6c78a53317f828df10682b400e6ba41c5d455882e03d6fbca",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:11658",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:11658"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.modulePowMap_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6e471ffbe8e3e4fe35e921fcbe60913f1ded65c8f3ec4f11a2a6cc67033ab891",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:12423",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:12423"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.modulePowMap_restrict_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPowerRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "77f6dabab5d9a87c68d8ff99f6b3785eb503493931d9915727314edd99986778",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPowerRestriction:2086",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPowerRestriction:2086"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.modulePowMap_unitPower",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameTensorPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "26d4079ce446fc8eb41e1ccb725d902413f240cec1977b62bef4f62ad6b1b7cc",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameTensorPowers:4422",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameTensorPowers:4422"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.modulePowRestrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPowerRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "03e6215eb2c8c1c3fda5c65a0b9dd7180d4f3767933bb3ad8606a109a97c672a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPowerRestriction:367",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPowerRestriction:367"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.modulePowRestrict_natural",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPowerRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e8cf800a06da317be71005c83bd47f1b6f999d1fcc86713d7be4361af7900d47",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPowerRestriction:685",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPowerRestriction:685"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.modulePresheafRestrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1c33c20947a3327f72adc946d7afe35c61a43a53baaed7e91c009c26ba2c424c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:4913",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:4913"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.modulePresheafRestrictAdjunction",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dfcd5a3f0ecdb8537b158c2c0c1405ffd8ce3de58c37eb6e228f17fc177a853d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:5225",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:5225"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.modulePresheafRestrictOpensIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "053d3410b813039e1f5a35a45f52a01f7cd7ddb30e6be835542710a1bcfcf6b9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:6508",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:6508"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.modulePresheafTensorRestrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4dd4bf698b6fc3b1c2918eeb7c2ffa3e765fa9707d13db0b1ba7fcc6f3df3014",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:7128",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:7128"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.modulePresheafTensorRestrict_natural",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3f0423939d809e4533468b8db044898d0b84ae211695292cac65ba2f8efea2ad",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:8154",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:8154"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleSectionMultiplyRight",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "592c29a66f98d5fd7895edca9dc536c238195d16d9d9a334a1683e0f3cf95e56",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistSections:307",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistSections:307"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleSectionMultiplyRight_natural",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b58110a6a3e6b16b2fa12cabc343db92572b76e0a2c43215c7141b79f01fa3ae",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistSections:501",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistSections:501"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleSectionMultiplyRight_natural_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "99284d597a6b69dd1127175d2db6a55e994117c0e6b7d28ddc2d7e609373e434",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistSections:501",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistSections:501"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleSectionMultiplyRight_pure",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionScalars",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0073d21eda5d05586f2b545e1a2f2cd3baf9d34a5e597c9a1060cc8639791b8a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionScalars:363",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionScalars:363"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleSectionMultiplyRight_restrict_frame",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionScalars",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5fd05e597bdc7ad43bafe9becd2f41572ae6e3248060fb3cb8eaf4dbe244ff28",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionScalars:2343",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionScalars:2343"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleSheafificationRestrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "800125db62c7f3adde08f28b7f2bdd913d7976cf4654a1db930f1561f8366af1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:5819",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:5819"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTensor",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5b7b28403cf6e6d2b07ce99e0c90ff703a571cabf589102c92aea0f970e8988d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:591",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:591"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTensorComm",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2b6bfbe03bbd4a1068c7c7f97334f33489b056d31c4cacc1b3c6a348fc0c4095",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:20700",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:20700"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTensorComm_pure",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistPowerSection",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fc34459bc1fcad12d3478252dc455fa790f77bfb6cd9f1390f9735897dc415c1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistPowerSection:393",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistPowerSection:393"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTensorFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "105ef04f63368d507a92df27a0e41964fde2b910e40621b0c8efc6caca65ce4a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:13033",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:13033"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTensorFrame_natural",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e90ec03f9b036441475668382ca276f6f5902c6594bb0800f156ca614c9af61d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:13219",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:13219"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTensorFrame_natural_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7777cdbf61af1e18aaef3f843a8233d461a304461901d936fbd92a215b2b0f8d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:13219",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:13219"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTensorFrame_pure",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionScalars",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a4f18f1cdb0319626b7d0a03f6aefed26bad0106c91ce83c54d596ea402d090c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionScalars:1307",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionScalars:1307"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTensorInverseCancelIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleInverse",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f638ff0d33cbb9d3b604be1bfffc1a94ae90671977319a420a08b85d7ee8260e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleInverse:1574",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleInverse:1574"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTensorIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "029050965cb93541c95a6755806d68fa8ff0d09d8972a2e55dd571a5f0e51dec",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:8462",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:8462"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTensorMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "25c753b1307664763b4c3eabf436922798af83ef2078a322f215f40a5c7e0483",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:9942",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:9942"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTensorMap_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "63c7bb4b100b978c9a5e9282b6ce8c1aafebaffa92b8588e31ae0ca32a38b13f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:10686",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:10686"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTensorMap_comp_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b329770393ce94ec5971d3cba8698a5d4c1a15612ab21d09fccc38e1943ab740",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:10686",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:10686"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTensorMap_epi",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8b395aa3bffa4e0761eea293a85f34ade45ce7e5e3058b18d501ec64644af2d5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:14921",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:14921"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTensorMap_id",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d9a2d3d9f90751ea12c21507c1bac6000553aaf07180aeb5018d3c4f610f394c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:10209",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:10209"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTensorMap_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b6d4a231b87d3becd74694d98551db5eea41317d550565325e777c5806f6322c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:11233",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:11233"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTensorMap_mono",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "456295fa4363fef9bee7193138730c15a776aaa4271fd75555dce70418dfc611",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:15909",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:15909"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTensorRestrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e256ba38e212155e564a927f27fe6706c62791b163ddc5db988a8fb0af6df76b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:8100",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:8100"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTensorRestrictFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8854bd0b7b6cef506d488b230168d17e2cd6236362d9b2f30afe243934a70d1b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:14041",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:14041"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTensorRestrict_natural",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f5cd82f300cd0d0c6732ccc3118c6d7c1879e476433bf9b8576aee64031493d2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:8856",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:8856"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTensorRightFunctor",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d248bbe9aa0b3f67bf8110b341ebaad5a830e4097892245b4e5d6f1b2b48f446",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:10995",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:10995"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTensorRightFunctor_additive",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c70cfc206bd49a95819f06745fac6fcd9f75027cff0a861a5935f7ae498be771",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:18391",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:18391"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTensorRightFunctor_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "db91374618779ed11c5de7de705a16e4bcd848f333d8cd7b3870348662215041",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:17535",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:17535"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTensorRightFunctor_preservesZero",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6ae345dd65d2e8e129816f16a203eba489df2d4a57a4a8c1a1c4a74d19c65492",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:16904",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:16904"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTensorRightFunctor_shortExact",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "92ced32bfcfad0ca6afd317987a09f84a7f19c71b75b21ff375a61ac80d679bd",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:17997",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:17997"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTensorRightUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b9200fdd13f25e68f2e1b973b18acfd204ebac21a88ee501be2406edc240e1c7",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:13928",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:13928"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTensorRightUnit_natural",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "004044e3c48481c3b69d30a3c545b36f3215b6c46de3815a59af103074be1cb2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:11424",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:11424"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTensorRightUnit_natural_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4a44788e520c288cee44fb3f7795100983e561a9bbbe238b4a3176648e0ca5ec",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:11424",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:11424"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTensorUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e67cdb5c982f16e473afe0fb302ac61e06c1d4963724d26b879329f4e4e87f5d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:8885",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:8885"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTensorUnit_natural",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameTensorPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b125f3897b26abf271aa78b9f96d0d3db68e34e551a2f1fee1427452fff04b36",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameTensorPowers:2864",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameTensorPowers:2864"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTensorUnit_scalar",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameTensorPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "14bb29558d20c4c4cb9ea9417eb23c048decc5c7ebc2a9dab44a6f8190859759",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameTensorPowers:656",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameTensorPowers:656"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTwistForward",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c5fafb53406a68f2c26ef38649d762beea03646d6a5f3b52825ec568d8e76cf5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistSections:2058",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistSections:2058"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTwistForward_frame",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionScalars",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1cd3aaef6ef38ec78dbe085e6e5794dacc6500f5df3444fcc6181924b4c075cd",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionScalars:4174",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionScalars:4174"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTwistFunctor",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "330083185a24d16bdc4d63d023fcb210f152b483c9c270cbc62fa248ee51196b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:19297",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:19297"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTwistFunctor_add",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "23782ee79d1716b15ab5ddd82cd19104c4bf8a29b7cec70356aac897aee5f717",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:19786",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:19786"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTwistFunctor_additive",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6865c6ec613b90441f033f5464b7e4f9cb328215d9a77c85d0ecfd720980e68e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:19467",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:19467"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTwistFunctor_shortExact",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "694aeb5b31b1cc6ca1dc545666101452f10e4402b9325e43c014d8cecfbcce11",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:20270",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:20270"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTwistPowerIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ModuleLinePowerLaws",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0ce6e680c42cfacfa83fd87a8aab4182f87326e00047deeade87600693e03b4e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ModuleLinePowerLaws:6578",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ModuleLinePowerLaws:6578"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTwistPowerMulIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ModuleLinePowerLaws",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4ee03f194e1bb44eb14898f5b1942017b7113ee01f6b6c3797bd2b5412bb09ca",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ModuleLinePowerLaws:6996",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ModuleLinePowerLaws:6996"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTwistRestrictFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ed9f61e895e24fbe044f0d969804484cff01972bc340bcf1c9b85e2efaa7f4db",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistSections:2810",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistSections:2810"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTwistSection",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c73dff59687ad4b638345fe769a156b9b84221abff44749d9444cbc41bd84d47",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistSections:1836",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistSections:1836"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTwistSection_add",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2c4e54f5a48b2451cb00ee05053694dab95fbc6dab664073d544393907f8b2ff",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistSections:2308",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistSections:2308"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTwistSection_frame",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionScalars",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "77137ae1e07979d4335b7d1083c607647d801fc56762f9fbf30f88ff11ba4091",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionScalars:5379",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionScalars:5379"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTwistSection_unitIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistPowerSection",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1f07eccc779d9771a3ecdff08a554a3f2af8881c562322835f0a616afc7cca93",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistPowerSection:955",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistPowerSection:955"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTwistSection_unitIso_app",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistPowerSection",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7fe1c6fb3fee41d025a57064743d7f99934ed84ab8ffa76b9198388f495c656a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistPowerSection:3050",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistPowerSection:3050"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTwistStep",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "08af348525f7e6a259735e79463e0eba70d2111366799facecfb45492b51be4a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistSections:1515",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistSections:1515"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTwistUnitIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d751b925008526a24494915e2820bd7082e56530f564e3daf3f912770484f90d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:21141",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:21141"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTwist_app_bijective",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TwistLocalSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5ac2ee5e5c243e5e4acf3a5ba4c6059a1be4fbd30196a9f2cac41d4e8a797836",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TwistLocalSections:239",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TwistLocalSections:239"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.normalizedPowerFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerFrames",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fec19952ce006a3ddc8badac70c7a7fe529df8424b3330993d591a606a56c706",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerFrames:414",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerFrames:414"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.normalizedPowerFrame_coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "83212055ee4514c9db081c81d09be1c358437a7ea39a53f52a470cdbb506b9b5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerFrames:1177",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerFrames:1177"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.normalizedPowerFrame_normalized",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6122cdadf052afcd8fe826271c02db39a5fa0767c74d1518b55f8d24235d489f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerFrames:807",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerFrames:807"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.openImmersionTop",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8c0849dc361b177263bcd4ace531834f370f2c196d4fbd5ae41a0ae208859815",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:12880",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:12880"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.openImmersionTop_localize",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0449300d580c3aa29d4cf340027324c9cde73654157c365427ea1ddbe99101b4",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:13312",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:13312"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.openRestriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9904b097a763c4bc7c8390d8abdcd790e572b455c809993d2cef4670f029af2e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:2933",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:2933"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.openSectionIso",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteSupportLocalIso",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9331f493fecba9bd4898187765425bf05a3ed31fbb921b6e2a465ba6645a863d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteSupportLocalIso:1848",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteSupportLocalIso:1848"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.openSectionModule",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteSupportLocalIso",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1f3d76f299a54bcc6141d85d85253bd2351b9f0aada0b60e31e2bccbd87e01c8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteSupportLocalIso:386",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteSupportLocalIso:386"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.openSectionRestriction",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteSupportLocalIso",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "99e85c399bc1eb9e279fec2f0590e8307be85f4de97f6dd70e9bc5148186ed73",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteSupportLocalIso:606",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteSupportLocalIso:606"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.openSectionsCongr",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ab2f2e013d442ebb893119e94b2c4bccde7414f743d91c4770b4aec080b52f02",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:6603",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:6603"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.openSectionsCongr_restriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "baa09aaf304dd4485f04b97ab0941012a8c41a1cb76332bea189fbfe862c0072",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:6778",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:6778"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.openTopSections",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "259a1ac42efad34cc30f2422c04754592abf4e573a92a273770988e0add875d6",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:8661",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:8661"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.opensMap_final",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePullback",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c9572eb6625ba886e1c43e2f0aa7a7c99679259a462fcb6d0f35f17d5816e088",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePullback:312",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePullback:312"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.overFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteLineEuler",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "095e7735312f03f84b3c7d0db2acac81060fafed9e2057f61938c71149b94380",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteLineEuler:351",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteLineEuler:351"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.powerChartIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalPowerSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "52c4c2345a47be20098fadacc3e95a4c690652cd844d3e99da97fc61d6dee6f6",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalPowerSections:4221",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalPowerSections:4221"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.powerRestrictionUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPowerRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "68c3ab20fda9c7e9dffcd3348f76307732e66aca0918ef5f8cf78112603bfa9a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPowerRestriction:3566",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPowerRestriction:3566"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.powerSection",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c90a34ca3dfc4796c1350283c7b293f75e825132c999ff94daa4f6493e35da80",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:13092",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:13092"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.powerSection_coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameTensorPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "18919009f8b1ddd37d72d9b97b510f3b31e653cbc9dfb73e2fc550428b8937d9",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameTensorPowers:6168",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameTensorPowers:6168"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.powerSection_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f29c69f47eebb5abdc85222e530da98d32afbf606ebbbb8a8942b2b2b4b92370",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:13758",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:13758"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.powerSection_restrict_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPowerRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aa2767b3c390291995bcde4a024f0c65f2de9b8dc8cfd2d51d3ba6f01e3d86a2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPowerRestriction:2720",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPowerRestriction:2720"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.powerSection_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "afb4a888aa9fbb9224043ccb52eebf53c41ce806196d6967592b6812454a4a9b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:13259",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:13259"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.presents_morphismRestrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupPresentationRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e313de4bc7558c94e3196ac792af83f0888c11be6e6d45378931bf383ad87a82",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupPresentationRestriction:1018",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupPresentationRestriction:1018"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.presents_post_toSpec",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupPresentationRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bd2e7983eb6a3e5ea57fae67ba008258207c28229c75019f04d477e08da750a0",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupPresentationRestriction:402",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupPresentationRestriction:402"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.proper_closed_finite_of_dimension_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d3495ddf94bff779136ac09015fc28a4df9e41ee481faa789ac265fb1a0111b2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros:5011",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros:5011"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.proper_finite_euler",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9722737252c550bca81cc3e606d599781a4c638f8d1c35a2f1403547e3cdb2fa",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros:9367",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros:9367"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.proper_finite_euler_eq_sum_stalk_finrank",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d7e9f3dd429b59196563c4cef4aae6dfc7951f8f8d88d06f18eb0a7c6bc85b41",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros:10136",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros:10136"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.proper_finite_euler_eq_sum_stalk_lengths",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "abc6ab5ba63ae185d56093972b425cc3146fab9c181c4371f830261ad95c8259",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros:10564",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros:10564"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.proper_finite_finrank_eq_sum_stalks",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "319d1f57de9ea6e077226be1fe5c52469a54cff83aabdcf5d7d5045978509f6a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros:7576",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros:7576"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.proper_finite_functions",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6b88308f28041494e75472583f8f2e43073d558bd5ad4a2eddcbbe22b1e0e7af",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros:874",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros:874"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.proper_finite_germ_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ec99a4e94dce9c3f131c6860ac3ddaf13d4880c8e3261e96517bf3099e68a9e2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros:1413",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros:1413"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.proper_finite_scheme_isAffine",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9a38a352b73816131f344c1d3e2dc26c1ea9587fe61acf73bc0b16ca90b461ad",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros:661",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros:661"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.proper_finite_scheme_isFinite",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "05c2481fcc46b74c0682961c1989d7b9aabfa244e949c6f8388ae6332cbb7509",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros:428",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros:428"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.proper_irreducible_closed_subsingleton",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "083c1f4c2a41302ebb911f96a753f22ba8a1de6a9cc5599d57bd33c2636ee216",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros:4036",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros:4036"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.pullbackFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8f7f85d98f3a8a6b7881c0d993f3e870cd133e600dc291ebaca8eca6a009bb93",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor:4138",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor:4138"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.pullbackPowerSection",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cd9ec1ff0d2d6ade32716f3b7eea69e2205fa01a758097927ee262e92bd1cf59",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleRestriction:1560",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleRestriction:1560"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.pullbackPowerSection_surjective_of_ideal_ext_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedPowerSectionLifting",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "892c1486e5cc678c2901855bda10f2e1c2c8c138eed5a7c053b5178153d7e49c",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedPowerSectionLifting:516",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedPowerSectionLifting:516"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.pullbackRestrictFactorNatIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectivePullbackFrames",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d7abe9b5408302e4fd067f58ed6a50f22639dd61b65a184287310bb1a3869bbf",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectivePullbackFrames:273",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectivePullbackFrames:273"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.pullbackRestrictIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePullback",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f8a3165b227bf2771be7264fe5cbb4033579c0f9088c0cad8128d2605215143b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePullback:659",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePullback:659"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.pullbackRestrictNatIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FramedPullback",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "71076538fd1bf2d462794075cbd94a029808fc763e5f8b4b597fe5b1909c1120",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FramedPullback:1626",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FramedPullback:1626"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.pullbackSection",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "742f9692410bcd9154c155e80eb56b456331e3b2dfbfab2e4d98e860804dab7c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor:3952",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor:3952"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.pullbackSection_surjective_of_idealTensor_cohomology_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedUnitKernel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9225270667b9b91330572532db9f6672695ab9cf4d571d8078290332be285d24",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedUnitKernel:2969",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedUnitKernel:2969"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.pullbackSection_surjective_of_kernel_cohomology_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedSectionLifting",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "504aa3a6011dd7f8f115ca4a4b4fb892b3b1e385884ecdde08133fd56f663a65",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedSectionLifting:634",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedSectionLifting:634"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.pullbackUnitIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4dc846ca376a96d980c1b14711cd10716a86057935908a5dd8724c426ca57ba2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor:3180",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor:3180"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.pullbackUnit_adjunction",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b3c0f70e391c29f6f1c8cc2b00fea43320f72a422f552cd229c7743d4773ca66",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor:4322",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor:4322"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.pullback_endValue",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionPullback",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "741d0a330ee9e483e651fe405eae631620c034585db7decdfa8a1d11caad6e8e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionPullback:356",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionPullback:356"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.pullback_isFinitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ModulePullbackCoherent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bbd50d52b046b9edba6cbd083e0cf6bae23601fd910bc8ada93ffc59b49de42c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ModulePullbackCoherent:559",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ModulePullbackCoherent:559"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.pullback_isoOpen_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3b55e7a3f5389a7180b55dd7df70e2f64d354f9a61eda88bed9fc27b6d884b19",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleRestriction:421",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleRestriction:421"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.quasicoherent_pushforward_iso",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c498bb503fe9358a6c2b8862ce0e75c913c5208824b65ce990a3e5af0710aaed",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:3941",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:3941"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.rees_isBlowup",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0c2d051947a1c688de5735e2404fcfe0fa04ae6b530295e40812d66af798ccca",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing:264",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing:264"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.restrictPowerSection_factor",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPowerRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1959aa03e687810fe1ce5939b523112ea15c135f1357fb4b2769d334ae990fed",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPowerRestriction:3979",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPowerRestriction:3979"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.restrictScalar",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d8631d835724dc08e0b7a6d36c62fd1b4d073f67fba450640dacd3e57a17e276",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler:388",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler:388"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.restrictScalar_appIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1fb4f5c76f750d4562da9ff94d81b069097ff62baadbb9aa78528750083bd788",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:10454",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:10454"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.restrictScalar_naturality",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "674e5f47d894fb3dfbd9103bf4e50044729cdd3a050a372adbd5596d118d0c97",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler:499",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler:499"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.restrictedOpenSections",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "59e711e11a5b22fa0a24d20d3bca5db168d7fcde2f68e920185fc9adf7e3b93b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:11047",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:11047"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.restrictedPullbackFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectivePullbackFrames",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b2ad04171d8b40ec644891360bfacaadd5893a04a9b14730f98d5a333303a49d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectivePullbackFrames:4328",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectivePullbackFrames:4328"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.restrictedPullbackFrame_coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectivePullbackFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6bdef6c0062a493baee640f8a5922ca1e082380472d290f4e5b86911dce8cea5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectivePullbackFrames:4676",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectivePullbackFrames:4676"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.schemeHasExt",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6a389f26a6ae3c63aea0a38519bac54a12261997a5f071beb9d6671238685f12",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler:3474",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler:3474"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.sectionImageIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f8263a6677b4593c63b1f77dd541c87bf514d2280fadbab5305c21e35dff2da9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:329",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:329"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_038.jsonl"
