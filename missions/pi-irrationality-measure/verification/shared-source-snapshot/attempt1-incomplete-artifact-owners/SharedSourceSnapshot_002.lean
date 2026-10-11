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
      sourceName := "OAI.PiExponent.BranchContactIdeal.exists_generator_colength_eq_contact",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.BranchContactIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3d0766307d948524906f01b9f83b44b184b1bd59bfff464f3e41d22a0bfdbe98",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.BranchContactIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.BranchContactIdeal:1580"
    },
    {
      sourceName := "OAI.PiExponent.BranchContactIdeal.powerIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.BranchContactIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9ee1f24bb67929abbda4c316aae092e62c979e8b2edad92ee08188b6071fb936",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.BranchContactIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.BranchContactIdeal:350"
    },
    {
      sourceName := "OAI.PiExponent.BranchContactIdeal.powerIdeal_eq_singleton",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.BranchContactIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "99bf19abbcd6c88588197a81df30172c62a030dc411ddea2ba34eefe2d374afd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.BranchContactIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.BranchContactIdeal:460"
    },
    {
      sourceName := "OAI.PiExponent.CanonicalRecoveryProperties.ComapBijective",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CanonicalRecoveryProperties",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f8cb5f707b7913bef5abcff8e88fe98208035c3a888a2f62cc8669052500ed89",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CanonicalRecoveryProperties",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CanonicalRecoveryProperties:348"
    },
    {
      sourceName := "OAI.PiExponent.CanonicalRecoveryProperties.OrdinaryBijective",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CanonicalRecoveryProperties",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c9a5c0bb5f84798a1a2b08d018275ee23f39f355845ae17ea3594fde961f9a58",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CanonicalRecoveryProperties",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CanonicalRecoveryProperties:531"
    },
    {
      sourceName := "OAI.PiExponent.CartierDegreeLength.cartier_euler_difference_eq_sum_local_lengths",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CartierDegreeLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "97d05dfab8a477397666daff25d60307f63c11fcc394747907576f7475080a0a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CartierDegreeLength",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CartierDegreeLength:502"
    },
    {
      sourceName := "OAI.PiExponent.CartierPowerFrames.sectionMultiplyLeft",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CartierPowerFrames",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9d0cb61edcb91dbb2f4e1f4f241d11a1c826608720011777bb4f6e281094a6b1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CartierPowerFrames",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CartierPowerFrames:353"
    },
    {
      sourceName := "OAI.PiExponent.CartierPowerFrames.tensorFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CartierPowerFrames",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4051e5f8824aa788c7a7eb9f90874ab17ae522964f52b71c86370ecb8f938bc9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CartierPowerFrames",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CartierPowerFrames:521"
    },
    {
      sourceName := "OAI.PiExponent.CartierPowerFrames.tensorUnitTwist",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CartierPowerFrames",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "acbe0967e78cb4fdc4f3acce6f4a8f01864c19ea43d90143422db1a3588a6d8e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CartierPowerFrames",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CartierPowerFrames:823"
    },
    {
      sourceName := "OAI.PiExponent.CartierPowerFrames.tensor_multiply_framed",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CartierPowerFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e49147bdcb64e832b19b2f72f160b125a209e901dd823bd258b3660580f66e38",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CartierPowerFrames",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CartierPowerFrames:1972"
    },
    {
      sourceName := "OAI.PiExponent.CartierPowerFrames.tensor_multiply_ideal",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CartierPowerFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "936f827d5813e7f51fc0d866cffa8d4fdab5d08750e5179bcb2da47341f4fd77",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CartierPowerFrames",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CartierPowerFrames:4416"
    },
    {
      sourceName := "OAI.PiExponent.ClosedImmersionSerreTransfer.baseScalars_comp_actual",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardLinear",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "04f59543fb596e8297b7a545c9e109da79b3ccd5ba289212e324c96b1b224441",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardLinear",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardLinear:605"
    },
    {
      sourceName := "OAI.PiExponent.ClosedImmersionSerreTransfer.closedCohomologyEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7dfbb839e4dddc771ce50255c86c24aeb71fba6356cb807e5b5909a133aa0f1d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer:4040"
    },
    {
      sourceName := "OAI.PiExponent.ClosedImmersionSerreTransfer.closedPushforwardLinearSourceHasExt",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardLinear",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cc6f9e3851f54cdd3a517d88b61c9c20f8a9c7e5a0f5cb588c5e0424271a87a9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardLinear",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardLinear:421"
    },
    {
      sourceName := "OAI.PiExponent.ClosedImmersionSerreTransfer.closedPushforwardLinearTargetHasExt",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardLinear",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9b3d02287a530ff25beba566af7facf5df9f2a9e11935fdb67d3871c2a9ca0ee",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardLinear",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardLinear:512"
    },
    {
      sourceName := "OAI.PiExponent.ClosedImmersionSerreTransfer.cohomologyEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bb0127f83ed32a6da3ad193b59fd54993469f39ebc8f04e05ae125b42abccebe",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer:3292"
    },
    {
      sourceName := "OAI.PiExponent.ClosedImmersionSerreTransfer.cohomologyLinearEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardLinear",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c145a1a9fd7dd5cff68d3da7f4e757390e8924115f116d210f1ac90d900d60cb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardLinear",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardLinear:4237"
    },
    {
      sourceName := "OAI.PiExponent.ClosedImmersionSerreTransfer.cohomologyLinearMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardLinear",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3ea841d928172c74b318ad7db1e835781490e67764b01c3726e8c1b2ae9ff75a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardLinear",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardLinear:2843"
    },
    {
      sourceName := "OAI.PiExponent.ClosedImmersionSerreTransfer.cohomologyLinearMap_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardLinear",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a8ca77abe8bcd6112af90235360a90b25fc9bc444127805bf2ccbdca95f0eafa",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardLinear",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardLinear:4067"
    },
    {
      sourceName := "OAI.PiExponent.ClosedImmersionSerreTransfer.cohomologyMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "43f47264c009c3647df7e4e964604065c2aee5067829983962f01672e789fc60",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer:2307"
    },
    {
      sourceName := "OAI.PiExponent.ClosedImmersionSerreTransfer.cohomologyMap_bijective",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2231002362df78896be1a80ff817a555560bcfdaf00040a3715ee43106a57c43",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer:2622"
    },
    {
      sourceName := "OAI.PiExponent.ClosedImmersionSerreTransfer.cohomologyMap_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardLinear",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c00244bc6f7043ca4d657618a7e30e7eb13136cb8fbf4913cf21eaf6b5e08a9c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardLinear",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardLinear:1852"
    },
    {
      sourceName := "OAI.PiExponent.ClosedImmersionSerreTransfer.finiteDimensional_of_pushforward",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardLinear",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "63f2030bd7ec91b4c399f39285de3b6073a7883255ce3365411644443e441ec8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardLinear",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardLinear:4732"
    },
    {
      sourceName := "OAI.PiExponent.ClosedImmersionSerreTransfer.globalHom_push",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aa81c1cff1ffbc81fff3001c3cc479b5d3fe102cfd77e9161dc90b14e40c6c76",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer:708"
    },
    {
      sourceName := "OAI.PiExponent.ClosedImmersionSerreTransfer.globalHom_push_bijective",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2a0369215dc0fc89f784e702901f41fe9c00c34830a2034005a98d4714840236",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer:1070"
    },
    {
      sourceName := "OAI.PiExponent.ClosedImmersionSerreTransfer.instHasExtModules_oAI",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5fced2782c3d8bc531a10abe2593e7f23f1bf9ca9bcd13302b38d1f4c4bc9f5b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer:2112"
    },
    {
      sourceName := "OAI.PiExponent.ClosedImmersionSerreTransfer.instHasExtModules_oAI_1",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2cf75479166033a9b3edae4c944b97d56a11c82c1dfc06e6424afe40f7f8bb1f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer:2174"
    },
    {
      sourceName := "OAI.PiExponent.ClosedImmersionSerreTransfer.instHasExtModules_oAI_2",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSerreTransfer",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2486b03e4bd217894398684625c76a539ff3f15ee174dce996ae1b58846c3683",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSerreTransfer",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSerreTransfer:487"
    },
    {
      sourceName := "OAI.PiExponent.ClosedImmersionSerreTransfer.instHasExtModules_oAI_3",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSerreTransfer",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "20cf990b2eb2fba1030984b078b7b9e40320eaf63eeb69ab5dca68a5121fcbad",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSerreTransfer",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSerreTransfer:547"
    },
    {
      sourceName := "OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f4fb839a7aed235255d63da7083a6d0fe6cffdaf04c1ba86a5fade1f36c72c76",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer:1753"
    },
    {
      sourceName := "OAI.PiExponent.ClosedImmersionSerreTransfer.scalar_naturality",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardLinear",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6805c686d3db0797e9cc53f86182c3417fb485e54b74eb85ee1fa5193018e46a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardLinear",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardLinear:854"
    },
    {
      sourceName := "OAI.PiExponent.ClosedImmersionSerreTransfer.structureMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "20652159de75d75d021dc170b85c5dffc6294cb6f2c56fc40bcd09cb3983021a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer:548"
    },
    {
      sourceName := "OAI.PiExponent.ClosedImmersionSerreTransfer.typedCohomologyMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardLinear",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3a051679004464c9e0a6195cfee597c066bf956d1c83947e2f4c5a8a0c424051",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardLinear",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardLinear:2223"
    },
    {
      sourceName := "OAI.PiExponent.ClosedImmersionSerreTransfer.typedCohomologyMap_bijective",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardLinear",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5dd2a0f4991b9e1940bcb9d254ac49da06a44e87884809511e29ffffe3b37a4c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardLinear",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardLinear:2690"
    },
    {
      sourceName := "OAI.PiExponent.ClosedImmersionSerreTransfer.typedCohomologyMap_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardLinear",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2ce4f45d4a89c43f49977cc71a7698747a12e41ca0075978206914ca9a0b6c3e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardLinear",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardLinear:2380"
    },
    {
      sourceName := "OAI.PiExponent.ClosedPushforwardAffine.affine_exists_finitePresentation_of_sections",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardAffine",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "761b69d35bc8e48e5c8387ea12231e68e3204693d2b268b6d6f54ead5a21000c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardAffine",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardAffine:2826"
    },
    {
      sourceName := "OAI.PiExponent.ClosedPushforwardAffine.affine_pushforward_exists_finitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardAffine",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c1e60ca457227db197e86562416a1217e3e5fc9dc962a73469c9a7ca4e8eb7ca",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardAffine",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardAffine:4203"
    },
    {
      sourceName := "OAI.PiExponent.ClosedPushforwardAffine.affine_pushforward_quasicoherent",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardAffine",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6f4a1ea8859a652ff729a7423275a8423fc41b4bf6f855358c4607b22a6d96c7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardAffine",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardAffine:625"
    },
    {
      sourceName := "OAI.PiExponent.ClosedPushforwardAffine.affine_pushforward_sections_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardAffine",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1ba04c64a35ab15a02fd9f06099a95ebe1eb1f1e780956040cf420e48b73bdd1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardAffine",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardAffine:1919"
    },
    {
      sourceName := "OAI.PiExponent.ClosedRestrictionTensor.powerProjectionIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedRestrictionTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f59aedace85d4b20aa571f5ef6a4b4dc4f9e7849fd5cb276f948618e198fbeb7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedRestrictionTensor",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedRestrictionTensor:2093"
    },
    {
      sourceName := "OAI.PiExponent.ClosedRestrictionTensor.powerProjectionIso_succ_pure",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedRestrictionTensor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0d9d10e50ed79b5e20961f2b86d562ba1cf8c5d03190c5fb3f06c4ecefafdf04",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedRestrictionTensor:2718",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedRestrictionTensor:2718"
    },
    {
      sourceName := "OAI.PiExponent.ClosedRestrictionTensor.powerUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedRestrictionTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a01101ce6f5df48f0fe0ff850b6f21ee182bd2fc848c0e267aaa06cbc0580050",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedRestrictionTensor",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedRestrictionTensor:2423"
    },
    {
      sourceName := "OAI.PiExponent.ClosedRestrictionTensor.powerUnit_succ_pure",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedRestrictionTensor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "727641ee67035cb01011811604390f3236052a2c3c7459e7fa38a43ab3ae6814",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedRestrictionTensor:4685",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedRestrictionTensor:4685"
    },
    {
      sourceName := "OAI.PiExponent.ClosedRestrictionTensor.push_pullbackSection",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedRestrictionTensor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2fb87bf191835d4622dc6524e4fa091c4d1d8781b78658731dc8dbeccae3ebc9",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedRestrictionTensor:10382",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedRestrictionTensor:10382"
    },
    {
      sourceName := "OAI.PiExponent.ClosedRestrictionTensor.twist_structureMap_power",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedRestrictionTensor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b29c4c2f059b9848cb4d28a71897343023c021707049194bf33fbe180ef5d1af",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedRestrictionTensor:7361",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedRestrictionTensor:7361"
    },
    {
      sourceName := "OAI.PiExponent.CoherentAffineFinite.LocallyFinitelyGenerated",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "02c62090fe86d947290936494295506dccd8bb5367a220b9916f52bedaaf4b5e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite:3312"
    },
    {
      sourceName := "OAI.PiExponent.CoherentAffineFinite.LocallyFinitelyGenerated.restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7a4332db8d93c9eaac98d99578aab9491a9fff8d5fb292e86caf1af4c6093ada",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite:8244"
    },
    {
      sourceName := "OAI.PiExponent.CoherentAffineFinite.affine_exists_finite_generators",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8d79971bc33781ab8ae218119a99a4d2580c3c284b524bb5375826db220d5afb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite:13815"
    },
    {
      sourceName := "OAI.PiExponent.CoherentAffineFinite.affine_open_sections_finite_of_generators",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "552b3b95f531ebc09c6441ebf57362d04dcfb6c45a9898a26a29884612e5de9e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite:5372"
    },
    {
      sourceName := "OAI.PiExponent.CoherentAffineFinite.affine_sections_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c2ed98e83d51b71ffb6e0c7d8e171af3371b22ec495fe2f7f410b6895b333ff3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite:10561"
    },
    {
      sourceName := "OAI.PiExponent.CoherentAffineFinite.affine_sections_finite_of_generators",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2e6f6131347ff0ab4179b8f05632ec9fa010c28711acd456af36bdd5fec01636",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite:1818"
    },
    {
      sourceName := "OAI.PiExponent.CoherentAffineFinite.affine_sections_finite_of_localGenerators",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "70b4bbc2d8f7413ff01e5664f69b40f4dd43eb690d78a50c09bd47f7a79658b8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite:9412"
    },
    {
      sourceName := "OAI.PiExponent.CoherentAffineFinite.finite_generators_of_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "90257a62149419facc797cdd4d983b44ad191689891c0f040f0dc2f3c0168023",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite:4521"
    },
    {
      sourceName := "OAI.PiExponent.CoherentAffineFinite.finite_isoSpec_sections",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d582c66f3ff5939446f1080c3ebe798a05dbc4f14c1f8a747525254377d601e1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite:10862"
    },
    {
      sourceName := "OAI.PiExponent.CoherentAffineFinite.locallyFinitelyGenerated_of_finitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "61d1595ddd2a5f36080db17b4b581e82b0aba4f35a57f9870e526b3e03019aae",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite:3496"
    },
    {
      sourceName := "OAI.PiExponent.CoherentAffineFinite.spec_exists_finite_generators",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8a7790248b74886e1b457c82d2574e35a4129bb79e00e917f01fbd5cc48dc35b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite:12257"
    },
    {
      sourceName := "OAI.PiExponent.CoherentAffineFinite.spec_sections_finite_of_generators",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "470d6d873cc8d0ca7d0163d2cb98145ea8de1dcda510fcdf1d987dcf215ccc7b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite:659"
    },
    {
      sourceName := "OAI.PiExponent.CoherentAffineFinite.spec_sections_finite_of_localGenerators",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "04240c5e255985354553dcb553425d504c5e801eb48c7ca7cff505dda6641735",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite:6222"
    },
    {
      sourceName := "OAI.PiExponent.CoherentCokernels.affine_cokernel_exists_finitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentCokernels",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7be5affc8a26ac9a7117ae8d14c575b6f0ce43f9a93c3ce647fa5cf02cdf0b77",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentCokernels",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentCokernels:2533"
    },
    {
      sourceName := "OAI.PiExponent.CoherentCokernels.cokernel_isFinitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentCokernels",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ef4f7133b7fc3ec520b6840bce23e9e39bca258c06052c11de69fd7bffad9d85",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentCokernels",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentCokernels:4208"
    },
    {
      sourceName := "OAI.PiExponent.CoherentCokernels.specCokernelIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentCokernels",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "53be7951152742e787ae4de0ca10b9759dbb52fb23c5f6bdd30cab4ca0ec0e52",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentCokernels",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentCokernels:552"
    },
    {
      sourceName := "OAI.PiExponent.CoherentCokernels.spec_cokernel_exists_finitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentCokernels",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3ac54660da4a8abef5722b27d5fdf86449aaa8b2ab561fa8cd9163699acf7cb5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentCokernels",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentCokernels:1579"
    },
    {
      sourceName := "OAI.PiExponent.CoherentExtFiniteness.CoherentFinitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      graphKind := "inductive",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a85740f7e6028539be995d387156390e1d42a664390a9ce06f8c0062c194dfa0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness:4238"
    },
    {
      sourceName := "OAI.PiExponent.CoherentExtFiniteness.CoherentFinitePresentation.casesOn",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3def0069094861e40cc94ec11997d285d04a8de80997d1543fd57365d3dbe2ef",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness:4238"
    },
    {
      sourceName := "OAI.PiExponent.CoherentExtFiniteness.CoherentFinitePresentation.comp_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "75e5aa64631665069e49c59d2972760506a711c9d7d07a4823c6398ae4de10fb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness:4238"
    },
    {
      sourceName := "OAI.PiExponent.CoherentExtFiniteness.CoherentFinitePresentation.kernel",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a3515cc662cc3ddc3a81a663a1e3b16e54b06e8d4a2f574c8cf3108baae65445",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness:4238"
    },
    {
      sourceName := "OAI.PiExponent.CoherentExtFiniteness.CoherentFinitePresentation.kernel_coherent",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7bdbac7c8c0d428ff3ecc71dea107e5632c55307deeca432067a383d2ecdac98",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness:4238"
    },
    {
      sourceName := "OAI.PiExponent.CoherentExtFiniteness.CoherentFinitePresentation.left",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "03c24d5509d640b478b81e3da021b0258d9c9c7dc83cf61a7e094c4f018d6b11",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness:4238"
    },
    {
      sourceName := "OAI.PiExponent.CoherentExtFiniteness.CoherentFinitePresentation.middle",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eed0ea59a8126a1c78304ce70e4bff766f4a4fa2cff9edebc01cf2ce9f48596e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness:4238"
    },
    {
      sourceName := "OAI.PiExponent.CoherentExtFiniteness.CoherentFinitePresentation.middle_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "789e3a14a8084edc617b36296fbec4e2a2312469962c2e0d0e432004530f2745",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness:4238"
    },
    {
      sourceName := "OAI.PiExponent.CoherentExtFiniteness.CoherentFinitePresentation.mk",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      graphKind := "ctor",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "205c224ea084f3dfc10bc5296e70187fbeea534a51d9d605db93d5e963afdc74",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness:4238"
    },
    {
      sourceName := "OAI.PiExponent.CoherentExtFiniteness.CoherentFinitePresentation.mk.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8302956a4c86fda745a40701a81038ee2f226334ab18e4cb3f14ab01f80edb37",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness:4238"
    },
    {
      sourceName := "OAI.PiExponent.CoherentExtFiniteness.CoherentFinitePresentation.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5e163d2ce62786e847bc85687f0176b2ad16d1e95a39f67422b4d682f9dd6d68",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness:4238"
    },
    {
      sourceName := "OAI.PiExponent.CoherentExtFiniteness.CoherentFinitePresentation.rec",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      graphKind := "rec",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "176e39124ead210ae0c1cebf8a413621cbf0289b180caab2acf7436350149c84",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness:4238"
    },
    {
      sourceName := "OAI.PiExponent.CoherentExtFiniteness.CoherentFinitePresentation.recOn",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3293790481b3a43c243d6783d5a66598d0729c3048ffc265b61a82dfd9d0f7a3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness:4238"
    },
    {
      sourceName := "OAI.PiExponent.CoherentExtFiniteness.CoherentFinitePresentation.right",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c008986db348b3291f7972c501cda444003223bf34c8a4cf73c8ef3e7594ec65",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness:4238"
    },
    {
      sourceName := "OAI.PiExponent.CoherentExtFiniteness.CoherentFinitePresentation.shortExact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4ce78f0312e10663ce6333bae33cc0bf2be85195cd24b05c1aae77cd41a650a0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness:4238"
    },
    {
      sourceName := "OAI.PiExponent.CoherentExtFiniteness.FiniteCohomologyPresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      graphKind := "inductive",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "28a988700cb81bf74d8ca7ce368b5200788faac0105b813924506669304e3cb0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness:1738"
    },
    {
      sourceName := "OAI.PiExponent.CoherentExtFiniteness.FiniteCohomologyPresentation.casesOn",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2fab91abf8a8636f60b8669be246c98c98438f2d4477058d67d897a90c3afe70",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness:1738"
    },
    {
      sourceName := "OAI.PiExponent.CoherentExtFiniteness.FiniteCohomologyPresentation.comp_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9e8ebf8d0f5fa0244efd8f2b6bde8f523696dd3e97f594448a4cb3899f3cc7ca",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness:1738"
    },
    {
      sourceName := "OAI.PiExponent.CoherentExtFiniteness.FiniteCohomologyPresentation.finite",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dc8d9739ca35566b2a09eb3a97065439ee60ed7195fc4ba87653c626eb16a174",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness:1738"
    },
    {
      sourceName := "OAI.PiExponent.CoherentExtFiniteness.FiniteCohomologyPresentation.kernel",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7ec4264aa22b73ddbb6a8feeb18576214c52c54e3e8bfefc47f707b711e2fe67",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness:1738"
    },
    {
      sourceName := "OAI.PiExponent.CoherentExtFiniteness.FiniteCohomologyPresentation.left",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "186128892abcaf0f52af08cb0cabe8ad54ba09184ac19195d9adbdf5ccc5014b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness:1738"
    },
    {
      sourceName := "OAI.PiExponent.CoherentExtFiniteness.FiniteCohomologyPresentation.middle",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "242b73344baa41a5101f8e945fc17642253c099107c14d5a8c8432d3f5e79a34",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness:1738"
    },
    {
      sourceName := "OAI.PiExponent.CoherentExtFiniteness.FiniteCohomologyPresentation.mk",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      graphKind := "ctor",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4390dff30ba35c07012cf617fcc056c9477dbae9508446a9527131e59a3c1ede",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness:1738"
    },
    {
      sourceName := "OAI.PiExponent.CoherentExtFiniteness.FiniteCohomologyPresentation.mk.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6696427cc241c19b53790481c0310101833339e6873cdad35ef6116dbead5199",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness:1738"
    },
    {
      sourceName := "OAI.PiExponent.CoherentExtFiniteness.FiniteCohomologyPresentation.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d837da9f84f5cfdf2065636fcedca1f9c035b7ddcbd3cde176b76b588cff1bce",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness:1738"
    },
    {
      sourceName := "OAI.PiExponent.CoherentExtFiniteness.FiniteCohomologyPresentation.rec",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      graphKind := "rec",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fd2258ddd123c5ab3fa71205a54e3ff1c9c2f8fa3e9b87cb66d1de7b71f78f4b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness:1738"
    },
    {
      sourceName := "OAI.PiExponent.CoherentExtFiniteness.FiniteCohomologyPresentation.recOn",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "076a9e820cce38da5288d27376500790980f527890e3cf19f03653003c4d0653",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness:1738"
    },
    {
      sourceName := "OAI.PiExponent.CoherentExtFiniteness.FiniteCohomologyPresentation.right",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6ebcf59989a8546a5d53404cf2d2e70dc5c8c1194fcc3e710caaa3dab216b7bd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness:1738"
    },
    {
      sourceName := "OAI.PiExponent.CoherentExtFiniteness.FiniteCohomologyPresentation.shortExact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f0c869b961a136bff35e4cedffa354694b5bc97f3f9925a9d77ed145195f5345",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness:1738"
    },
    {
      sourceName := "OAI.PiExponent.CoherentExtFiniteness.coherent_cohomology_finite_of_presentations",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d96947dd9f88301d17af6f775fc08bc0d0b7e2003589fce37f0bd9e552bf7192",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness:4719"
    },
    {
      sourceName := "OAI.PiExponent.CoherentExtFiniteness.cohomology_finite_of_biproduct",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1ea7436ff1b85280b3dc57dc52113d861ffefe995178961b62520694e7fe7373",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness:3331"
    },
    {
      sourceName := "OAI.PiExponent.CoherentExtFiniteness.extLinearEquivBiproduct",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bfa3894460cc50551e8f83eba5f41896d86db67b7a07981df9e21d5104869f88",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness:927"
    },
    {
      sourceName := "OAI.PiExponent.CoherentExtFiniteness.ext_finite_of_biproduct",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1e2dd7a26039202edc52a448ce2d7c2343073fea2ff3d7a41c251e92dd70908d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness:1275"
    },
    {
      sourceName := "OAI.PiExponent.CoherentExtFiniteness.ext_finite_of_presentations",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a92b7145bdc9a83489e9b164913e6ae60a62ccb046482c475b3913b17dda02b8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness:2073"
    },
    {
      sourceName := "OAI.PiExponent.CoherentExtFiniteness.finite_middle_of_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "00a1348592f704573631c5575cfdabe8e04c3943006405d840ae80075b649686",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness:326"
    },
    {
      sourceName := "OAI.PiExponent.CoherentProjectiveFinite.coherent_cohomology_finite_of_inverse_powers",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentInverseFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f1fd2dbaa0b1f2563e3c1c5547547dd9da42c416c9ec8479f7a4ddc304ff5836",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentInverseFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentInverseFinite:2380"
    },
    {
      sourceName := "OAI.PiExponent.CoherentProjectiveFinite.coherent_cohomology_finite_of_standard_twists",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CoherentProjectiveFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ae52130d213509a503d055f59fd124a13e152e9e9e59972a239f3bd648945364",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CoherentProjectiveFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CoherentProjectiveFinite:438"
    },
    {
      sourceName := "OAI.PiExponent.CoherentTwist.app_zero_of_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9cfd259322df84b369f9a2821193c59292992c63f346e3b0360548db8a6c85b0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:2822"
    },
    {
      sourceName := "OAI.PiExponent.CoherentTwist.epi_of_local",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2b340d403cd48da3fc120a4b94682db1cd9674c1f70f33516920f6e4413b3eb6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:4410"
    },
    {
      sourceName := "OAI.PiExponent.CoherentTwist.eq_zero_of_local",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b72cbc6212cbb7dc135cd19f2c20f0de558f0c7c9b953379580ddbce1a6ff489",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:3430"
    },
    {
      sourceName := "OAI.PiExponent.CoherentTwist.exact_of_local",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e9c9a0cea60ec4293f8f9fae3348bd1281243bffede1cb3d6d422b7d92402982",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:5346"
    },
    {
      sourceName := "OAI.PiExponent.CoherentTwist.mono_of_local",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eabc4ba7a878908eff507eb85224078e502ede7c5a18347e6766b091be1b76a8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:4872"
    },
    {
      sourceName := "OAI.PiExponent.CohomologyFiniteness.CohomologyFinite",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CohomologyFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "af4aa8a37d6920e877999df6e09330b16d99152fb62c2517a4e1260f7db4f46f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CohomologyFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CohomologyFinite:434"
    },
    {
      sourceName := "OAI.PiExponent.CohomologyFiniteness.closedPushforward_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CohomologyFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "13c000443c122d461bbd3715c4ed4793fc05c5a06baaaf45ba6039c18bc07dce",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CohomologyFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CohomologyFinite:1440"
    },
    {
      sourceName := "OAI.PiExponent.CohomologyFiniteness.finiteDimensional",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CohomologyFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2d015083c62c0206a1ca63937355a23bbd126512f033db2b0044f2aca96a117a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CohomologyFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CohomologyFinite:633"
    },
    {
      sourceName := "OAI.PiExponent.CohomologyFiniteness.finiteIndex_coordinateBundle_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFiniteCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2cef328861b2bef3dcb52164db6aba3a3b671dfb9238ade09b24d02b794e612c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFiniteCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFiniteCoordinates:613"
    },
    {
      sourceName := "OAI.PiExponent.Collision.collisionRatio",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.CollisionExponential",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cfee77ef1030e1a7cd1a84c0c97f6a3cfc0240cdaabd30fa7c546e9a23b6532f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.CollisionExponential",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.CollisionExponential:149"
    },
    {
      sourceName := "OAI.PiExponent.Collision.collisionRemainder",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.CollisionExponential",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "38ec3a0ffe57deee1bc99c578f79b1682ecd3c715cb27913b6e30a139adf9937",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.CollisionExponential",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.CollisionExponential:3607"
    },
    {
      sourceName := "OAI.PiExponent.Collision.collision_geometric_sum_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.CollisionGeometricSum",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "353b71ec3f3acd2a7c700aba1f675c5b48011b2cc21fa6efcbfdc4173e756d6e",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.CollisionGeometricSum:1252",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.CollisionGeometricSum:1252"
    },
    {
      sourceName := "OAI.PiExponent.Collision.multiplicity",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.CollisionCombinatorics",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4e6ded2da2cb9d78d081724e1279de1b14e6a0a2e573f6a506afcde25a564b56",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.CollisionCombinatorics",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.CollisionCombinatorics:1120"
    },
    {
      sourceName := "OAI.PiExponent.Collision.sum_weight_ge_of_low_count_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.CollisionCombinatorics",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a807d9f19aeab422b7d9b15208ea3ebc15f311ac941216e59bfab3d72674a10e",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.CollisionCombinatorics:6196",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.CollisionCombinatorics:6196"
    },
    {
      sourceName := "OAI.PiExponent.Collision.twice_collision_count_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.CollisionExponential",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d3417cf915d29d15bbbc8b0f3eaa664b282aafa4e15008144e3369d264bd1e3c",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.CollisionExponential:1031",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.CollisionExponential:1031"
    },
    {
      sourceName := "OAI.PiExponent.CommutingTaylor.coeff_taylorHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1bc5c9531bfbe1a93e5593b304186a9917bf72c76577f0758c71f1af46c1a698",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:3634"
    },
    {
      sourceName := "OAI.PiExponent.CommutingTaylor.coeff_taylorHomFin",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e06f2b94169155c7d55d99c4a4109778954458b2dc07d9b5f48d951a739be476",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:4565"
    },
    {
      sourceName := "OAI.PiExponent.CommutingTaylor.coeff_taylorSeries",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b60fcb2412b6d8d8c35727eaa25b3d97fca937f78e5a8eb2c7eb11d012ac9a80",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:2452"
    },
    {
      sourceName := "OAI.PiExponent.CommutingTaylor.coeff_zero_residueTaylorFin",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e356114fb6cf15595b394c175a8df75e8b772f86d6ad774b289f01168d71faba",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:7715"
    },
    {
      sourceName := "OAI.PiExponent.CommutingTaylor.coeff_zero_taylorHomFin",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "603cdb3adc0a7f7eb9d17955d55da1c466ad8022e7dbf86bd3a2da1a6a293e3d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:6507"
    },
    {
      sourceName := "OAI.PiExponent.CommutingTaylor.constantCoeff_residueTaylorFin",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b829bd380ba88ff59568b070d95876ae29d5295f62a833a406ca0c8a48a2b4b7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:8242"
    },
    {
      sourceName := "OAI.PiExponent.CommutingTaylor.iter",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "86a0474915dafe9177965d3fad6cef1859ce8338e435dabb7562c8225883984c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:203"
    },
    {
      sourceName := "OAI.PiExponent.CommutingTaylor.iter_mul",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4eb12d2ef61d00d8e33518f9616d0da88ad8daf459c7a7d998b17200e650ebd5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:942"
    },
    {
      sourceName := "OAI.PiExponent.CommutingTaylor.iter_succ",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5399914e670a8c53616aed49ee076814c7b75f179d07a2f7926f02911821e124",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:373"
    },
    {
      sourceName := "OAI.PiExponent.CommutingTaylor.mixedIter",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9cd2e63f26c9bed8d2719c990af023cd1344378884ef57b397d29a6bbde004a6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:4056"
    },
    {
      sourceName := "OAI.PiExponent.CommutingTaylor.mixedIter_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "611d11e1d032cdb0f40aac87d001a3f82d0a351fbaab39e591d0e4cf0a1eabf6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:5768"
    },
    {
      sourceName := "OAI.PiExponent.CommutingTaylor.residueTaylorFin",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "28774f2bcba721aee3f431941a58880d96a6a5b4931a6da4ebae2123bb7fc4df",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:7126"
    },
    {
      sourceName := "OAI.PiExponent.CommutingTaylor.taylorHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0837850797181723a656951708a7be5a9c94631470c7e309e07d74390a2dad3e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:3138"
    },
    {
      sourceName := "OAI.PiExponent.CommutingTaylor.taylorHomFin",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b4a41fb9433f5b938abc505ce532c5328e7154eeff050b9cde1a51ab4e1084c4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:4278"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_002.jsonl"
