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
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTensorRightFunctor_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "db91374618779ed11c5de7de705a16e4bcd848f333d8cd7b3870348662215041",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:17535"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTensorRightFunctor_preservesZero",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6ae345dd65d2e8e129816f16a203eba489df2d4a57a4a8c1a1c4a74d19c65492",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:16904"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTensorRightFunctor_shortExact",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "92ced32bfcfad0ca6afd317987a09f84a7f19c71b75b21ff375a61ac80d679bd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:17997"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTensorRightUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b9200fdd13f25e68f2e1b973b18acfd204ebac21a88ee501be2406edc240e1c7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:13928"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTensorRightUnit_natural",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "004044e3c48481c3b69d30a3c545b36f3215b6c46de3815a59af103074be1cb2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:11424"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTensorRightUnit_natural_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4a44788e520c288cee44fb3f7795100983e561a9bbbe238b4a3176648e0ca5ec",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:11424"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTensorUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e67cdb5c982f16e473afe0fb302ac61e06c1d4963724d26b879329f4e4e87f5d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:8885"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTensorUnit_natural",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameTensorPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b125f3897b26abf271aa78b9f96d0d3db68e34e551a2f1fee1427452fff04b36",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameTensorPowers",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameTensorPowers:2864"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTensorUnit_scalar",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameTensorPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "14bb29558d20c4c4cb9ea9417eb23c048decc5c7ebc2a9dab44a6f8190859759",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameTensorPowers",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameTensorPowers:656"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTwistForward",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c5fafb53406a68f2c26ef38649d762beea03646d6a5f3b52825ec568d8e76cf5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistSections:2058"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTwistForward_frame",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionScalars",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1cd3aaef6ef38ec78dbe085e6e5794dacc6500f5df3444fcc6181924b4c075cd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionScalars",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionScalars:4174"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTwistFunctor",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "330083185a24d16bdc4d63d023fcb210f152b483c9c270cbc62fa248ee51196b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:19297"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTwistFunctor_add",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "23782ee79d1716b15ab5ddd82cd19104c4bf8a29b7cec70356aac897aee5f717",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:19786"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTwistFunctor_additive",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6865c6ec613b90441f033f5464b7e4f9cb328215d9a77c85d0ecfd720980e68e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:19467"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTwistFunctor_shortExact",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "694aeb5b31b1cc6ca1dc545666101452f10e4402b9325e43c014d8cecfbcce11",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:20270"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTwistPowerIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ModuleLinePowerLaws",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0ce6e680c42cfacfa83fd87a8aab4182f87326e00047deeade87600693e03b4e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ModuleLinePowerLaws",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ModuleLinePowerLaws:6578"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTwistPowerMulIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ModuleLinePowerLaws",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4ee03f194e1bb44eb14898f5b1942017b7113ee01f6b6c3797bd2b5412bb09ca",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ModuleLinePowerLaws",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ModuleLinePowerLaws:6996"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTwistRestrictFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ed9f61e895e24fbe044f0d969804484cff01972bc340bcf1c9b85e2efaa7f4db",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistSections:2810"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTwistSection",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c73dff59687ad4b638345fe769a156b9b84221abff44749d9444cbc41bd84d47",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistSections:1836"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTwistSection_add",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2c4e54f5a48b2451cb00ee05053694dab95fbc6dab664073d544393907f8b2ff",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistSections:2308"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTwistSection_frame",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionScalars",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "77137ae1e07979d4335b7d1083c607647d801fc56762f9fbf30f88ff11ba4091",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionScalars",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionScalars:5379"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTwistSection_unitIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistPowerSection",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1f07eccc779d9771a3ecdff08a554a3f2af8881c562322835f0a616afc7cca93",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistPowerSection",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistPowerSection:955"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTwistSection_unitIso_app",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistPowerSection",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7fe1c6fb3fee41d025a57064743d7f99934ed84ab8ffa76b9198388f495c656a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistPowerSection",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistPowerSection:3050"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTwistStep",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "08af348525f7e6a259735e79463e0eba70d2111366799facecfb45492b51be4a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistSections:1515"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleTwistUnitIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d751b925008526a24494915e2820bd7082e56530f564e3daf3f912770484f90d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
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
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerFrames",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerFrames:414"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.normalizedPowerFrame_coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "83212055ee4514c9db081c81d09be1c358437a7ea39a53f52a470cdbb506b9b5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerFrames",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerFrames:1177"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.normalizedPowerFrame_normalized",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6122cdadf052afcd8fe826271c02db39a5fa0767c74d1518b55f8d24235d489f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerFrames",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerFrames:807"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.openImmersionTop",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8c0849dc361b177263bcd4ace531834f370f2c196d4fbd5ae41a0ae208859815",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:12880"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.openImmersionTop_localize",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0449300d580c3aa29d4cf340027324c9cde73654157c365427ea1ddbe99101b4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:13312"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.openRestriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9904b097a763c4bc7c8390d8abdcd790e572b455c809993d2cef4670f029af2e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:2933"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.openSectionIso",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteSupportLocalIso",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9331f493fecba9bd4898187765425bf05a3ed31fbb921b6e2a465ba6645a863d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteSupportLocalIso",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteSupportLocalIso:1848"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.openSectionModule",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteSupportLocalIso",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1f3d76f299a54bcc6141d85d85253bd2351b9f0aada0b60e31e2bccbd87e01c8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteSupportLocalIso",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteSupportLocalIso:386"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.openSectionRestriction",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteSupportLocalIso",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "99e85c399bc1eb9e279fec2f0590e8307be85f4de97f6dd70e9bc5148186ed73",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteSupportLocalIso",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteSupportLocalIso:606"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.openSectionsCongr",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ab2f2e013d442ebb893119e94b2c4bccde7414f743d91c4770b4aec080b52f02",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:6603"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.openSectionsCongr_restriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "baa09aaf304dd4485f04b97ab0941012a8c41a1cb76332bea189fbfe862c0072",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:6778"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.openTopSections",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "259a1ac42efad34cc30f2422c04754592abf4e573a92a273770988e0add875d6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:8661"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.opensMap_final",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePullback",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c9572eb6625ba886e1c43e2f0aa7a7c99679259a462fcb6d0f35f17d5816e088",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePullback",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePullback:312"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.overFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteLineEuler",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "095e7735312f03f84b3c7d0db2acac81060fafed9e2057f61938c71149b94380",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteLineEuler",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteLineEuler:351"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.powerChartIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalPowerSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "52c4c2345a47be20098fadacc3e95a4c690652cd844d3e99da97fc61d6dee6f6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalPowerSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalPowerSections:4221"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.powerRestrictionUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPowerRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "68c3ab20fda9c7e9dffcd3348f76307732e66aca0918ef5f8cf78112603bfa9a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPowerRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPowerRestriction:3566"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.powerSection",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c90a34ca3dfc4796c1350283c7b293f75e825132c999ff94daa4f6493e35da80",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:13092"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.powerSection_coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameTensorPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "18919009f8b1ddd37d72d9b97b510f3b31e653cbc9dfb73e2fc550428b8937d9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameTensorPowers",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameTensorPowers:6168"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.powerSection_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f29c69f47eebb5abdc85222e530da98d32afbf606ebbbb8a8942b2b2b4b92370",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:13758"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.powerSection_restrict_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPowerRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aa2767b3c390291995bcde4a024f0c65f2de9b8dc8cfd2d51d3ba6f01e3d86a2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPowerRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPowerRestriction:2720"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.powerSection_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "afb4a888aa9fbb9224043ccb52eebf53c41ce806196d6967592b6812454a4a9b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:13259"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.presents_morphismRestrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupPresentationRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e313de4bc7558c94e3196ac792af83f0888c11be6e6d45378931bf383ad87a82",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupPresentationRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupPresentationRestriction:1018"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.presents_post_toSpec",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupPresentationRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bd2e7983eb6a3e5ea57fae67ba008258207c28229c75019f04d477e08da750a0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupPresentationRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupPresentationRestriction:402"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.proper_closed_finite_of_dimension_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d3495ddf94bff779136ac09015fc28a4df9e41ee481faa789ac265fb1a0111b2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros:5011"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.proper_finite_euler",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9722737252c550bca81cc3e606d599781a4c638f8d1c35a2f1403547e3cdb2fa",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros:9367"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.proper_finite_euler_eq_sum_stalk_finrank",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d7e9f3dd429b59196563c4cef4aae6dfc7951f8f8d88d06f18eb0a7c6bc85b41",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros:10136"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.proper_finite_euler_eq_sum_stalk_lengths",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "abc6ab5ba63ae185d56093972b425cc3146fab9c181c4371f830261ad95c8259",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros:10564"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.proper_finite_finrank_eq_sum_stalks",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "319d1f57de9ea6e077226be1fe5c52469a54cff83aabdcf5d7d5045978509f6a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros:7576"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.proper_finite_functions",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6b88308f28041494e75472583f8f2e43073d558bd5ad4a2eddcbbe22b1e0e7af",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros:874"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.proper_finite_germ_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ec99a4e94dce9c3f131c6860ac3ddaf13d4880c8e3261e96517bf3099e68a9e2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros:1413"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.proper_finite_scheme_isAffine",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9a38a352b73816131f344c1d3e2dc26c1ea9587fe61acf73bc0b16ca90b461ad",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros:661"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.proper_finite_scheme_isFinite",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "05c2481fcc46b74c0682961c1989d7b9aabfa244e949c6f8388ae6332cbb7509",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros:428"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.proper_irreducible_closed_subsingleton",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "083c1f4c2a41302ebb911f96a753f22ba8a1de6a9cc5599d57bd33c2636ee216",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros:4036"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.pullbackFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8f7f85d98f3a8a6b7881c0d993f3e870cd133e600dc291ebaca8eca6a009bb93",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor:4138"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.pullbackPowerSection",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cd9ec1ff0d2d6ade32716f3b7eea69e2205fa01a758097927ee262e92bd1cf59",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleRestriction",
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
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectivePullbackFrames",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectivePullbackFrames:273"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.pullbackRestrictIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePullback",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f8a3165b227bf2771be7264fe5cbb4033579c0f9088c0cad8128d2605215143b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePullback",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePullback:659"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.pullbackRestrictNatIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FramedPullback",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "71076538fd1bf2d462794075cbd94a029808fc763e5f8b4b597fe5b1909c1120",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FramedPullback",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FramedPullback:1626"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.pullbackSection",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "742f9692410bcd9154c155e80eb56b456331e3b2dfbfab2e4d98e860804dab7c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor:3952"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.pullbackUnitIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4dc846ca376a96d980c1b14711cd10716a86057935908a5dd8724c426ca57ba2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor:3180"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.pullbackUnit_adjunction",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b3c0f70e391c29f6f1c8cc2b00fea43320f72a422f552cd229c7743d4773ca66",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor:4322"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.pullback_endValue",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionPullback",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "741d0a330ee9e483e651fe405eae631620c034585db7decdfa8a1d11caad6e8e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionPullback",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionPullback:356"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.pullback_isFinitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ModulePullbackCoherent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bbd50d52b046b9edba6cbd083e0cf6bae23601fd910bc8ada93ffc59b49de42c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ModulePullbackCoherent",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ModulePullbackCoherent:559"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.pullback_isoOpen_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3b55e7a3f5389a7180b55dd7df70e2f64d354f9a61eda88bed9fc27b6d884b19",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleRestriction:421"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.quasicoherent_pushforward_iso",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c498bb503fe9358a6c2b8862ce0e75c913c5208824b65ce990a3e5af0710aaed",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:3941"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.rees_isBlowup",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0c2d051947a1c688de5735e2404fcfe0fa04ae6b530295e40812d66af798ccca",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing:264"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.restrictPowerSection_factor",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPowerRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1959aa03e687810fe1ce5939b523112ea15c135f1357fb4b2769d334ae990fed",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPowerRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPowerRestriction:3979"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.restrictScalar",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d8631d835724dc08e0b7a6d36c62fd1b4d073f67fba450640dacd3e57a17e276",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler:388"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.restrictScalar_appIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1fb4f5c76f750d4562da9ff94d81b069097ff62baadbb9aa78528750083bd788",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:10454"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.restrictScalar_naturality",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "674e5f47d894fb3dfbd9103bf4e50044729cdd3a050a372adbd5596d118d0c97",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler:499"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.restrictedOpenSections",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "59e711e11a5b22fa0a24d20d3bca5db168d7fcde2f68e920185fc9adf7e3b93b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:11047"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.restrictedPullbackFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectivePullbackFrames",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b2ad04171d8b40ec644891360bfacaadd5893a04a9b14730f98d5a333303a49d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectivePullbackFrames",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectivePullbackFrames:4328"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.restrictedPullbackFrame_coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectivePullbackFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6bdef6c0062a493baee640f8a5922ca1e082380472d290f4e5b86911dce8cea5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectivePullbackFrames",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectivePullbackFrames:4676"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.schemeHasExt",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6a389f26a6ae3c63aea0a38519bac54a12261997a5f071beb9d6671238685f12",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler:3474"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.sectionImageIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f8263a6677b4593c63b1f77dd541c87bf514d2280fadbab5305c21e35dff2da9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:329"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.sectionOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "221226c2452294698d178816b11a34d9a05afbe1198596ae9918ec01996eb227",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:1070"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.sectionOpen_le_powerSection",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPowerRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "702c930bbfebdf29060d845c096306af43d9f5106318791a6ffc8de7425e53a6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPowerRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPowerRestriction:3112"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.sectionOpen_pullbackPowerSection",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "432fca446780031ae030102e749655acc288a906f243aacd7a66faffa82b2a83",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleRestriction:1827"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.section_eq_zero_of_local_restrictions",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionDivision",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "96b0cfc16c6a766734bf5211e76ada1d3cf6c7a93c1bac6d1974af2287d7df1a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionDivision",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionDivision:1183"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.section_eq_zero_of_top_value",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionDivision",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "48388eeaf1501859fcca5c5b4939954d8822aea37547b3190f0d79780d334a5b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionDivision",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionDivision:761"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.section_value_naturality",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionDivision",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8e38deb5d6ecbce7cbad0f77eba765212b1b95cc1c73039411e457774e91c85a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionDivision",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionDivision:293"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.sheafComplexLinear",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fc7eb98fb9ada35753c4f9ea4ba29177652440a8cfd0a5230e75e36cefeffc9e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact:6884"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.sheafHomModule",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0cf16f544c2dda4098064f86c536cd249df88b26e73fcf9b339f2241c2514f4a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler:2050"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.sheafHomSMul",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d5cf8efc8818f5228cfa86f9611577297ec0195e8bbbea80e57847aa5d0850cc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler:776"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.sheafLinear",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4abbb4bace4e237630700ccab3605c106197caa183f12db735c9c6304c347320",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler:3046"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.sheafificationTensorLeft",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "78c52fd6adb54d779aaaf3fcf5e24f8eca6c5d0e0e5f25c65c62d039753f9ed6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws:7536"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.sheafificationTensorLeftLinePair",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ModuleLinePowerLaws",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f693d9fe8774f5d64069de89fa4d692f2f6e15b57a526afea1104e5b447e589e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ModuleLinePowerLaws",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ModuleLinePowerLaws:5175"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.sheafificationTensorRight",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "22a04107f548dda9e1965a4099b339586044e02f1bb5ba19b0dba7de1b8cc67a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws:6565"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.sheafification_tensor_left_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "46e3e42d8d026a174d493aa3351236a74421de09b7b2bfbf9455665c9c49f520",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws:5289"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.sheafification_tensor_left_line_unit_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ModuleLinePowerLaws",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "57314d7e71fe89d5fd845aa02e8bcacbc364f0e77be4c183635d0e4d7fe11049",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ModuleLinePowerLaws",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ModuleLinePowerLaws:2475"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.sheafification_tensor_right_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b61057edea13c4de40d116f179ea1aa90dcc0ff75016fe95b93a95814298e9a8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws:2124"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.sheafification_unit_isIso_of_iso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SheafificationUnitIso",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ea54fcd18839ee6d2af437eb69c6085ca78414f2bb2848e46052dd16239a2b12",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SheafificationUnitIso",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SheafificationUnitIso:419"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.structuralStalkAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "369389d315ff6f3265558ef8485c555db28521e2b9e8ccabbcdb17e02f4c183d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros:7331"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.structureSheaf",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "69a07d1e79854697dae1044ff14b8737e8f3e02fa902c3f12316211815e79c4d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:931"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.support_comap_ne_top_of_open",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e96395e50a42ea9a69ef65b2774a8b85a16cfd1d3dbf72491088f8d79b359da8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:7431"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.tensorFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "90b17f65c70d5a6977c19a2b7e95ce7bb9331b410118021aa2ff400067a9a29f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen:450"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.tensorInclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TensorIdealInclusion",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "57f11ea7ca5f617c343cb139fc05961ed0dfcbe5843878c34d67da4b6c67ac5e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TensorIdealInclusion",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TensorIdealInclusion:952"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.tensorInclusion_mono",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TensorIdealInclusion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8915012b7b471f3c4f7dd79a101071f121bbd8cba91090b2d0a1cc5d7814e971",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TensorIdealInclusion",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TensorIdealInclusion:4932"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.tensorUnitTwist",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TensorIdealInclusion",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "61f32564f0da58af068e6fbee75fccd495d7502b12d49db2dd1a3cb6a2486171",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TensorIdealInclusion",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TensorIdealInclusion:410"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.tensor_inclusion_framed",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TensorIdealInclusion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f278cd24d136fc71b90b9625b5eda3af2c8c8dbe8fd6dfed65daba68e634f475",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TensorIdealInclusion",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TensorIdealInclusion:2219"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.tensor_inclusion_ideal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TensorIdealInclusion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "14c30d2baf6703abd5b861dac26235b0c560821054253174b794a150a6e62557",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TensorIdealInclusion",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TensorIdealInclusion:5959"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.tensor_unit_end",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameTensorPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5643d470c8902a1e1717f2a8df93e6b249ec706de68250aea161bb23b5688cde",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameTensorPowers",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameTensorPowers:308"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.trivialModule_restriction_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.IntegralLineSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "db301cdef594158a5c73920a56fcbd0f2bdc263cf9d29e6ff026a83e7a8a7186",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.IntegralLineSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.IntegralLineSections:271"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.twoAffineCohomologyOne",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c9a06f5c2aaa6ec034a223e8bd853be3ab8ad5ac4bb13f742aab0a72ece33d80",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech:7381"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.twoAffineUnionExtOne",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7c947fc42d2eeba59b1e747eaf06c8c9d67587743757875088c181e10577a5b8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech:5560"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.twoChartImage",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "912bf596f2f9bd287a78175e5acc004a6fda6c5806e451f56b61067e8a2a62cf",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech:2703"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.twoChartImage_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "119c4207e6e393c2f48fb63b53bc9517e679d6b9f00468ba16c5c755bd51b3ca",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech:2952"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.unitPowerIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d8caee0700b9ac7559a943834f04b42c22c63c449213361115296f444bff10c2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:12933"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.closedInclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "80a037704bbaf18f979212bd81d9509520e0cb90951e9065d5cb4c9e5c05fab6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:3071"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.closedInclusion_mono",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "66d9549027f7544de84e8daa91c81a71336ada548796f72b42be3111e6879cf1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:541"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.closedInclusion_structureMap_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "53a9a7646620022a8dae7f63fdc83cbb60f8e80a30e5a45c88469e93055b4f05",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:679"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.closedMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "897de68c12d70c916ff3b37ca9c76d1a5d9c06a063c912c251948aadb29008c1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:1348"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.closedMap_inclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f68fb0a70e0f432622e6d17c5e9c64aeb84875e78eb4a90dc60c878e8ee26228",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:1553"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.closedMap_inclusion_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d7437d0683fbb6f429eca81f3edf1f5eaba10a58319a5a9bc543d2bd640cc546",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:1553"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.closedMap_mono",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5f447d25bd5304b0ad594f59a16b1c8be2ca2685121061af3117d01ec4affe05",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:1732"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.closedModule",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ed783f691834d38ef11e1e38eb819065a693638a7faa676e01ac58dbea0012e2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:2987"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.closedModuleRestrictIso",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6d7b9792f1d09df8ca2ab0f82febbebcc2de52ea636d6120e5038a3e7f2e3b02",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction:2777"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.closedModuleRestrictIso_naturality",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e17935ca67423ac68b6b8792f36ebbb97d139036442673615f2174d5687318e4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction:2963"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.closedModule_isFinitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7ed9c700a02f5b5dbcb6e1590f87409a749030726471ff26ede962507b234721",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:3666"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.closedQuotientCongr",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1cb1ad7c7a838e6c4573896a5cd479cd49b604eca521b071479d695b7dfd83e8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction:750"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.closedQuotientRestrictIso",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "45cc9782c604ad0dae61097d9de00932d7e09efcf916dcd7b74acdbfc4ccd321",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction:308"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_027.jsonl"
