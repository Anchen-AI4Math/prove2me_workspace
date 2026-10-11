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
      sourceName := "OAI.PiExponent.CurveNormalizationDegree.finite_support_positive_cohomology",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationEuler",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "543d383c3c8060d42c2e7ed5c6500d31a79037eb5c5ac3f17bf4351c1f0776fa",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationEuler",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationEuler:1056"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationDegree.finite_support_tensor_euler",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a4d344dcea105bf4181272d1d5e03822e659daca3e271a17edddacdb0720d9d2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDegree:5044"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationDegree.finite_supported_quotient",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationEuler",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "adfecdf68e73eebae71ee32712d34e4590d1836013d616a1b4498e6713f0a4ed",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationEuler",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationEuler:2167"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationDegree.generic_extension_tensor_euler",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationEuler",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cf83c81555e9be034717cae178862453b80d67af52fd3042ca1aec3f2552865d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationEuler",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationEuler:3744"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationDegree.lowCohomologyFinite_of_iso",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationEuler",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d6fa769bd03ff7468571cb709c768392db1dbf4d70865317c6636ad7c1352eff",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationEuler",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationEuler:621"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationDegree.lowCohomologyFinite_pushforward",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationInvariance",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7e8e0d81ea94e9567820a9c982641201a7d958b35799ca859d575f9368089e3b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationInvariance",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationInvariance:568"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationDegree.parameterCurve_pullback_euler_degree",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProjective",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4fd241181ac6d9e27468b0b5245d4d25a80d0f57e1c656e7911d80ac4d95a387",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProjective",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProjective:908"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationDegree.parameterCurve_pullback_euler_degree_of_ample",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProjective",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c3d42e8c9b66b6c4cc665bf2732cd4c90fe741954ea312bce0f9d5a7704df4a8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProjective",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProjective:3597"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationDegree.pullback_euler_degree_of_open_iso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationInvariance",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "413c4d78c9211db5bfa1616ef0b05a3d71708e1ba06538d651d212b7789e63fe",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationInvariance",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationInvariance:1516"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationDegree.pushforwardPullbackIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationUnit",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "52b028cdf95fe54e75c20c4232f0a2655ebd2c1668167b631dd3ac068120c1e9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationUnit",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationUnit:2631"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationDegree.stalk_subsingleton_of_localIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f1209aaccf91fcd620cbe5356153b73fe1e96e74237ef42316170dd7e6d1b9ea",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDegree:2933"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationDegree.tensor_stalk_subsingleton",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2ed68a35527b4e518685ed21233d1cf73c722f811504712956a87d593b28add4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDegree:3615"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationDegree.unitMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationUnit",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a8ccc219f663e9a094e8e0bef8ee9d3fbdb76555abd8a9a555f357f9136723ba",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationUnit",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationUnit:415"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationDegree.unitMap_isoOpen_ne_bot",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationUnit",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "95aa5cb0003492450346a8e87496855ff324f2d4964337c8b226716bad8c2470",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationUnit",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationUnit:2299"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationDegree.unitMap_mono",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationUnit",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5b3326f41eec248ce3a6cb887a10c9fb5d19f894cf64be7ffde4aea78b1f1b1f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationUnit",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationUnit:592"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationDegree.unitMap_restrict_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationUnit",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2f1194fc51bfaeb0b8676442580955f32d01e82143351fc0aedae2d3c88de45c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationUnit",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationUnit:1514"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.affineChartFunctionFieldMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveChartFunctionField",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7884f02b46f10f15747c98a30edfff34f605f52ca2607069f3f1cf7f53476ef0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveChartFunctionField",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveChartFunctionField:319"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.affineChartFunctionFieldMap_eq_of_overlap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveChartFunctionField",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1fd4eb51caf86c56f5945651c83488112e415c61ec31f279e20e38208329b960",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveChartFunctionField",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveChartFunctionField:1708"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.affineFunctionFieldEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AffineFunctionFieldCompatibility",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "72c373ff5e1245f806d49ff2259e63a9646b2d2bd95ba9794bd52d1440ac6033",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AffineFunctionFieldCompatibility",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AffineFunctionFieldCompatibility:1350"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.affineFunctionFieldEquiv_fromSpecStalk",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveModelGenericPoint",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9cd41ba727806471d8c2d39874e83c444bf9ec1aaf35aa538ba10b6d03acba4f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveModelGenericPoint",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveModelGenericPoint:1080"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.affineFunctionFieldEquiv_naturality",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AffineFunctionFieldCompatibility",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "88444f72c5068164b923239b31b6804c0a0ec6451a00cff2e1c14afb03abce66",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AffineFunctionFieldCompatibility",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AffineFunctionFieldCompatibility:4336"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.affineFunctionFieldEquiv_toStalk",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AffineFunctionFieldCompatibility",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7eff27c46c5ecd1b19e758f732518ede6e8f8b6d1a70af6b0f1816664ac15be7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AffineFunctionFieldCompatibility",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AffineFunctionFieldCompatibility:1755"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.functionFieldRestriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveFunctionFieldCompatibility",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1b9df9b6eb0e44b0f0955e17e92f577cffde3b35b0032af11ad04e708584351c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveFunctionFieldCompatibility",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveFunctionFieldCompatibility:214"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.functionFieldRestriction_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveFunctionFieldCompatibility",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c32cfebfbf4ab1c0f30f27655aa87e678d112271fdb3922c7475453aae7c82e3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveFunctionFieldCompatibility",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveFunctionFieldCompatibility:1615"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.functionFieldRestriction_fromSpecStalk",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveModelGenericPoint",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1b1f6d2f7a130aff813b83e7a9a3d5f5d33f1eb2e10013729069fb8bc47f6f1f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveModelGenericPoint",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveModelGenericPoint:608"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.functionFieldRestriction_toStalk",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveFunctionFieldCompatibility",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fc890b962e3e9bdfc9f7a5ceffcfcc1281c7d88cd8afb4e91eee07dc5a9fbd44",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveFunctionFieldCompatibility",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveFunctionFieldCompatibility:2470"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.infinityChartInclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "38c646729a5395b904d5d0e9853c7b447908fd5b9b7b7986944e6c6cecbd4dcb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel:8856"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.infinityChartInclusion_isOpenImmersion",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4a895c10c325dfded7e2db1b3942a1851fee288a9e3f920e737f16423db5d091",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel:9285"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.infinityChartProjection_isPullback",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bafe9c177019b2649cebc33a839be28f4edd3f0b050800531780740ab17d4d90",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper:6429"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.infinityChartStalkIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "54637aa16eafed12af11bfddf21b3cc2beafb5f315b8f88530e7085aa880aca9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel:10869"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.infinityChart_mem_zero_iff",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationOverlap",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3f9057113cf5071731fb8f02956d5bdcd0b082e63001aadd5b01d4fb203172ac",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationOverlap",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationOverlap:2808"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.infinityChart_projection",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b5a36e4a1fa8c5aaefbe3355e77e5633dff000241661c208aa72682974c2568f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper:3051"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.infinityChart_projection_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "32efcd1cd5870d2866bcc47436f072319023b2e2d4663f5aff677f709acc2a3b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper:3051"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.infinityChart_stalkDVR",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationLocalRing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "87ea14f4b68fcc3f2926da10af41020ea6122bf0cc7af65c01bd290fa6d08135",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationLocalRing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationLocalRing:2104"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.infinityOverlap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "138df8a77bc8ba20f9624f0e77de03767c4a1979d34005999166a2f355ac4bdc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel:7644"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.infinityOverlap_isOpenImmersion",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "145f6bc6788534f5a3b00678b95a5e3e40490a5dee193953f3dc67ded54c6b2a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel:7944"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.infinityOverlap_projection",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1db61f33506a91b6b8e54a6cba9048edc75d42e2b8494722a7f156f09ba9129c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper:1330"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.infinityOverlap_projection_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "db67fa8c819a5d4b4956e56a38827712af9aba921968cd3c94e6ed5f709894eb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper:1330"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.infinityOverlap_range",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationOverlap",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e58db5228a3db1beee313620df38b1bfaa79c9b75beb3f0b297b45e6268e4d44",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationOverlap",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationOverlap:1536"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.instHasExtModulesParameterCurve",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "45961fc2cb346b8cda6a39db0a3441c505c7f599231380ebd592a84ee9c0ea5e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationCohomology:689"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.integralClosureTowerHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7dab972b27d1f951235e01afbd84faf0cd00c27b9f727940a2109005b94a41e5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel:523"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.integralClosureTower_SpecMap_isOpenImmersion",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4f67b04846a5f759ed3fa644e3aa2793f52636eae00027f405331d8a30c7ec1e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel:1750"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.integralClosureTower_isLocalizationAway",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0f22cf931c2c7eb641f6d29141b3db07922c1502cd09ebae7bb33f712c8d61ee",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel:866"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.isFractionRing_of_intermediate_domain",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AffineFunctionFieldCompatibility",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6a2439fd596b9d2dbacbb2a5a495b1c1dbfe54249f4d635af87793328613df53",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AffineFunctionFieldCompatibility",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AffineFunctionFieldCompatibility:382"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.isIntegralElem_comp_equiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "85794b6341db8afbd17e7ce2503b97e6cec6e073c2839372dd6791ad07695edc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel:6012"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterChartConstantMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveModelGenericPoint",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e507434fca771231e3c25101a18848cfa4ad55bd0a040cb8673c5ff4ca2716be",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveModelGenericPoint",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveModelGenericPoint:2880"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterChartFractionRing",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveModelFieldEmbedding",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1aad9004102561e9411a0515f5bd3f45f6b4fe948109627d4cac6c66d95b4034",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveModelFieldEmbedding",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveModelFieldEmbedding:520"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterChartOverlapHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7de6c94493d1ec446c6821ccaa12ba60231b91710ef443d7691d2b0e36ace842",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel:4213"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterChartOverlap_isOpenImmersion",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c07bd00a180fe67cde38894ab18025cc6b9f23fe932b8f8d17c5a50e430253b8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel:4556"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterChartProjection",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationLocalRing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5b69e879043c7803f27eb9f25d129756d53764f7ee203d411a16346affaaa440",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationLocalRing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationLocalRing:423"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterChartProjection_isFinite",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationLocalRing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a581fc6e6cae94a17d23c761fc26489a4bded422774d57874b77ee56a43a6ed0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationLocalRing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationLocalRing:628"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterChart_localDVR",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationLocalRing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cac9bab481f8ca38696068e776da880d76e71c5f272e6f051909b3e4e4d82ea5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationLocalRing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationLocalRing:1108"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterChart_noetherian",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1e4b4202899894dcea17beaa5b3fd0d8867bce197aaf35b40c8d60294a9ff484",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDimension",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDimension:1059"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterCurve",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d3f0c7affa1e40fec8fe39b4e3f25a879ad69dfb35d90d3b6099d0d1b1eae2e3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel:8610"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterCurveAffineOpens",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cee07a5f7d6eac74d8b1937fcc64af49c60706f27d67f53c1f067690ab5e56f8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationCohomology:1093"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterCurveAffineOpens_affine",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d7d3c547e9f7f3a5802f27930ac7db07d5c2b402727d0f36b230bd1ed3bbcd96",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationCohomology:1274"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterCurveAffineOpens_cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1c66a450f103f3beb52d84ebbf781c43362674bf68d060549cded331ed2cb8c1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationCohomology:1549"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterCurveFunctionFieldEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1fc9d39fac2b556694373df43f23956bdaac9a014ec8910b8447dbb372d6ea72",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel:14444"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterCurveFunctionFieldEquiv_eq_infinity",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveModelFieldEmbedding",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "797b64a674455ba199ddf820bc2598f0f9a443178235cd5aa5bc20d2bc6e90ff",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveModelFieldEmbedding",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveModelFieldEmbedding:2110"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterCurveFunctionFieldIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5670b7e012b8b2997e1fdb04144a9e6eefc228fea8f44f4de1739e570d52ec1e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel:13807"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterCurveGenericPoint",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveModelGenericPoint",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "472cbef7d5dd85bd6706221c6f36fc14d12aaf4d5819810dde17e10beaeef608",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveModelGenericPoint",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveModelGenericPoint:3815"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterCurveGenericPoint_eq_infinityChart",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveModelInfinityGenericPoint",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2abfcca2631cb50d321fdaeaaf6ea69a10cdab275511935954d6791c782c837d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveModelInfinityGenericPoint",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveModelInfinityGenericPoint:474"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterCurveGenericPoint_eq_zeroChart",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveModelGenericPoint",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ddb2e811b8895a24cbfdaf5db49cb74d49740b0c8317534396c1055930740a5c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveModelGenericPoint",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveModelGenericPoint:4055"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterCurveOpenCover",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDimension",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9477ac3922678939c98be5cbd10f03221df6d976f99326f07b23a70d1720b137",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDimension",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDimension:436"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterCurvePolarization",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CurveNormalizationPolarization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "36009dbe048ed2404761c8602f7451218bb4b3160be1652dc83a60a077accf71",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CurveNormalizationPolarization",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CurveNormalizationPolarization:737"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterCurvePolarization_ample",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CurveNormalizationPolarization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ec1d0210eeccad22e7c3c4f0f32db1c1bae211d3c18306d15026024c718d3f4d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CurveNormalizationPolarization",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CurveNormalizationPolarization:903"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterCurveProjection",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b44ec67b4baaecb940ab427d98b4d40c7ee6a179f7b92a5db3a3328a7d3e90dc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper:2395"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterCurveProjection_isFinite",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "65bb278786badeb688f99479e9294e7f48c7f31ea3bcff11ff946bcaaee3c3e1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper:6801"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterCurveProjection_preimage_infinity",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cd786f58d5d3dbfc0f3d237699a393633d960d01c765b5060cbd515bc10b3d34",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper:4757"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterCurveProjection_preimage_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3d945668c2eea054bac3fdd316a986f374e96c3e218a3df320049dec62f186bb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper:3318"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterCurveStructureMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7d3f3f352e5e64d5fea528b7be5a8dfd1e828e654d531893ed3babbc43dd8f26",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper:7966"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterCurveStructureMap_isProper",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f6520e6cd0e2fa094fb93571df4bdaaa29b1229a9fce9c6948ecf6cd20c49703",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper:8109"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterCurve_compactSpace",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0fb2f4a2f0b58027d9a9f876055c007fff3926151925c095a25568009e18fa2f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel:11421"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterCurve_dimension_le_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "528f7166d515b17d1a02f2a3dbaba196597aae0ab23b8e7e6dc3a6dc983063c6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDimension",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDimension:2043"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterCurve_exists_nongeneric",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "69b28c4333f11f64d9e46bd711e5d83829e37a4528b2620b98461bdcbc1f57c9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDimension",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDimension:4141"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterCurve_ext_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "704549a82c17ddcd1ac8b77cbbdb7aa1daf77edc5c89a92575862f19e7d43db7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationCohomology:2107"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterCurve_finiteLineCohomology",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CurveNormalizationPolarization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "68cf303b94c03c455a9af4fa8adbc103c68eed95aff8f5b2c383e7b45d07ed2a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CurveNormalizationPolarization",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CurveNormalizationPolarization:1264"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterCurve_genericPoint",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f6aafe3e4f06c4399dfed6fb5ef2dc2fc4d859761e5f5798eaed7ff8b0ca753a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel:11937"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterCurve_irreducibleSpace",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8b1ac9e15b0b613acdbee24c2b256a16aafe0a658f407ea7e099af84af05920a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel:12919"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterCurve_isClosed_iff_ne_generic",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0ab74d37e4b93e915bf42055b36416cb983f1efe7651d6fa4cbeef49daa9c698",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDimension",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDimension:5228"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterCurve_isClosed_of_ne_generic",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2b3098b6c3bcbfff76a3de40174c89bca986220a2b3ab775af5b1c0d38ab2633",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDimension",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDimension:3065"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterCurve_isIntegral",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a6644408910d76094dd090e23b00bf3e12aad50bc9e98ed7767985d19226eb8e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel:13682"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterCurve_isReduced",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c261052e53c94136e4d18c70831f7a4b1be35c18b02653bf0c52b04d72f83d08",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel:13088"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterCurve_isSeparated",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "496b0e5739145fe46cd83fa06feb13a2b225af8140e6e88ce95897618986d01f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationCohomology:898"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterCurve_lineBundle_ext_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "41702e90b80c4faa32f4431c94c883ed7b7de483f7d7c2b7255a4821adbc8ee6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationCohomology:2547"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterCurve_lineCohomologyTwoZero",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CurveNormalizationPolarization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "da279273be20d8e54dca03ee4663d966bffd9cd8d284301d2047dfd41a22f618",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CurveNormalizationPolarization",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CurveNormalizationPolarization:1707"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterCurve_noetherian",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "53e848bd2428632d60e11586f95be89ef9a29b5416915715c468edb07650cabb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDimension",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDimension:1383"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterCurve_not_isAffine",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationNonaffine",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f57e78abcd8e94c7aaede20f6c9a724554af8e01b07efd5ec30b34fbcb25fe8c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationNonaffine",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationNonaffine:556"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterCurve_overlap_compatibility",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b224cbfc2ffa0c592ceebeeccf500013f0c69f1e0a956205df06f4a495d20e88",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel:9530"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterCurve_stalkDVR",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationLocalRing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4b1f4d31f946210e2810e45cd69bfc6606f8eb47af2f94f49e74ec9cb1485e07",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationLocalRing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationLocalRing:2779"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterCurve_tensor_euler_add",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CurveNormalizationPolarization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b47ae2e1c8f1098f523a18e1367bfd539dba652c93aa3804f545465ff6b656a2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CurveNormalizationPolarization",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CurveNormalizationPolarization:1949"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterCurve_twoChartCover",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "57599a06a4e0cfb6445b6a249fa2bf31f7f3960ee4992bac07508f53647e9395",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel:9723"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterLaurentAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a26886081b11fa5138c92c8291b815f218e4a0060586cebcfab834de60f0bf85",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel:2686"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterLaurentChart",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "584aa9149c6d4ddb171b1b9f184121e377dc3f2db478e6bee8ef528e37e1afd2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel:4000"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterLaurentChartFractionRing",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveModelFieldEmbedding",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5ce11314db935e38669e609640d421063bd43427b7faee2df425d54f03288ebb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveModelFieldEmbedding",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveModelFieldEmbedding:1603"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterLaurentMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a4f697c6302919dfa4d2b5240323474d3238bbb5b7f27ac5d7b5be8609228e04",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel:2468"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterLaurentMap_T",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fb7f4cdfb95c6435a424440149e2b66f325054a81fb8c1d5d01d0d94dc2152b6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel:2884"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterLaurentMap_T_inv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7d6d46ea16ec35dc4128d3330d5f286fbe76846fdb657b6db993c7493a1dff14",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel:3138"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterLaurentMap_invert",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5c9ad598b960de6e86abdc4f9e3cb1423b31d17cbefd5ef65295d3d68fc2c22d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel:5396"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterLaurent_scalarTower",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e8ea55146d7489b9e9f31dbd428cd50305eea5f8df7460e81d25da00ba7568bd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel:3404"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.parameterOverlapProjection",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e259efd4bb54b86f1779ddf7205ac451743add25cf3593bc487dccf691a4ed1f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper:440"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.reciprocalLaurentChartEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "63c90ffe303ccfcd60cd95fa3093d8fa621c09df5a1c5d497eb02e823f7efcb0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel:6489"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.zeroChartInclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3755a82e3bd8cd697c8738793536aab090d8f2c6f7ba2057b2db8a613daa1108",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel:8704"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.zeroChartInclusion_isOpenImmersion",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "41a4d658bbbe09314d1ae424247732ca28d778df9a9468353dab6bf65d62e9ca",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel:9049"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.zeroChartProjection_isPullback",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "85ada63503a318eb43dbc9e895c4dfae6b9b0f66cb78f3ab3083154817cf6db1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper:6111"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.zeroChartStalkIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a9801d1644439016bfff58646ba40a413f4cfa6288f4d8f74ea6c173ac0d488d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel:10406"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.zeroChart_mem_infinity_iff",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationOverlap",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5eec156977dbfeb0d70f40fb9b09d0f2c7b44110f70a0c568c4e53af6b09d410",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationOverlap",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationOverlap:3958"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.zeroChart_projection",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f221e5832b63b811a369f35cb610642d50fadffba90c3a644c6f37cdf1196505",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper:2832"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.zeroChart_projection_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7c65c2f54d05f205436a51ba9ec986c18834a4c77ea1dd1411cf897b019278b9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper:2832"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.zeroChart_stalkDVR",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationLocalRing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3ea4bab65e9319365120b00a90bae21257163f43dc3d478360da3bbe78affc5c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationLocalRing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationLocalRing:1639"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.zeroOverlap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "56630493e6942dd2241c39820e6e5b49befb8fff2994535047673161d60ddf23",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel:7353"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.zeroOverlap_isOpenImmersion",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "642ba2d7ad9d677019ea9854bd8c79d1683f9e7060485d95ef4df0cc9db5cd4d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel:7518"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.zeroOverlap_projection",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ba57d2c4ad97dcc088e2539b658197084a50932c9ee7ba6957c4805123e06f02",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper:697"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.zeroOverlap_projection_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "780304f16a8c56f785adc7e8880cc6ae5a4ba4463288861c554a4d657d958a11",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper:697"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.zeroOverlap_range",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationOverlap",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1eac627f0f97452de7c13105bf3310370cfeb796d334e0ba8bc43975ea31291f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationOverlap",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationOverlap:372"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationMorphism.structureFieldAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationMorphism",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c9a08a52f5cfb81dcaf7469b6b820fcdd933cb9bc53b56951816d332a75518c0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationMorphism",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationMorphism:513"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizedDegreeTransfer.curveDegree_eq_normalized",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizedDegreeTransfer",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "42331ac72f92930fa83e84a53bc6b30cf2cfb44d088c538ae349420cc73cb1f7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizedDegreeTransfer",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizedDegreeTransfer:433"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizedDegreeTransfer.curveDegree_pullback_eq_normalized",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizedDegreeTransfer",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ff7cc6e40a6638e57be00728355988aba881d88d81f9b923b37c5b61fa489b20",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizedDegreeTransfer",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizedDegreeTransfer:1708"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizedDegreeTransfer.weighted_curveDegree",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizedDegreeTransfer",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a71d83d019190ebad47b6ff6ac174dd73abcd6981123b3f8d2b5e8fad5671e7e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizedDegreeTransfer",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizedDegreeTransfer:2877"
    },
    {
      sourceName := "OAI.PiExponent.CurveParameterFinite.finiteDimensional_adjoin_singleton",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveParameterFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "321aeaa8a387818417eaa7adec03df9d26a76e46a20113af88ddd096b0966394",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveParameterFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveParameterFinite:192"
    },
    {
      sourceName := "OAI.PiExponent.CurveParameterFinite.finite_over_every_parameter",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveParameterFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1a780150964e4d3cf36a6ac7fa7973d556f2d311a4f8c41939428425dacb3e1d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveParameterFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveParameterFinite:1136"
    },
    {
      sourceName := "OAI.PiExponent.CurvePlaceCenter.centerMorphism",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "471f7c97f3e930a489e3592c648a439eb2d49ee171a02e317931f94588f77aec",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter:1491"
    },
    {
      sourceName := "OAI.PiExponent.CurvePlaceCenter.centerMorphism_closedPoint",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aa3fe45a4241492db65ba60e3880b635ef29cf5425099ec0666c82796649512a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter:2129"
    },
    {
      sourceName := "OAI.PiExponent.CurvePlaceCenter.centerMorphism_comp_eq_of_generic",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0fffe3f7a21d4245eb01a5b015e864f794e3923c13aef2d2be3ebcdece39187d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter:4339"
    },
    {
      sourceName := "OAI.PiExponent.CurvePlaceCenter.centerMorphism_generic",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "30a28b5b15c09170f5fe174163e5867a7e065757ab138250a794320f0e206cf2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter:3134"
    },
    {
      sourceName := "OAI.PiExponent.CurvePlaceCenter.centerMorphism_generic_of_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "26eae6d27ceb7644539422fba4377b6a7d0c9e8c9448649699e4a26dc73203b3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter:2571"
    },
    {
      sourceName := "OAI.PiExponent.CurvePlaceCenter.centerMorphism_stalkClosedPointTo_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenterStalk",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7ea3307ddabf31de07e6e585e7d2cc6282058ab8fcd323556138a49dc0c06323",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenterStalk",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenterStalk:1198"
    },
    {
      sourceName := "OAI.PiExponent.CurvePlaceCenter.centerMorphism_stalkMap_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenterStalk",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0719548838b7e6131949cb733e040a7eb077a35f73d35e5c32211bdb2b931a3b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenterStalk",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenterStalk:631"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_005.jsonl"
