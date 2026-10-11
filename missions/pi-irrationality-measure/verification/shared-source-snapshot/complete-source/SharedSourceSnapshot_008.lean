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
      sourceName := "OAI.PiExponent.CurveNormalizationModel.zeroChart_structureMap_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveModelGenericPoint",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ea01931d8b10361c149f5ed6ff16affc8e86bbbc9ffcf9d5feaea69ce2958293",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveModelGenericPoint:3392",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveModelGenericPoint:3392"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.zeroOverlap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "56630493e6942dd2241c39820e6e5b49befb8fff2994535047673161d60ddf23",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel:7353",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel:7353"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.zeroOverlap_isOpenImmersion",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "642ba2d7ad9d677019ea9854bd8c79d1683f9e7060485d95ef4df0cc9db5cd4d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel:7518",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel:7518"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.zeroOverlap_projection",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ba57d2c4ad97dcc088e2539b658197084a50932c9ee7ba6957c4805123e06f02",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper:697",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper:697"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.zeroOverlap_projection_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "780304f16a8c56f785adc7e8880cc6ae5a4ba4463288861c554a4d657d958a11",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper:697",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper:697"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationModel.zeroOverlap_range",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationOverlap",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1eac627f0f97452de7c13105bf3310370cfeb796d334e0ba8bc43975ea31291f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationOverlap:372",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationOverlap:372"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationMorphism.exists_finite_model_morphism",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationMorphism",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8328168b33b5668c75c81ce7a51d0c22d8b800a8dd82af73735acec8b35f469d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationMorphism:4546",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationMorphism:4546"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationMorphism.exists_intrinsic_normalization_morphism",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationMorphism",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "092804e68418eb0246b47f2daa2731c69d0030b295a5244500192d4bbe5c9664",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationMorphism:5830",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationMorphism:5830"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationMorphism.exists_model_morphism",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationMorphism",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ca1c633e611f674f53920d85fc329535e54f8897810cd8e5b853526a970c14b1",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationMorphism:2674",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationMorphism:2674"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationMorphism.genericPoint_over_structure",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationMorphism",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "91d8b5777c70956d409621cacd180aeab40ef84c5534895cdb41af5b7185ac9c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationMorphism:770",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationMorphism:770"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationMorphism.isDominant_of_generic_identity",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationMorphism",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5d58246da724c295e640188ba19c803ea0cf75b8ab89b47d69ffad914d5c57b6",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationMorphism:1707",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationMorphism:1707"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationMorphism.nontrivial_of_dimension_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationMorphism",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b99c0b65ca94c56dc84050a32ff04a4378360313470a9f14050f0c74367272db",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationMorphism:2357",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationMorphism:2357"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationMorphism.structureFieldAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationMorphism",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c9a08a52f5cfb81dcaf7469b6b820fcdd933cb9bc53b56951816d332a75518c0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationMorphism:513",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationMorphism:513"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizedDegreeTransfer.curveDegree_eq_normalized",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizedDegreeTransfer",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "42331ac72f92930fa83e84a53bc6b30cf2cfb44d088c538ae349420cc73cb1f7",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizedDegreeTransfer:433",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizedDegreeTransfer:433"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizedDegreeTransfer.curveDegree_pullback_eq_normalized",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizedDegreeTransfer",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ff7cc6e40a6638e57be00728355988aba881d88d81f9b923b37c5b61fa489b20",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizedDegreeTransfer:1708",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizedDegreeTransfer:1708"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizedDegreeTransfer.weighted_curveDegree",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizedDegreeTransfer",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a71d83d019190ebad47b6ff6ac174dd73abcd6981123b3f8d2b5e8fad5671e7e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizedDegreeTransfer:2877",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizedDegreeTransfer:2877"
    },
    {
      sourceName := "OAI.PiExponent.CurveParameterFinite.finiteDimensional_adjoin_singleton",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveParameterFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "321aeaa8a387818417eaa7adec03df9d26a76e46a20113af88ddd096b0966394",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveParameterFinite:192",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveParameterFinite:192"
    },
    {
      sourceName := "OAI.PiExponent.CurveParameterFinite.finite_over_every_parameter",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveParameterFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1a780150964e4d3cf36a6ac7fa7973d556f2d311a4f8c41939428425dacb3e1d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveParameterFinite:1136",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveParameterFinite:1136"
    },
    {
      sourceName := "OAI.PiExponent.CurvePlaceCenter.centerMorphism",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "471f7c97f3e930a489e3592c648a439eb2d49ee171a02e317931f94588f77aec",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter:1491",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter:1491"
    },
    {
      sourceName := "OAI.PiExponent.CurvePlaceCenter.centerMorphism_closedPoint",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aa3fe45a4241492db65ba60e3880b635ef29cf5425099ec0666c82796649512a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter:2129",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter:2129"
    },
    {
      sourceName := "OAI.PiExponent.CurvePlaceCenter.centerMorphism_comp_eq_of_generic",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0fffe3f7a21d4245eb01a5b015e864f794e3923c13aef2d2be3ebcdece39187d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter:4339",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter:4339"
    },
    {
      sourceName := "OAI.PiExponent.CurvePlaceCenter.centerMorphism_generic",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "30a28b5b15c09170f5fe174163e5867a7e065757ab138250a794320f0e206cf2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter:3134",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter:3134"
    },
    {
      sourceName := "OAI.PiExponent.CurvePlaceCenter.centerMorphism_generic_of_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "26eae6d27ceb7644539422fba4377b6a7d0c9e8c9448649699e4a26dc73203b3",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter:2571",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter:2571"
    },
    {
      sourceName := "OAI.PiExponent.CurvePlaceCenter.centerMorphism_stalkClosedPointTo_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenterStalk",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7ea3307ddabf31de07e6e585e7d2cc6282058ab8fcd323556138a49dc0c06323",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenterStalk:1198",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenterStalk:1198"
    },
    {
      sourceName := "OAI.PiExponent.CurvePlaceCenter.centerMorphism_stalkMap_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenterStalk",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0719548838b7e6131949cb733e040a7eb077a35f73d35e5c32211bdb2b931a3b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenterStalk:631",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenterStalk:631"
    },
    {
      sourceName := "OAI.PiExponent.CurvePlaceCenter.fractionSpec_isDominant",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cfe55c9b70fb2b22a23b7f0139da7bd0ca9490dd052134eb0d740f40ea604245",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter:422",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter:422"
    },
    {
      sourceName := "OAI.PiExponent.CurvePlaceCenter.hom_ext_fraction",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9754c7a95627b49bc79541f138e56aa6351cbc761592e30588d760678142dd79",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter:1039",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter:1039"
    },
    {
      sourceName := "OAI.PiExponent.CurvePlaceSectionDivisor.degree_eq_euler_difference",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceSectionDivisor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a9ff9a6026b10ba737794c40ec538e82107103d202b78484dac8f5af6c009d16",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceSectionDivisor:1450",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceSectionDivisor:1450"
    },
    {
      sourceName := "OAI.PiExponent.CurvePlaceSectionDivisor.degree_eq_euler_difference_full",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceSectionDivisor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5c49cb78379e9581e982b8e92a4fe35674cee36d8c3b0c1e223232217deca690",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceSectionDivisor:2828",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceSectionDivisor:2828"
    },
    {
      sourceName := "OAI.PiExponent.CurvePlaceSectionDivisor.divisor",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceSectionDivisor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b7993485cfb309e74a5995e6797816b4b35d66542c2ae1c6469d5061df90cc50",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceSectionDivisor:641",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceSectionDivisor:641"
    },
    {
      sourceName := "OAI.PiExponent.CurvePlaceSectionDivisor.divisor_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceSectionDivisor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6b1517907fef002c11cb671fb6c1b771ee87db4c9c571caf5d5ac05fa289f836",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceSectionDivisor:1022",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceSectionDivisor:1022"
    },
    {
      sourceName := "OAI.PiExponent.CurvePlaceSectionOrder.divisor_eq_local_order",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceSectionOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3e5fa47dfdea36f4ec20dd2e483eb26c674d13fa602124f2a24a07c41ae1f834",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceSectionOrder:736",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceSectionOrder:736"
    },
    {
      sourceName := "OAI.PiExponent.CurvePrimeHeight.height_add_one_eq_of_quotient_dimension",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurvePrimeHeight",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3f5c0b3997dd1e2133cfd3190f3c4bda2b130cc72985b1d690959ef38a4111a5",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurvePrimeHeight:295",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurvePrimeHeight:295"
    },
    {
      sourceName := "OAI.PiExponent.CurvePrimeHeight.kernel_height_add_one_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurvePrimeHeight",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "53f35216d2d7ee037bba1c858421cc9de98e713a844bb47385eb17217065d7ec",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurvePrimeHeight:3770",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurvePrimeHeight:3770"
    },
    {
      sourceName := "OAI.PiExponent.CurvePrimeHeight.kernel_height_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurvePrimeHeight",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b593d8d4b66ff2aec436b658c7aa5e1d35342947e89c1b72322aa18d8f869998",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurvePrimeHeight:4286",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurvePrimeHeight:4286"
    },
    {
      sourceName := "OAI.PiExponent.CurvePrimeHeight.kernel_height_succ_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurvePrimeHeight",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e4716de2b914d8a820184a9885de6c24e4f7173f1dbd5d8c1633d32b61fac25a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurvePrimeHeight:4727",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurvePrimeHeight:4727"
    },
    {
      sourceName := "OAI.PiExponent.CurvePrimeHeight.kernel_height_succ_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurvePrimeHeight",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c4bba5493446fe69a7807c3569a205d310b196f7741df010f05f02e7c709840e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurvePrimeHeight:5145",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurvePrimeHeight:5145"
    },
    {
      sourceName := "OAI.PiExponent.CurvePrimeHeight.quotient_dimension_eq_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurvePrimeHeight",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "79c18657b7eec1fdd097e8a9fab5cc6cdf27f57f9bb8e3a7ece74ada4d334dcd",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurvePrimeHeight:3278",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurvePrimeHeight:3278"
    },
    {
      sourceName := "OAI.PiExponent.CurvePrimeHeight.residue_trdeg_toNat_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurvePrimeHeight",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1f790c0219fdf92f1a1b7f096e1f40465a3660e80a084e04740318baf638faf0",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurvePrimeHeight:1647",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurvePrimeHeight:1647"
    },
    {
      sourceName := "OAI.PiExponent.CurveProductFormula.finite_support_placeOrder",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9bf551c1668f040d70e20f83d65e27a697a74ad855e66215d8d467dfb68bdb9f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula:3125",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula:3125"
    },
    {
      sourceName := "OAI.PiExponent.CurveProductFormula.mem_positivePlaces",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "020ddf9cb63c2a5ceb20b19352a906d1d93961ad18cfc3d4517c4fa0ca326c7a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula:1611",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula:1611"
    },
    {
      sourceName := "OAI.PiExponent.CurveProductFormula.order_ne_zero_iff_positive_or_inverse",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9aa6aaea2b44eacfdb3cff0de4a674fcb43c5f0117a65583d0a62950da4af120",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula:976",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula:976"
    },
    {
      sourceName := "OAI.PiExponent.CurveProductFormula.placeOrder",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5d9d947710bd904306b0982f1f5154f8fdfd9bf1e7270447a65bcb078f953de8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula:384",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula:384"
    },
    {
      sourceName := "OAI.PiExponent.CurveProductFormula.placeOrder_constant_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0d50173a7be590faac2f206be311e0a60f7af506bcee6880b61961be1ff82edf",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula:8180",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula:8180"
    },
    {
      sourceName := "OAI.PiExponent.CurveProductFormula.placeOrder_inv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b1f9e5772a7a25dfa538b98f51f3f6d8c09976d2fbb0046e56d84b529b348685",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula:527",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula:527"
    },
    {
      sourceName := "OAI.PiExponent.CurveProductFormula.positivePlaces",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "04ba19c7f1ac58557c69aeb4ac5253d25dc66e103587e22cf9debe4e6020cec8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula:1354",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula:1354"
    },
    {
      sourceName := "OAI.PiExponent.CurveProductFormula.positivePlacesFintype",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "971cb0c51d4d6178123977e64b79d05d4aaf4228a863caaca9095e93c503e91d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula:1965",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula:1965"
    },
    {
      sourceName := "OAI.PiExponent.CurveProductFormula.principalDivisor",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f4609e3cffbccd87d121ce0600773a6c717b5968822aa4573c55b6bf66f80ec5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula:3781",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula:3781"
    },
    {
      sourceName := "OAI.PiExponent.CurveProductFormula.principalDivisor_degree_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "17f268a02a611948dd09af34c408884106aa424dba7573409f0b5f4d8abf486f",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula:4972",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula:4972"
    },
    {
      sourceName := "OAI.PiExponent.CurveProductFormula.sum_positiveOrders_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4b4c7cc4013950dc10dbf0cdf30a4cee1b26c074ef725df5e2066f5dc056188f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula:2356",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula:2356"
    },
    {
      sourceName := "OAI.PiExponent.CurveProductFormula.valuation_constant_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1c3a8217983d464cc4981d2dc43cf1ab9d5334aeed02ac19bebf7bca844b7598",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula:7404",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula:7404"
    },
    {
      sourceName := "OAI.PiExponent.CurveProductFormula.valuation_pos_iff_order_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9dbb2bf06bb46cfa590e64c7f4dd87c5bf748f6264c4e9642e202506354c06d3",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula:736",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula:736"
    },
    {
      sourceName := "OAI.PiExponent.CurveProperExtension.exists_stalk_map",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveProperExtension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8a8ae1f8979005c2d97354d09850d8b7764cb604f8f8c44fb5c0f54042915b5f",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveProperExtension:683",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveProperExtension:683"
    },
    {
      sourceName := "OAI.PiExponent.CurveProperExtension.fractionMap_fromSpecStalk",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveProperExtension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1410fd3ed20d21ac15c5ae2c1bdb197d294799048565020b364755c182103d30",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveProperExtension:264",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveProperExtension:264"
    },
    {
      sourceName := "OAI.PiExponent.CurveProperImageDimension.dimension_eq_one_of_proper_dominant",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveProperImageDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "469a07d616ca772ef641d7cf14292d1b2960b91a02c4abe1a1826f67f6c63567",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveProperImageDimension:1209",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveProperImageDimension:1209"
    },
    {
      sourceName := "OAI.PiExponent.CurveProperImageDimension.genericPoint_map",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveProperImageDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f5d193e75273581acc3451226b77afa0765d273c2b83c787b5674a1697c3305c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveProperImageDimension:301",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveProperImageDimension:301"
    },
    {
      sourceName := "OAI.PiExponent.CurveProperImageDimension.image_dimension_eq_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveProperImageDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "63b25b58566fa174ac32c82f58242c8ae5aaa79af023c0383181907867cc21ec",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveProperImageDimension:2126",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveProperImageDimension:2126"
    },
    {
      sourceName := "OAI.PiExponent.CurveProperImageDimension.image_dimension_eq_one_of_nonconstant",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveProperImageDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fa5a5327b609f35a48da86009791e681ecd2335bd64abb5040cc90070e1e5d63",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveProperImageDimension:3174",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveProperImageDimension:3174"
    },
    {
      sourceName := "OAI.PiExponent.CurveProperImageDimension.image_nontrivial_of_nonconstant",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveProperImageDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1cf2b8761a845e5aa0111699584a0c2989610cd3fcf36630d1224e80dfac2c7a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveProperImageDimension:2587",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveProperImageDimension:2587"
    },
    {
      sourceName := "OAI.PiExponent.CurveProperImageDimension.target_nongeneric_isClosed",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveProperImageDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "faae0532afd31ea575794b76454280ac8dd64bff1aa38bc36ebdd5c60234dc5c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveProperImageDimension:680",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveProperImageDimension:680"
    },
    {
      sourceName := "OAI.PiExponent.CurveSectionDegree.AffineFrameAt",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      graphKind := "inductive",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "013cec1aa9e18efb9717629fd4e4fa43fedc210608e90e71116169b3a37dc931",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:361",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:361"
    },
    {
      sourceName := "OAI.PiExponent.CurveSectionDegree.AffineFrameAt.casesOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5677cc2ca62be934276133e522499d58158b0e2d16afe7832fddd49de5e3a81e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:361",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:361"
    },
    {
      sourceName := "OAI.PiExponent.CurveSectionDegree.AffineFrameAt.frame",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "36bd4b156d6022e493183c3c763c61d836ad7c024c4bd249aaf1358cf5140b8b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:361",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:361"
    },
    {
      sourceName := "OAI.PiExponent.CurveSectionDegree.AffineFrameAt.mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "baac86b0f5a139d078db1374bf54780f8a1649a1c6c50af45971e0e3f618059f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:361",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:361"
    },
    {
      sourceName := "OAI.PiExponent.CurveSectionDegree.AffineFrameAt.mk",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      graphKind := "ctor",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8b038f00a50d143814beb51e220a584d6a46f6732810097bb1e7f9aa2eaa60a4",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:361",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:361"
    },
    {
      sourceName := "OAI.PiExponent.CurveSectionDegree.AffineFrameAt.mk.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0f0fa670cb6f96e8c2a0d348d5327142638928a42bfcbaa01bafa42e376cbdb2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:361",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:361"
    },
    {
      sourceName := "OAI.PiExponent.CurveSectionDegree.AffineFrameAt.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7312e2f51948b01a0df968ddefd8fd8ed6a72a229eaa591e217f33d682f34bab",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:361",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:361"
    },
    {
      sourceName := "OAI.PiExponent.CurveSectionDegree.AffineFrameAt.openSet",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "58a4b2626eb0886393104247746ae6472fc80700b166240c9f953a1bf609b558",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:361",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:361"
    },
    {
      sourceName := "OAI.PiExponent.CurveSectionDegree.AffineFrameAt.rec",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      graphKind := "rec",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dfb0a29e5e9d8f5caa72a7eaaf335566926ba0dfadd6ecb3eea23e4fafbbd86c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:361",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:361"
    },
    {
      sourceName := "OAI.PiExponent.CurveSectionDegree.AffineFrameAt.recOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "53343d9ee44b59610c705c9d80770ad6861e0989c087f08bd86300772308d496",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:361",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:361"
    },
    {
      sourceName := "OAI.PiExponent.CurveSectionDegree.affineFrameAt",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e2fb4fdec283ce21034477c4366a51fed8833f92f16fdbb0f521d73e96297a6f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:830",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:830"
    },
    {
      sourceName := "OAI.PiExponent.CurveSectionDegree.coefficientGermAt",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "975a9b92c5cdab0acb7ea8ae7ed8fd1801b4175ad5506d291f562c22bff7c77f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:950",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:950"
    },
    {
      sourceName := "OAI.PiExponent.CurveSectionDegree.euler_difference_eq_sum_zero_orders",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2f8fb94aa4ce0f941128e435f8f0d28544b744cfddb91befc9f25881833b077a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:1958",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:1958"
    },
    {
      sourceName := "OAI.PiExponent.CurveSectionDegree.nonempty_affineFrameAt",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "df8da54ca0d5a617c015f821ca039d7b218e0731999276bce8f5cb8a0928b488",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:540",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:540"
    },
    {
      sourceName := "OAI.PiExponent.CurveSectionDegree.zeroPoint_ne_generic",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "129fc78132b066cca0d635f580ab80ab0e053e32c8c0b9575a1c85e917050506",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:1183",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:1183"
    },
    {
      sourceName := "OAI.PiExponent.CurveStalkGluing.exists_morphism_of_stalk_maps",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveStalkGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ed58455f4e25697490a164520ed71ece3cb3b687049c799167df69a110adbec9",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveStalkGluing:3442",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveStalkGluing:3442"
    },
    {
      sourceName := "OAI.PiExponent.CurveStalkGluing.genericPoint_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveStalkGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8fd3b66a2555bb776992dc7623c454ca621e07d5b671d70973825bb4a9f3c280",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveStalkGluing:1079",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveStalkGluing:1079"
    },
    {
      sourceName := "OAI.PiExponent.CurveStalkGluing.isDominant_fromSpecFunctionField",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveStalkGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0231c5c20017beb0ed61b0375bc5a051b5c3fdbe376d5cfd2b563033a2ab9d1b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveStalkGluing:714",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveStalkGluing:714"
    },
    {
      sourceName := "OAI.PiExponent.CurveStalkGluing.overlap_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveStalkGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "136d799ae33d7118087bd140c7835cdd44f7db5ac3b5f1d1ac1fc00e203eafc7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveStalkGluing:1696",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveStalkGluing:1696"
    },
    {
      sourceName := "OAI.PiExponent.CurveStalkGluing.specMap_stalkFunctionField_fromSpecStalk",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveStalkGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ef11297e7e87705857c0e9ca04a82708eff7782ff8a4ea753a7cee54349654c2",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveStalkGluing:298",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveStalkGluing:298"
    },
    {
      sourceName := "OAI.PiExponent.CurveStalkGluing.specMap_stalkFunctionField_fromSpecStalkOfMem",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveStalkGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "74454d1182d509ae7994c29f11d7110ae76047470708e202c609176d7eb71171",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveStalkGluing:1228",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveStalkGluing:1228"
    },
    {
      sourceName := "OAI.PiExponent.CurveStalkGluing.specMap_stalkFunctionField_fromSpecStalkOfMem_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveStalkGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "44705cfb304bba7e3322a534bc69aa4b4de5648c497b49d91537712f7dc9b3fd",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveStalkGluing:1228",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveStalkGluing:1228"
    },
    {
      sourceName := "OAI.PiExponent.CurveStalkGluing.specMap_stalkFunctionField_fromSpecStalk_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveStalkGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "38b540def87b38a21964d7b29b99eb62f87a58bfa063d7e9b42b493ce662a16a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveStalkGluing:298",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveStalkGluing:298"
    },
    {
      sourceName := "OAI.PiExponent.CurveTwoAffineVanishing.cohomology_subsingleton",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveTwoAffineVanishing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e98b191271364cfbe6ddae1bd385936c7e34007c81377b1d1c97fd70317351a1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveTwoAffineVanishing:421",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveTwoAffineVanishing:421"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.NormalizedPlace",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "inductive",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b49daf27e6eb76ce85c5e56816f323ef076d91223e4180e60acb06024f57cb00",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:12391",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:12391"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.NormalizedPlace.casesOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "58ae96bbc2c4f28a7d2e9593d32f97d7eade328152c5328ec7d3ae1709e6e77f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:12391",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:12391"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.NormalizedPlace.constants_nonneg",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8fa6fb436fe8b2cca4185d0d3449577078c86c80924a6fce8c93fc40f26acdb9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:12391",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:12391"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.NormalizedPlace.ext",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "66b8f22cb5e565332e6b360593d0e654a8589cee50965e94614a12a38701d8b4",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:12664",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:12664"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.NormalizedPlace.ext_iff",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f4b2a492a9f3f6ea8f4c4a8d0fabdd9ffb5ee3e36a4ffc939620b1f7cb96dc3a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:12664",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:12664"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.NormalizedPlace.mk",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "ctor",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a06dbdec6544ccb5b69d0e4c39234b6eaa490edb10e0453ae04fe19933751b64",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:12391",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:12391"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.NormalizedPlace.mk.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b1cb4ce38d5209173c21adef2462356099df3d6c52a470a8059c69661ccc69df",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:12391",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:12391"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.NormalizedPlace.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cc5f63dc9891a10b5bc38daf5787ad36a2bd8d98df255f6389044295a4d7df74",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:12391",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:12391"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.NormalizedPlace.normalized",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3822d4707462df8968f9a18080183c2a955ceda0b791fd1f9926f7b2cdc52891",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:12391",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:12391"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.NormalizedPlace.rec",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "rec",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "182df821a76cb14cbf1ac1ef75a2e2b59a1650555c4d82baaf57b47c14842b38",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:12391",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:12391"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.NormalizedPlace.recOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0388ebd52809b20df79ac2c333ee7616a9ec6ba0733dd5051a2f0599caa86663",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:12391",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:12391"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.NormalizedPlace.valuation",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a285d34c761e2214b2c258463431087499366aabf54ec6ecc221cbce40b190dc",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:12391",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:12391"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.aeval_mem_valuationSubring",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0b9090040b95e4220196c3c413fae420ef242f28e40536895591b9f360f7c2f7",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:1104",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:1104"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.enatToIntegerOrder_pos_iff",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9b3d4a78f098509dc35bf36ab7f9488c57a5c0c9c5707d1e853c32348d23c4c1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:11490",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:11490"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.finite_positivePlaces",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "de7464f30981fea596025f24e02b1558093cfa2f38fe653bb2792790c1fe257a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:20455",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:20455"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.integral_mem_valuationSubring",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a81b1fb6dabeeedeb7ec1139946fe1c14835251a6474dcae886a7e9d5050ad06",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:336",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:336"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.mem_parameterValuationCenter_iff",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dee809e21793b4f2bb6b26a05dd89500051685b05cf5e6f897619cab5fd69b5b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:3493",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:3493"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.parameterCenterLocalHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a1f9e81cf65d88123cf9e92334e85d3427e56ccebb595aaecc7d1ffc39b1f33e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:5216",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:5216"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.parameterCenterLocalHom_algebraMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "75591df01c434e98a4742145a8158c7e1e6a62c9a3ebfb75848e7e2f3acceb25",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:5942",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:5942"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.parameterCenterLocalHom_coe",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c1e2025dd41d0ebd02381a3d324015dd90485f890e3ccd89493df65aa3bf02b5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:7204",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:7204"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.parameterCenterLocalHom_comap_maximalIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ec3cb6b65280d923fcead2ad40ca37734c02bbcbbedc8d52ef8111f5cecdf55b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:6391",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:6391"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.parameterCenterLocal_nonneg",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "65a2315c462c564f3dcaea42d2c5aa3477df82e59d8944d902781d6295030a41",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:8273",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:8273"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.parameterCenterLocal_positive",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5880247837bbb60dcb1d1159aa9feed628e14f3200c291c831c7e3087b4b76f3",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:8938",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:8938"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.parameterCenterPlace",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e08ca1ec5c4c42fd547511a45c593407336a56f4a5971f54b3031a4dbfe6f334",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:4779",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:4779"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.parameterCenterPlace_parameterNormalizedPlace",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "de066a221275c1d25e00bc2a02a95f543ecee8c08647430f00609f0f50006703",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:18612",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:18612"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.parameterChartValuationHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "48dc7efa9ffbe370819b4b08160a4c67473d670e4308bf1b3843b9779c9ec59b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:2283",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:2283"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.parameterChart_mem_valuationSubring",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d77a4e778894fe7134c1af8d67d44963bccdd7a01d607fd17046cef04eaede11",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:1734",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:1734"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.parameterNormalizedPlace",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1b8bda5c94157b9595e68394eed0dd5ed55448b172d182255f6dbc034c8fee7f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:17791",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:17791"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.parameterPlaceValuation_constants_nonneg",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "25f8c3233347d9f02daea389bacc03c7148b2a299ed67bd37f794e9aca34a6ef",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:15461",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:15461"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.parameterPlaceValuation_positive",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d88c4d9fef05604e94e38abb26fd800f763ffa6e55b67e40d630bdd47b1812f7",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:16492",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:16492"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.parameterValuationCenter",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f5e968aab0deeba6c84b1c61f80d90b261104b81311b7c15b94963e4c1c449d3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:2742",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:2742"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.parameterValuationCenter_isPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b5d5db0ec2b9f50b365b28b9cb494015ca259907dc2e3157a4073bbfcdeffc82",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:3122",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:3122"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.parameterValuationCenter_liesOver",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fb77044fd03dc30335a92d012655b4ef5495b9590ea725a3a52b3ab460dc1f43",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:4007",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:4007"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.positivePlaceEquivZeroPlaces",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b4544e8ce3570fb02f0b1b0621131968af7fcf0f8571abc89d00bd1ed88453bc",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:19726",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:19726"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.primeFieldValuation_algebraMap_localOrder",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ea755fb6f987a4fc53f476f4a3e07fa5c33144749cc47b3f62f561b6ad87d823",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:9818",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:9818"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.primeFieldValuation_algebraMap_nonneg",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ef60ac7bd8a51e2ed9561810b0e365737c750cd0f23036d00e4f631d6dc188a8",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:11076",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:11076"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.primeFieldValuation_normalized",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "805b9caaba6fb54a6c7a0c96b24d6b532aae0d55643962d832fe0de595f00f73",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:14601",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:14601"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.primeFieldValuation_positive_iff",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ef94b9784555a4ada7f7167bdc9a10b3c5d7aaa5f4f0b5831c2e160b687b223a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:11732",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:11732"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.valuation_eq_parameterPlaceValuation",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c59519adba995ebe28f4f49ba00daf5ee1397967aad5a9110891b231ad52f93b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:12874",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:12874"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.adjoin_inverse_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3e8eb8e5891f76dac4433b6626de6a62e7ea0dd57406c7be7121b0e137c059e7",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:2331",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:2331"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.baseParameter_nonzero",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6819afd473b165c7a4e253041480d7d6f6366bb2dddcbbfe9920e3fd96a4c3d9",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:15764",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:15764"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.constantCoeff_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d1caae8e22b6a8c2285fd98e3af7267213ab350c539039521933d4a193e1b016",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:7608",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:7608"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.fiberDegree",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f7e8dd405aedcd1b760ca454ea552e64cc46ea319b2e1a62e0d9e3454931f554",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:536",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:536"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.fiberDegree_eq_fractionField_rank",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "70bc7313561659530e962b3817d73be49ec2a185715813b894c74f7f7c441f04",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:1189",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:1189"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_008.jsonl"
