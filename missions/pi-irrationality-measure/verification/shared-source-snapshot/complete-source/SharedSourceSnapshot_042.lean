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
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatePowerVertex",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "66ff87be710d748415d45f5279a38f18bfb92c2ade6c3b48323f7bc60707baba",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections:4601",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections:4601"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatePullbackFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinatePullback",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "227e237c5ac4df93d0012fa1171a0a488fb75f3c084ae3cd0bee6e793e18de71",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinatePullback:1021",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinatePullback:1021"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatePullbackFrame_coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinatePullback",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8bd6c646c12b74cfcdc4cd067e77a7270e46747cf1ba1decc0ea719c52fadbbe",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinatePullback:1539",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinatePullback:1539"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatePullbackIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinatePullback",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9fc97094347d4b0ac9065740deea22c1f93a8d759c4f3b0c4c88670866a628f0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinatePullback:2660",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinatePullback:2660"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatePullbackModule",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinatePullback",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8bb7b393b662ffea77c591b7def70df0fa7b01b128ad686ae9d8880615ce2fa2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinatePullback:669",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinatePullback:669"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatePullbackSection",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinatePullback",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "62c68afb7423ea7095118669273a3d2c34c79c440128dbd7d8dd50c2a77668ef",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinatePullback:843",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinatePullback:843"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateRatioOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "013df5fb77f6c3fa3e076bda4c109d00929c159546a42f8421aba4deb026d9f2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios:535",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios:535"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateRatioOn_change",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "17f3aa7dc7e39446e51b533b4a9358b42cbdfb5e151e555638901bf6c603a595",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios:1378",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios:1378"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateRatioOn_eq_coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "832389f993c0eec8909b06d6090a92f110ba8e93989d48c1011020b799e3aea0",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios:825",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios:825"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateRatioOn_reciprocal",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f9dc44f87bd72e60033b6da35d3da8600a72d8b6c540085f63b44722a0be9c75",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios:1900",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios:1900"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateRatioOn_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "431683d214b993940c01d20114e98735a87f15a63f4a9beb52ad60b5949b3666",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios:2200",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios:2200"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateRatioOn_self",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b360f9c4970fc5d61e2a897190711ab049b4b853574e8b257a2c081c7aac9783",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios:1159",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios:1159"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateSectionChartIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6d1c55336fb773f27e8d5cf0f5b216693269e7b088661541e264b8e62bd3bd0e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections:1774",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections:1774"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateSectionChartIso_factor",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3dc2f19d86dbf1b8aec1c8c5f14744a49b9783131734ab4fbfbc4146c6f5d355",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality:2095",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality:2095"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateSectionChartIso_hom_away",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c4e65125422e484cc692c11eda3a6543b34fba40ccc2927029eae29429c24a75",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections:2161",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections:2161"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateSectionChartIso_pullback",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d3ee8ac6224fb8218ff284ed8a8458767304cf97a6380b9b9049a6a63c2b06bf",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality:2734",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality:2734"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateSectionRingEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cad279d68b68eb03328ce9cba0e1d43192ed678053c66d7758946e6d9ecd4ba3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections:2611",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections:2611"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateSectionRingEquiv_constant",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateConstants",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "361eb3026a6972bc26fc98a9b972cafc4e28fe02c09cc4b01d6792744e657e95",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateConstants:4132",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateConstants:4132"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateSectionRingEquiv_coordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4b067a4582c42014539e1bb143f5dc2eef7bf005770cd80eddf4a4151a956d34",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections:2924",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections:2924"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateSectionRingEquiv_symm",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f765e866669d05270453f523a2cae271a56df2f2faaf220125fb6f60e23f68d0",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality:3467",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality:3467"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateSectionRingEquiv_symm_constant",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateConstants",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6b8067bcb4ba9b06e55a1663a5655dce5c0d04275b0dd670ae52b944c057109f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateConstants:2860",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateConstants:2860"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateTupleCoefficient_restrictVertex",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveVertexCompatibility",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "08a2069b2acd3445f036b7e307c8c5bbcfb55ad07885996c3517ad6f8bd59fb5",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveVertexCompatibility:1968",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveVertexCompatibility:1968"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinate_chart_preimage",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartOverlaps",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "947c37febd1791854d6e5da8a8a703c7eb45975a02167b7bb312e3dd7bfeface",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartOverlaps:846",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartOverlaps:846"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinate_finset_preimage",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartOverlaps",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0f8e3554a88ed967fe4e1596f45bd2d2a10a7e635ada0cb05e0dc88b9a6b40e4",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartOverlaps:2586",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartOverlaps:2586"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatesMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "26b001e45d193ed7b14619ce6b7d106e22921c67c4a54d721b62febf4ea7333b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:6400",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:6400"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatesMap_congr",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedAtlas",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0b0695b22669b61995f9a3f6f672b5d5d2b30be5d9590354a9f2035cff421b4a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedAtlas:387",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedAtlas:387"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatesMap_natural",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4b7874449f6688532323512535c2988dd94ca2cea74ebedd2150c61c5422c555",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:6978",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:6978"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatesMap_natural_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5671001d91dc4699ba1f0a5e159224a2c01a9945353dcf9359e54160fbecfae7",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:6978",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:6978"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatesMap_over",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9b97ae3d0974941c16963fe298caf023662753006b5d23997559950a8092643f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:6631",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:6631"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatesMap_over_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7644cc285cfe9e42a376c43b0b6dea3e9d9162a191adedf81c14fb6c8483ef5f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:6631",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:6631"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatesMap_preimage",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "53974810bb71553427bd8f97e4aeea1cc33a254a8edcf6beb0598b6f73d4c7ed",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:8977",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:8977"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatesMap_pullback_constant",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateConstants",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "01c4250dfe6a83744e19cf18f7acb2f83397429c09f77f45175ea73cd6d9ff91",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateConstants:1242",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateConstants:1242"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatesMap_pullback_coordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateValues",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dd4ac194c13f7f90d7741119e6dc358a63c35d427240e4a015d7137aa5ceab9e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateValues:896",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateValues:896"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatesMap_scale",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "43bc0f8ff8608c58a028600b240db36301009e97abab58cccd1f312bf0246207",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:7571",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:7571"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinates_X_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "70db76fdc3cb6e054b8d02645357000568ece31805bf5ebff7f37162cb8bab73",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:6287",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:6287"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinates_eval_natural",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a23dc6044df09520f0761e4d915912934a096c6d7ad6545e559f4a39be7a0093",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:6716",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:6716"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.dehomogenize",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b627f1203bd4976e05542fa5c34d2f8b810fbaadc7cfe5bbaea7aec6475d717e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:1700",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:1700"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.dehomogenize_X_self",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7f03970097758d20d06212363102eeee77209abee4e6d042074a40dfb5c68fc1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:1848",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:1848"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.evalAway",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6a664ff063f3e30b8e238038f864e3f0c92c08bbbf6837461fb0bc72226a1e8e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:453",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:453"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.evalAway_constants",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateConstants",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d7ca05d46dc2ff47e2fc464dddf71f0f082e8c1522825960fa4c730c281e2aee",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateConstants:413",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateConstants:413"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.evalAway_constants_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5eb3b2b49688dcf9f9749543e3c6fc5d5e59cc0b99456bdf8db2e4ad02f562f8",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:5710",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:5710"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.evalAway_coordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateValues",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "427ea52f74625ab6976ddca83bbf0c688b1d62902e916815166ab09a3d9e468e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateValues:337",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateValues:337"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.evalAway_mk_clear",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "17b3cbe33e906a9a41cd2dc73a48361fecd395bf2d7cf29184fcda57600999d1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:2156",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:2156"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.evalAway_natural",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a89fdc37b5f89912da5ae4a6c0f1f108be6532ea4ca05a644d706a1f8e1454aa",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:1583",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:1583"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.evalAway_scale",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "78d658d7c571f076d3621625850e4ab0d92b7e98fe16894ba3bdc65902fd9294",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:2685",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:2685"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.evalAway_transition",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "466acf83441a41388148b6169f0807592956fc7b9c741b184e5f83b5960d1bd1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:784",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:784"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.evalAway_val",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c145259bd28591785b6b7d2258c33af031a036044ef5ad2202d9f0efde5acdef",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:646",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:646"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.eval\u2082_surjective_reindex",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionReindex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9e0c14302ba43647d9a39f96b96a9ff05800474e60cdef14c107f7cb69ecbc8a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionReindex:8138",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionReindex:8138"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.finite_pencil_chart",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "89fbd5219c2fa8b5e66cea35b3dd5e738dfc2340e8e13f958bbead3ed38ae9c0",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts:5640",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts:5640"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.finite_sectionsMorphism_chart",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "04b5106c297926088a420825db03a7a9dbc7ae9e441ce5290d4c267a604fed6b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts:3213",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts:3213"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.framedHomCoefficientsEquiv_change",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "83d8e3c47ebe6cf0c2b41640d506be24a0ebdcd54128fca9bdaddc66802cc86d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios:2593",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios:2593"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.framedHomCoefficientsEquiv_eq_of_normalized",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "36cabd3d90b7ad2b30e26938311aa888ec520f450a90c684673b17375e674ec7",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios:4237",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios:4237"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.framedSectionsMorphism",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aa45472d4cfd674aca32d4958197c1ca8b950d9bde08452fce5033b87d9a6215",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections:707",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections:707"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_closed",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cbdec25bf4129353c3a905e86099899ba711192b636ddbb401ac84566526e55f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections:2841",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections:2841"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8d1ca086038f147e9165ae7bf2cae9d6ad1934e8e25fe0a292e334a88c96a23b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections:4724",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections:4724"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_eq_sectionsMorphism",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "45f669fde0b8ef5e14f46d663f56e6c136be6cf5ad513378e2dae997e15c4538",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections:6553",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections:6553"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_local",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f044ad77093c6bb2ae506d505a0de15eff1c0a2022b36dae91b4cff229c195e6",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections:863",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections:863"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_local_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a20d3ba055f52e19fc14db306051666837e31422dafd1316f42ab00acd16ebbf",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections:863",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections:863"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_over",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ad92282892cc7b2f5129c545d2ca3fe03af386eddf0b872f685d70b5ba69ad0a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections:2007",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections:2007"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_over_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e10b7032d836d135958419d1f7acf5ec15d73348a267a5b7e257dc61000e42c1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections:2007",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections:2007"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_preimage",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f4d04bb59e10c6fbf4ad6dfe4bf196be0016f942f545407820919ca82b33321b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections:1253",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections:1253"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9f84642611d5931a8b7c0ce10fa2901d1abc3848915a179ca2ab467d185c43b9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections:2480",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections:2480"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.fromUnitCoordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b6bd2e8cca1d8dc0aa812a7f66d790c69354bff2427aae725e79bdee157c46aa",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:3398",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:3398"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.fromUnitCoordinate_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cba1c9bdda6291a98af6238f4af0567e9fec81f4ab0c32cac4e9ae5685dec917",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:5587",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:5587"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.fromUnitCoordinate_mul",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "31d77cc64fd736f8cd668ae27e6bbf243d68124e1e7ffc111afe9721fd3b004a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:3622",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:3622"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.fromUnitCoordinate_natural",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1913345f17d5d3215dfa15d4ffbdac17b6a5e34585cb4d3f3fb952da5fdcc9cd",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:4110",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:4110"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.fromUnitCoordinate_natural_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ac102823dd8d988c7f02b9460368374fd3f0d54a8300aa4912c15df8332508cc",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:4110",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:4110"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.fromUnitCoordinate_preimage",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "648d8f6966de07ecf0b791012c33c93bdc2e1933115abbb8e849721f01fa69bb",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:4902",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:4902"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.fromUnitCoordinate_scale",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0bef710a523a2dcdee47b9e2d026975368f8990ee500295fed2a613a9cdc993b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:4531",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:4531"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.homogeneous_eval\u2082_scale",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aabaaf1804dd8ba1b97e11020c29f1f960b91b7923fd4fa9ed31bd71eb0b4a1a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:300",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:300"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.identityCoordinateOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6c600aaae1332a829220292238a23d9e7ece74b46e0d8cce3ebafa891aee900b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:16324",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:16324"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomSheafOfModulesRingCatSheafFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a9072912f61556764e941c0e28edf6eebd07d989d27eecb33cf4bf63359834d0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars:3554",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars:3554"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomSheafOfModulesRingCatSheafFreeOpen_1",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeScalars",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9e460fa180457d1820d49a71a559213d5f6b0af984284af9f8a3792532ed56ee",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeScalars:1029",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeScalars:1029"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.isoPreimageSectionRingEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "098bb5342f1b21bae3794a048305073855e91337b0ce804e6e08d8325274d4f5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections:590",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections:590"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.isoPreimageSectionRingEquiv_appLE",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "830421d13cba147dbfab55da4d33acc2d89210525263b240373cff70cdd74ea8",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality:825",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality:825"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.isoPreimageSectionRingEquiv_symm",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7e7edd4be1fe6a814c0b8df05ef005193d1963faca921182275887c2ff79eb41",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality:303",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality:303"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.negativeCoordinateFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeFrames",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "be9bc766286d116698e617adc0ca4043eb15548d1c3bf52473333c1354b73693",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeFrames:466",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeFrames:466"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.negativeCoordinateFrame_frameChange",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7f39ba6647f6c0e9a1315ab4619d7999f15a01dbd710e5b05be646a009c98b1d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeFrames:721",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeFrames:721"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.negativeCoordinateFrame_hom_change_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "12733876f1ea8b9f6a4c9402c836d70a19dbd164d30263af95405fd53e435677",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeFrames:1655",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeFrames:1655"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.negativeCoordinateLaurentPresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "de7a0e900f5c8780c68a082191350b1164a712c670a285e5ad9094149f2c7cbb",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeCoordinates:3416",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeCoordinates:3416"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.negativeCoordinateLaurentPresentation_smul",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeScalars",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "70cb03124af1822a1aa01a38cdf3b75bf835abe7db8805a93c68ff0b216d14d8",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeScalars:1273",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeScalars:1273"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.negativeCoordinateOverlap_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f07f08cabc10f25bfca6fc573a87d39af63877886001f510823acd4970747d01",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeCoordinates:1099",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeCoordinates:1099"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.normalized_coordinates_closed",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b401faaf7cda1b2192d6bfe4903ee2d6446d2405cc67c002e478e4d8d51ce953",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:2611",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:2611"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.normalized_evalAway_polyToChart",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3d8b39c2eb109ba735bb7bd17bae0ff3395041edfaea14f1a6f464e5c940a45b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts:1973",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts:1973"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.normalized_evalAway_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8b12ddfbf4d24028cdc5c7a274ff701ee96965152e561cfeb7dbf41efe5c06b0",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:442",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:442"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.normalized_eval\u2082_of_evalAway",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionReindex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "804d6691a9147f5f10782f865eceda17ef9815030e20d185619e2f4823f00fea",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionReindex:4101",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionReindex:4101"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.pencil_overlap_basic",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5da6396ba77cdb16201032e0981f8e5174f0aa1cc1ae8f3762f893a013c4b7b0",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts:7514",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts:7514"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.pencil_overlap_reciprocal",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6d469af3d4a5260ad2239ece7ed4e51eed34c3cd6373387910dd79f9c2c131c5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts:7860",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts:7860"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.pencil_polynomial_irrelevant_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "288cb6e21bde2b5f089e04089a376b67e0f8be5960fda91b3087b004c9073159",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts:358",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts:358"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.polyToChart",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6823aed170898e0513498fe538780541a54ed81d17342372c61014fdc16bd352",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:2130",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:2130"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.polyToChart_comp_chartToPoly",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "be534680c7a9b7e8b5791460eed2a9ad468acab6b0d2ae5544103bb9e944c016",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:5150",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:5150"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.poly_X_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1cbd07372e63c2cbe564cfb312cadca378c8332d5f84856d764c8a1f45853360",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:1023",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:1023"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.polynomialChartEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9d1c1fbc8fcbdd31fe66bb300b01326c629cf5c84215612c83b18b637e5807b3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:6128",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:6128"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.projectiveBase",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "421c15b8c7e8187ef0c79733929b26569fecc5a6a694effe461e006d29a8759d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:5535",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:5535"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.projectiveBase_separated",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7697077853647d0ca5d5d64c136c4417a3f78a48a2418d98e9472bfd9f95d1fb",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:8118",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:8118"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.projectiveChartIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c17097e6c9d6a0beb0c97089a287e729eb5729b56141c521b24ab0f1a51fe9dd",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:6436",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:6436"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.projectiveConstants",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "46fa83973bfebd28bee51f84b1bde92aa089d46e3d6070de0ff109f1b96a3d22",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:5282",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:5282"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.projectiveCoordinateCover",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5e7cb8338c9d057d65b8bc9713224ef1c2e3ff6a64b9cc87b6d75da03b20826c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts:848",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts:848"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.pullback_isoOpen_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionsPullback",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "78f88720a97fb392ebfb5310db81a0350e1d87eba87f5a4d41555c52831caaf7",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionsPullback:2241",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionsPullback:2241"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.pullback_sections_cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionsPullback",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "72bc5130ed46fe6a5e086ca62750814b94e2f765a6391c86abfcc1bb20935b05",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionsPullback:3069",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionsPullback:3069"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.reindexCoordinateCover",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionReindex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e924bcaf1f1452dc23118c74a1ebc38bf1e251119be99f82ac741dbfbdb3009d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionReindex:834",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionReindex:834"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.reindex_polynomial_irrelevant_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionReindex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dcd56818987261e58e6449540ff6298248b13ce70ccb7f1106d8642896c5dd6a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionReindex:345",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionReindex:345"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.schemeIsoGammaEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b6af1a9c43dca7c0aa0036f422a7ced1a1cd28e797be771772a146aa7fb60f5f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections:765",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections:765"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.sectionFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c690eea0779297e936228ad6223f9f62734a47d57d05c91c105947f1c8b7c45a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:12834",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:12834"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.sectionFrame_coordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateValues",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "66e8331b0eb8a96163d923a9b1e1eb52d5dd289272d5f0a4448a3af9a54216bf",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateValues:2264",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateValues:2264"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.sectionFrame_normalized",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "30db388310f74ba62d464c97af32ddeeb2e97e2a0eb193697300a83b73aca95a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:13189",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:13189"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.sectionOpen_eq_coordinate_preimage",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "12004d8bfc240613e8a0e113bc8973d2b50ad352dcd2aa8896905febf460968b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections:1547",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections:1547"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.sectionsMorphism",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "45797b2124478b734c052a40078f4888faa9823aaa870debcdad32e80aeb3bfe",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:13456",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:13456"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.sectionsMorphism_chart_generators",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionReindex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "791e1cbd8cb7490d0a6a9773dde4d0dc0abecb697fb767c01271e9782e5b62d4",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionReindex:5675",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionReindex:5675"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.sectionsMorphism_frame",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionsPullback",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "be7252decedfcd6d0b939aabb97066e5f0e7dafc10ba7cf61a5f1176d3e3b839",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionsPullback:449",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionsPullback:449"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.sectionsMorphism_isClosedImmersion",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionReindex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9191df2a8bb0aa5704c27ae859bd1ecfb41ef60507f3ff0232a7942ba98e8e33",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionReindex:1373",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionReindex:1373"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.sectionsMorphism_local",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "efe68e30d55e27856d7480a15df961ca09e0823415680cf82a899a5131468163",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:14110",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:14110"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.sectionsMorphism_over",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9099b0a80ee2a5bc15c14f94a00985f2f8cde290f7b07b9eea95efba3c9b28e6",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:7128",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:7128"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.sectionsMorphism_over_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6d30d51e12bc76ba38f8ad4ab04ac1b66e8d05d7c0ba74ebb0cc3cfa495e63cc",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:7128",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:7128"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.sectionsMorphism_preimage",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6ca21bfefd78d5966022326f46e1a4186431902673b6202904ecac24d13dca05",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:14873",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:14873"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "33ece8ed007ef40c40bd6f486946f183c337ee6d79a73a612cdd61a34ab6aee7",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:8255",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:8255"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.sectionsMorphism_pullback",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionsPullback",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "88af512043f0390a471e94e8fd7d0bd68605e89d1f948a72b91204512e0f2e40",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionsPullback:3437",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionsPullback:3437"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.sectionsMorphism_reindex_closed",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionReindex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "290618ebc1c6b6b422de5dc10d4dc7df7a50900c659fe482e0f2a4c2996e0f76",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionReindex:8636",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionReindex:8636"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.sectionsMorphism_transport",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "559829a07ae1c41c3c10e24df3cb1a564efbe7d74fa9bf3d9e16f1652eaa5253",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections:8594",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections:8594"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.standardChart_cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b24c49957943822331ee637666a1a5d4f8d652f47eb269563c84933ecd11a3a0",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:7535",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:7535"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.standardChart_isAffineOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6ba3f19f692eae76b741870838ad4da76bd09ecfb1aad7ba3395a4b8ee47bc8e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:7374",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:7374"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.toSpec_scalarMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2f6e874b318b9fbcfd99e2d2eb7c0231cb114a8399e29bafce08eea97e20c268",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:8700",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:8700"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveChartSections.framedCoefficientsEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fb6a16df3b46d4464a3e0afebb5d3753d099bf16dad02ee59329965cf3f74ca3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections:1238",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections:1238"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveChartSections.framedCoefficientsEquiv_change",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficientLaws",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3ededd06100804d46042cffe339a1b5c76faaf8a9e9319b36bf6468dcad935dd",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficientLaws:1212",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficientLaws:1212"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveChartSections.framedCoefficientsEquiv_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFrameNaturality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1e4d422aea0d83033f3ede4408dc984e3a72bcbbda2bceedf5ccadd421f7d72c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFrameNaturality:3027",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFrameNaturality:3027"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveChartSections.framedCoefficientsEquiv_smul",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficientLaws",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0ec0688f50bb92c8d658a623a2292330e6ab06dda4d125b30bcbab59f2cdd893",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficientLaws:364",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficientLaws:364"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveChartSections.framedHomCoefficientsEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d24d21461ad3c9b946cf9e82a3680ce1d48bf37ef82d55e9ab61d70fce6d7d5b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections:1584",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections:1584"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveChartSections.framedHomCoefficientsEquiv_globalSection",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveRepresentedCoefficient",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "97489c6558895484a95f62dd06a1bdb8b5f74e76277822b9be9cd1966fd7e5f2",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveRepresentedCoefficient:1035",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveRepresentedCoefficient:1035"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_042.jsonl"
