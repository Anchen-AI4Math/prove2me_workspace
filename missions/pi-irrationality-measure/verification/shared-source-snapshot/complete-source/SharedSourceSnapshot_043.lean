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
      sourceName := "OAI.PiExponentSeshadri.ProjectiveChartSections.framedHomCoefficientsEquiv_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFrameNaturality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "05df8f443753eb2c0ddf3c4d3b1a6b69725f9b124031206d5b93d9890ec9289a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFrameNaturality:3586",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFrameNaturality:3586"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveChartSections.framedHomCoefficientsEquiv_smul",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6a9a30ff1ed230f7c9e633355252f4a121d53cfd90f60ec715ede65f12f48292",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars:954",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars:954"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveChartSections.framedHomRingEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ccecbf5c3c0531a3fda69680d6ba5d61a0e03a990d9fe13729c9aab3d45df617",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections:1784",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections:1784"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveChartSections.framedLaurentOverlap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9c7e597de429b115695f0c14192e912e313ca0255f0b4699b15dd49d3fac646f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections:3869",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections:3869"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveChartSections.framedLaurentOverlap_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "19d87dac2b4ed1f66bbbae63ec03d33fd6b8ab1a0fbbadbf5757c18ee29599cd",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections:4190",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections:4190"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveChartSections.framedLaurentOverlap_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "62237d84839bd37646030ebdf78ec12ba80d1456db0e15c575cad93ee32e95fe",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections:4539",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections:4539"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveChartSections.framedLaurentOverlap_surjective_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6238f04b7a01e7aaf424f16b42a9a78cb93028fd6d5b0c2d58431b72edb6562d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections:4933",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections:4933"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveChartSections.framedLaurentVertex",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8f48e1a43b42be498b2be4ce9bc88041645354c5a98ba3fe06ce259330a97661",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections:2183",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections:2183"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveChartSections.framedSectionsEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "121823e2b5051a18c258159d8f26565eca06aed9f9f7e4449beaa40246ee7c99",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections:658",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections:658"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveChartSections.framedSectionsEquiv_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFrameNaturality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2c6c775ae19628614d1939f11a3ec7df9a98d94855bc48664a793b8259ce12bc",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFrameNaturality:492",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFrameNaturality:492"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveChartSections.freeOpenAddEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "36cfabad2ed1348fabf9dd8494ed8e806f4f984e39b9b794b9103aa36e8b4cc9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections:1435",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections:1435"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveChartSections.freeOpenAddEquiv_smul",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "26bc78fbd3630d8a89d6169d7c9c45b67aa9b01467c756486d3b74b1d6a3c833",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars:775",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars:775"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveChartSections.freeOpenEquiv_freeTop_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveRepresentedCoefficient",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0fc65ba6c5928f92ae7810d14c13d7a4c0f5d17611d4c82b395ec77cab3940a7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveRepresentedCoefficient:488",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveRepresentedCoefficient:488"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveChartSections.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomSheafOfModulesRingCatSheafFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bd3e40b6eb1d819a73b09aea436ca181f9ce9b78a58905d9b6fd544a7c32665f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars:565",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars:565"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveChartSections.topIso_hom_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFrameNaturality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "583496ff28e5cab8a6820d86f266683e1f44dbc5c81cb339e82bdbea50851db3",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFrameNaturality:2625",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFrameNaturality:2625"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveGeometry.genericPoint",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f87c8fb6a882cb1aa31f607ab7e32622549b1408814f37df96d4e2322b665cbb",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:2162",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:2162"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveGeometry.genericPoint_dense",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c764455b2417e3fb93f2cdb2c1180fb98fdf4b94c273d4fa51777cd0751f4224",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:2438",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:2438"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e1610fee681f43ec181fb428ed1f3aeff7dead53793fb23bb5ef692f7b0d241c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:1612",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:1612"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "579da38e2a8ef91310278e646df8a824d37076855a23586bf70c0fd46e9d7ff7",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:2779",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:2779"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "555f03171d3e8499424dd5749d3648a51c6a2f43baf7bbf7d50d995d469c9763",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:3070",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:3070"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "89f717794f5163a6d2a99a9b33e929dd427a1ecd654887eb6f1b3061ea6ed011",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:1881",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:1881"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PullbackTensor.framed_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6a7c65125ff667a5348fc03ec37703bd2a9d7971ddfe611aa6c66c3bea2264b4",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers:9222",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers:9222"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PullbackTensor.hom",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "839422f40fa306b2c865fb232768795b2374f4da522170439cc757ee99215932",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers:476",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers:476"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PullbackTensor.iso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleProduct",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8c1ee673de3afc14d22b0826d378299f6a7ccf21b0296574911b2915949d779d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleProduct:3028",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleProduct:3028"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PullbackTensor.line_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleProduct",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b22cdbdcb62b4d5e516583d4a78103d74350ed820df93e08edfc15c698a81d2a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleProduct:1554",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleProduct:1554"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PullbackTensor.naturality",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fd5c9909e60bf7cca53f01cce4cdea1f82a1faedc977dc8795c11278b29ced41",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers:1386",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers:1386"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PullbackTensor.naturality_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "39025baccf9de7310fb24538ba445340119615279bf30a2250e6cd1fd9d48f0f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers:1386",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers:1386"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PullbackTensor.open_transpose",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b8ac9f95841595c78d4ed657b38256a72da8761e4a8fa2d4baccb60ec4102465",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers:6056",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers:6056"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PullbackTensor.powIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e880fb28e7f30d7c9b351afe94dc82a429ced1986ba07ed2df7ece26e222104d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers:11708",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers:11708"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c94fefd0cb23c623473528ad88b616a5caab149c9e63a11d441b2827c52bbc07",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers:10057",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers:10057"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PullbackTensor.restrict_compatibility",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0ca2f23f9b9a54fb17b9efa3e36e10014653ed3e1d84ba3e7a7eaa83e6c7c2b9",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers:6474",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers:6474"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PullbackTensor.unit_compatibility",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "613182111039c58c69a1797231cb693de299ccea40a872f0873773354921f399",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers:2433",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers:2433"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PullbackTensor.unit_hom",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a2ff7e345e569ef2ca86bb35d3c62a7de9b581c15133f918694ea080a8bd8c7a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers:924",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers:924"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PullbackTensor.unit_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cc14f48f378bd705bb832e9fb0960d13894c7a663ef5fa3b73d0247f7b79036c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers:5416",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers:5416"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PullbackTensor.unit_pure_structure",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "91498581dd23190588be93ff53c0508800d5b1dac23a2e7f804002f7f3c7ecf6",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers:2178",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers:2178"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PushforwardTensor.hom",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5bd51cf6508ebf8deff0f750a1e09c5b12aacf33d773d411674fc8fbbf923cfe",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor:1200",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor:1200"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PushforwardTensor.hom_pure",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c7c0a1edd044ca94865e45b9db49fc26dc605f68f603d6fdbbb49201882e6b95",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor:1450",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor:1450"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PushforwardTensor.naturality",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b8ab5484f7367f81317b4e1d8434f089631b4c2d0bc1fcf02e6a4e87622712c6",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor:2035",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor:2035"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PushforwardTensor.naturality_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0a5c8562cc7bda0f1a385f78a56775de98a8e1afe60d6219066d13ab17b1aa28",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor:2035",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor:2035"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PushforwardTensor.presheafHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6831400920f5cce1e7491805410f0abafb6d90a515709c45ebc9099821bf495a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor:491",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor:491"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.affineBlowup",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "db94dd9b884af6f3373847389c9ff1e6fd6d306308438b0d9a195cc3f36e89af",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:4768",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:4768"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.affineBlowup_isIntegral",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "06fd9d08407a78d7973c158f1296b6a3a0d59e23f662c4e13ac2d33fd1fcdfc2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:6054",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:6054"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.affineBlowup_isReduced",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7d6d5acaa6c749ce65f76afb24e4d974b8e88a26c60b769afb18e121a3a7be88",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:5795",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:5795"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.affineBlowup_universal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AffineBlowupUniversal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "847c465141f5cf91d0b23ec0ef3f149f73abbe0c505c4343d794b75343b93907",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AffineBlowupUniversal:2252",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AffineBlowupUniversal:2252"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.base_generator_comm",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9e677243b9f0c331bee6cfcd2952f884ccd4ceb768b8d9ad5e10f70448647973",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:4080",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:4080"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.base_mul_ratio",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "99193056d2f2943f906b22a11dd84ce709cf1e883365eef5c56a682341845271",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:10564",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:10564"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.base_pow_mul_mk",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "86d6ed014601a00837f3038a3eee9ea84d29d998716f97ea445fdba61177def7",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:377",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:377"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.chart",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "215027d2ad118941f7f5421473672f8367d4d366201c62493acc838355a582b6",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:7219",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:7219"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.chartBase",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1096454a1a0093d026a2df5b434aefeb164825f27fbe1d01b1d98aa88220c30a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:9399",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:9399"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.chartCover",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3f06fd2a9d8693c312dbcd499785d426a74dc675a01aac415ae9bbf06051be2d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:1776",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:1776"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.chartCover_projection",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a007c81d61be169954d62f78d6e4abe88f7ddd8014cce28aa2b4ad6938b41afe",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:2474",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:2474"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.chartEquation",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ad4185567fa4fff24225e4ad3d8b883ecf2f20c4c2497d95e2f6ce81bfc153d2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:4062",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:4062"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.chartEquation_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "408670263fac2d5aee247ebfe48a7a945375c4e853921162fd94e24bbd374e1f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:4606",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:4606"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.chartHom_ext",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8660bf62b2d7235ccd23d24be996daf0c5820d59edb6507c6795ead789b92451",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:4909",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:4909"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.chartMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b0be28de102982bf079be35f741c73ca6250a5a57ff22f461f40b0bcb3ffd243",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:7301",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:7301"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.chartMap_base",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "060e554681bb4e9d2b975bb7eef33d2e23f988e04bd1ae4290ef4485d7c242d7",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:9571",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:9571"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.chartMap_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c8be2fc85a9da69a176e37d8302ca089f3cd890de0d4a59b755d779043f98313",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:8292",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:8292"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.chartMap_mk",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bdcd1f24e6f5b78d6784fb7b0fb5f5a080ba7ec58fe998b0ac13df96cbf9491b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:7685",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:7685"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.chartMap_ratio",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "65afeaf9b1978e4e369e664b2ae0c9d4814353559f9c0f55d8404d7f407c9b54",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:10294",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:10294"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.chart_generator_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d4a01ef9a1396344f405e50d39af592e37d3ca38de2b5c291eefb8fd5203612d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:11925",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:11925"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.chart_scheme_ext",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "35d18e33ab114ff5f2e0b4168122986460bb20ac641c064429972df855f19b3c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:5573",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:5573"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.component",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0e44eb048ab1f5a3ecab0f5add3af107f4cdd01951a3778e0f540caeb85ba3f6",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:830",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:830"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.components",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7ce9fd26113231f0b322ffba05988df6ee6e0532a536e7ff0ecfb89abc6021ff",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:1162",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:1162"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.componentsAdd",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6da215f2f04f7bc004b2388c3c671a45bc13614d552a2d45c0df0193c3756e79",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:1689",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:1689"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.components_of_piece",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "90b2b425aa5de17029032df07720fd22ab53c57294ad6c47f7a6e5440907893c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:2299",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:2299"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.evaluation",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4f29a3e2fba50c4381506cc32392b51368fdab1e8caeadf46ce90be39cad4dc6",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:6749",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:6749"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.evaluation_generator",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e0a853e0ab9fdfd39be061992ab72080d1f1602b2f75cb5c6e91fb11ac178249",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:6859",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:6859"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.evaluation_piece",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b504d7589626c8d4f6e3692408e014a97bb1946d0352a2020f94423f49da6ff8",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:6971",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:6971"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.exceptionalIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b37b3044836892b4cd0b1b39f49fd83aeb4674991b691d6094cd36434a347795",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:3949",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:3949"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4a74970e849397bdedc1646c4b75554ecfbf640d51498f96ba981b090f48a97c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:5196",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:5196"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3f4a5916869eb3b92a9367dc94751e7dcc1b45f1db916880387f650fb29185b4",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:5351",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:5351"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.exceptionalLineBundle",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6e9e57049d95008f4d2c386566a82bac7684327c31bd573a68d15dce6a71806c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:4990",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:4990"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.exceptionalLineBundle_sheaf_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptionalSheaf",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "76efb8bb20b47e53c873170fceb7844bcdc5bd4d84d32eaefc5a837ea4ccc0a7",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptionalSheaf:196",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptionalSheaf:196"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.exceptional_chart",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e5ea9a8e8bc2c2ca853ea32191fbf517b0b172d6aedc07a0ec3ad30116dab7f0",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:4208",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:4208"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.exceptional_invertible",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8acec447a8d2d5bf5ee267045754c08d4d9d8451c1c7ef213fc32557842c749f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:5969",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:5969"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.exceptional_presents",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7e05ff957acd6a790fe7a51fba51941911d8c19127d8cb7230cd5d77dac0672f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:5520",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:5520"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.ext_of_unit_generator",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "37eb9751a058b01d886b59368e04e445053eb9effe588d595f68daaf1c3bd98c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:6081",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:6081"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.ext_of_unit_ideal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "baac9454e39e06d4a51fc80fe26f96ca114dfcc6acf4ba7e179892e2c758721f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:9257",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:9257"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.ext_on_generator_open",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f8935376f5e49869fd2cf4e4a6f40d88498a3cc4cf8f13edfdf015bf4945adff",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:8653",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:8653"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.generator",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5f45560abfcfaf29c673940dacbc562cf85014eeed72a266aee9bf1ccbbdbceb",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:6444",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:6444"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.generator_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4ce8c89818adb3b275229ed20f0d67e298d227529de22f714cb51cb00d63a442",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:6662",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:6662"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.generator_val",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "077246a13396f16fd8b1ed2689e41f879ecff3aabdb0649551011faedad1799d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:6567",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:6567"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.generators_adjoin",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3262f39e39137553f3932728fa991a47a82abb8e2aeb95ad22196aeaeeb45b7c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:344",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:344"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.generators_adjoin_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8c7aa8305ffb0bddd245b0d85c4f35c9f36cc9dde6013ee998363c9fcd649c33",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:980",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:980"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.gradedMonoid",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4a83d2580e5f7c636ae9d770397ac85f23f1cc97badf0cb30ecdbdf584d2995a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:3952",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:3952"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.grading",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "71b1ae2a1d5b8268435dca2b0f40830f1813ee6909fbdaa783cafb0351b1afe1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:4277",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:4277"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.iSup_generator_basicOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9ed093ca9bffeead786807ea89b83692b5039e098cdfa1bf1fcc2ebfa8497d70",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:1549",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:1549"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.instFiniteTypeSubtypePolynomialMemSubalgebraReesAlgebraSubmodulePieceOfNatNatOfIsNoetherianRing",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6d861c182d3c82c7d71504a1a549a7497ffb194a367a02eb9bc680a14f94422e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:5782",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:5782"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.instIsScalarTowerSubtypePolynomialMemSubalgebraReesAlgebraSubmodulePieceOfNatNat",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "df5c9af6af024773e7f899c46b189fcfb9e9b1e3dbe57565e1cf2306fde10560",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:5620",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:5620"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.invertible_unique",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AffineBlowupUniversal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "346dcb47fee744866bcd114088c691ea0113d682e1b28ca25bcafa52e24caa18",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AffineBlowupUniversal:934",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AffineBlowupUniversal:934"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.local_lift",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AffineBlowupUniversal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6fbd648a894a81516f90d8a7a6386f53ec3d16200556a0e495b987d357535aeb",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AffineBlowupUniversal:1615",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AffineBlowupUniversal:1615"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.map_ideal_principal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bc3b79f511a605ef80ce32894b072aa408aba93396ad1092846e4d3b3447ad82",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:10894",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:10894"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.mem_piece",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4153900075c8fe406c1e98cb4f85f6c49144fe5bcbeba12624bbe30b6eff223c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:698",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:698"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.piece",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "08d53696c6c5877142aae051f3bb724f874818c1882ac2f7a28b8eb492e35221",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:272",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:272"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.piece_coeff_ne",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "57122a7b9909bb398df6be7514f7b4f12affb4963366fd5d05b27868e236d667",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:2105",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:2105"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a23ff5fdef52c2bf7cbf385b4e767a63caa1d4788ccd85395362a776a17aefe2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:5622",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:5622"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.principalLocalization_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b6665f8d9ba35e26c4edc5d092a2d4bcfac3a916492f90290e0d2a5559852445",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:3830",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:3830"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.principalMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0974f4f7b2b026f5891aca6172f6fc4445d113824421936f50bbd77d72cca58d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:4045",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:4045"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.principalMap_base",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "49905e889e5ed5f4ff375feb63e6ea0b0195002c1d2a6547277dfa0d9fc8f606",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:5310",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:5310"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.principalMap_generator",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c798346e6d3480f2d4b68f93cf61f4808edfde109fdad6e0af353514dec92269",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:5524",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:5524"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.principalMap_irrelevant",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "46da5d3e4223c78025a852848549ae66a7f67956e3f17c71195408dd087f779b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:5761",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:5761"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.principalMap_spec",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c9959a1291a90e01a8d3d4f207f47302bceaacf9dd27f3a1f072b7a49b7666ce",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:5080",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:5080"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.principalScheme",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d99f287d707e9aef45f05a950321d56bcf3bf4a3a5142a7e2e19905a90269623",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:6442",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:6442"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.principalScheme_preimage",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "758ea981465e1a911e117aa4fbf68a1d8e89e4ac3fead04ef516155214b030a4",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:7891",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:7891"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.principalScheme_projection",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bd456ab5c8b1295f45bc6fa9c16553f8f111aac606aaa7be47465090c31daeab",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:6600",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:6600"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.principalScheme_projection_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "296a8b8e913d22300ed7418c70f091b8a53fa6f0be1652a1b81da985b36ecf8a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:6600",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:6600"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.principalToLocalization",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a7a5fa4b7585a38681e97cd179805315a9c008d7b27cd522699fd5b52ccc0a12",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:1839",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:1839"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.principalToLocalization_base",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a97071a11e4e219f17c46cd73b6712babe4facc146ffa82f7cbde46418d08f16",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:2064",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:2064"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.principalToLocalization_generator",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bca39e6b2c1ff240948a7b7fe252065231356954942ed22f9cf2a7b1e0b8327f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:2270",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:2270"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.principalToLocalization_range",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ebb0c4a8f8463c31f4a574f7ca3d3e832bbb0a0906590cd5e30aea5ac41e8f50",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:2984",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:2984"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.principal_basicOpen_unit_ideal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0c8c446d145053e348368e6f3efc7812c7ca732ff395ac207269773044222a7e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:9821",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:9821"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.principal_unique",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "adfae9861682d5a4f28b6ff96adbac42e22379c47b6847c769f71537f63e7fba",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:10372",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:10372"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.projection",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a25faf5d1ed6c3a45d178505fe920eccd3dc0acaabac5f8d972bd147443f76c5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:5496",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:5496"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.projection_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fad80e54c52071626a439ea35034577b8ea3348c9efa4a7338f0453a7adf3a20",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:3563",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:3563"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.projection_preimage",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "896499c9c2044ae36df83a3b070ee4b4e2d1b1697d9dc2ec576321850c837932",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:3864",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:3864"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.projection_preimage_le_chart",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a4bd8871b957fd84ce5e9b51a62cc0e2920f165a3cc5ea60673dffacec71817e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:4382",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:4382"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.projection_proper",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9e149cc93710b5ac701223e9bf298ea5dc2aa529a13811d491c0487405c42c77",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:5949",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:5949"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.projection_separated",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a6d8e8e2935527400e6295d4932944684e05f71da9714d6fac9edaef32225be4",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:3296",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:3296"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.ratio",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a4997a3394758124b013af02b80a43e267e3092c29dd5246da99c374be3746bb",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:10133",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:10133"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.recompose_components",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "10d25cef803405bc9547d08ba92dae49e761c4cd255cfb71fd00b77b5fda9f8d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:2751",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:2751"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.relative_affine_section_cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesRelativeSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d45a390d296e14c4c2ed809546fe3bfe8e083500cceb72a80f175d218556aa7a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesRelativeSections:7244",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesRelativeSections:7244"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.relative_generator_section",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesRelativeSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ba3aba182a27df01684da27ed1ac9dd96ad1fbe6f50a9cbf25669bbb18adda00",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesRelativeSections:2504",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesRelativeSections:2504"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.relative_generator_section_open",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesRelativeSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ea53e2a53ec4222c334acb05cfdc2abbfb7eaa9c1bea9e23d7d7bb24f8fac814",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesRelativeSections:3959",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesRelativeSections:3959"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.zeroEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e6e9cbc89c28a6190575d9932092272096a526ba1623ce85cd84d9890f6f175f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:4819",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:4819"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.zeroIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d2b6ebec0720888292e90e6618a83d9b891c423a18b8f6dfd602b915a8420994",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:5394",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:5394"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.RestrictionCohomology.freeOpenEquiv_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0cbd0d6d18ba33e774ca00fef4e91ef9087fbaf376fa5185eb09430acf35cebf",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:47059",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:47059"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.RestrictionCohomology.hasExtScheme",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "673339367c3582b1e4c79b15a30bf1bcef9fabd466c44e658606a5ddab0cf325",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:46965",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:46965"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.RestrictionCohomology.restrictionGenerator",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bd8758a386c74bbd8a2c7d7a0ce6b1cc8d95b3c14e84c250724e7341614dbad6",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:48886",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:48886"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_043.jsonl"
