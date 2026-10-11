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
      sourceName := "OAI.PiExponentSeshadri.Projective.CoordinateAtlas.scalars",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a98f09e09ed154c24d8022c19de016211ae8af76e0e166882483e37d79999e4b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.PolyChart",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a6f0030b805ca1c839cf7a176dfcc69bed7aa06526ea7ecde82b67f409108533",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:1102"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.PolyGrade",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "478388b9fdaa30f83c7d511952b9340f7c24dd4e6ae2f617c002f801f2191897",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:935"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.affine_evaluation_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2b91c89edf68fd8510a855218805b4bdbd1780087a7f3dc624da246496f487c3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts:1140"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.appLE_restrict_comm",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c573df0980dc7e170641f2a7ce5663533e262a10b7ac6dddc84cb7c0b6fad082",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality:1235"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.atlasOfFramedSections",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ecd88f4b343b6ab985a5d98c702398dbead38086f7efc8771618dc1e35d2f2c1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:11714"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.awayToSection_pullback_open",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e245a8131af56e69d998446c4478421ef46da30e80e09ea1fc95aa4efb245ef0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore:2651"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.awayToSection_pullback_top",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e5204c7b28256ea3fe4aa85aa5066d538db561d793567f0cbd59f734457d9d6c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore:1946"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.away_chart_appLE_top",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "368679a22a7952189ab9ce0d3cbd58b534f2427f0633cbcca61440e41274dc59",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore:736"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.away_chart_preimage_self",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "253c4b885d69b1004db4fb28063f31c631975c9b7bb5026558235ebf53d999b0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore:459"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.boolChartUnique",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "42d92650312701b156a9d843f8864037a3176ff1ec43409ca87de9d9023e9f5b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts:5446"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.chartConstants",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "08204c2a834d414198d43a933c14135030d8e1fb74acc4f263beaaba53978138",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:1223"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.chartCoordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "79efb580b74f95a5fa7fa2538a0c8677c1b87b0132665a594a7fbf92b347d115",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:1558"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.chartFinitePolynomialRingEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartOverlaps",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "61ab2a74f0fabdf3577a95f84a5eb48e264e55ccc1f66f73942ed08643ef27a0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartOverlaps",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartOverlaps:4310"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.chartFinitePolynomialRingEquiv_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d3b55be49025ffa9235e363b8f4ee70a7b7119d60d43da04bc917a7540f45cf2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore:6072"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.chartFinitePolynomialRingEquiv_restrict_poly",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1cf4622e0832ce6052f45d57731e01161bb607f7fe0398b2d585e959ce9d1841",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore:6532"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.chartFiniteSectionRingEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartOverlaps",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ff553c8e48d07f3f6d77e7f75c464cb1ef19b208e2e3cb4d276ac703369f4386",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartOverlaps",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartOverlaps:3131"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.chartFiniteSectionRingEquiv_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "28ea11d7af923dc3bf92ac288450a62ca385739e8509ce84ffeffbacc6847c93",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore:4106"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.chartOpenAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "883b801a8856ffb1104bcf380ad0289a02ed959bc99d428483e95f1e58d8e5e8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore:2408"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.chartToPoly",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "edfdc4ef4e8f3a577c3ebf7e5de224e1c7d5aef5599232d0cf58162b5721a7a3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:1963"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.chartToPoly_comp_polyToChart",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2e2436e8994447707e6670469e1934d33aaa11411b52361b5363301ab49d0cf2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:3106"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.chartToPoly_constants",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "870ffd3d081fab2056276fffe4a3d979a43c2a883d52918e26ee56f3f5845c46",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:2706"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.chartToPoly_coordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "21bd21c03da54a39ff26e28a3a488ecb674de93937c866017d918cdaaa218cef",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:2889"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.chartToPoly_mk",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fa53a94b74671d7dd6f118189f00e4e19f1f4323a3a056737b9ca6506231191e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:2283"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.chartVariableOverlapRingEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartOverlaps",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "10989422dda15bf3d97094c498ca57209234ac4c6c475933725d1222bd035099",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartOverlaps",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartOverlaps:5151"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.chartVariableOverlapRingEquiv_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fd375bb7814197199d2b534f522013c3b50d519490b898f067b1a2a90d5bb914",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturality",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturality:1207"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.chart_dehomogenize_val",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7c6b4e10e9ef5364b8a30edc5b5b703eddeb1b83b05c8ecba2297c4f47874d86",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:4348"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.chart_val_constants",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6d204387b9da5349f1ec0d3698f828e3cf2a60b36c7cf3bf9f185570b3266f01",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:3833"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.chart_val_coordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1524e5c5d5fa2d0f6571fa272e3748e71f24cf1b7c2ddae2650863b585239045",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:4079"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.chart_val_mk",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fc7ec0d92afa83d43e2a5f472f04be573c6d933d2a9fa2b361d4e38b42abc7ed",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:3353"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coefficient_postcomp",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e18b03885b6897d09fc8b2f9c8fcc0112cfa9c8757dbd2c0bf0fb10ba2082865",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections:7438"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateChartMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateChartMap",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5c59db06f5c7d0083ad8805337233fe5fd10e4bb231df1ae55a4a37e6e860cba",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateChartMap",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateChartMap:577"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateChartMap_factor",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateChartMap",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b469940713d64c718571d024a4d9ff809d76b1d62bec52a07a1d2d8df0993928",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateChartMap",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateChartMap:867"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateChartMap_ratio",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateChartMap",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "13e1b11232856baaa210c5197073b63e258a221a2a936e05dbe9c666ac818496",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateChartMap",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateChartMap:1185"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFiniteOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0cd3dbb6bb556d5c6532e54157180374d1a9fc490bebbae86af63a522e9b2fc9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections:1113"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFiniteOpen_eq_preimage",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "85629b12ea767ae892855b74a3fc32cab1e86a4b3479c8aac8bd000e9821e415",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections:1457"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFiniteRingEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "548d52cd148338a89010a3534132b2ed461d1baf4fc4ebd2b540f0608679dcf4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections:2121"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFiniteRingEquiv_appLE",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0576b53da788d45a3fd91246f5cf8697c6913a034d77f67367b70b60900a2bfe",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality:4040"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFiniteRingEquiv_constant",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eb171c5f444462e58644a424c7344fc92b96fc4c5743337ad79a84c9f5c1b007",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues:1996"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFiniteRingEquiv_coordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "166d9a35d510ff449b728a8bed31b7480321543cd93c045b45c7cb103914a92d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues:1388"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFiniteRingEquiv_cross_ratio_full",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "71e2d537660a03938fdc976affcb2653057ab17aeda340f4c4c641d9d0e23add",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeTransitions",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeTransitions:707"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFiniteRingEquiv_ratio",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "64d17151b2e2473a244134a41bb823a22224f3a1515c49066975a2c41c020e8f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateTransitions",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateTransitions:886"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFiniteRingEquiv_ratio_full",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3f862452d0e4327a69660dae25c5b871f793bea349ff84c39c369163380fca6d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateTransitions",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateTransitions:2151"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFiniteRingEquiv_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "290102b4daf9c8fc6409fc38e7df0fac9e5f9ce0f7d2eb6fd62f0da4bff3964a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality:4861"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFiniteRingEquiv_restrict_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0f16a49e63b0129743d5bc4ab35b9140d3ebd2859ccb142c4f200efa52eceef9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues:824"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFiniteRingEquiv_symm_X",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "68ead3bd7f5dc201e1f06c22c24616970e883fae8800308d3438899b4f58a9c2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues:3160"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFiniteRingEquiv_symm_constant",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3736dd29b7f0fa16a93514a25c2d021210290169eebccee0be33cb755aafa65e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues:2697"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFiniteTransition",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "93a4a45ef907be87a6b9fe9f918f54f2194b4a66a444527e4eb218b6fb145f90",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues:3874"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFiniteTransition_X",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "579a70b323e278a3e18588045af2260b3d2c0572a10c2058ed4c73a319961827",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateTransitions",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateTransitions:1294"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFiniteTransition_X_full",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0568b3cb620308ec76ede112993c4de102c8a145036729654351aab93a0661dd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateTransitions",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateTransitions:2747"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFiniteTransition_constant",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "69f1a45cd96466aa9d4a63d62b41933c6921264c0bf31911c98998a00f0827e7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues:4356"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFiniteTransition_full",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d2ef420d7f31c7665331595550a02fecdd8fa5ff069b4a853517b20155288b14",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateTransitions",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateTransitions:4058"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFramedLaurentPresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1c905faab05b9c914f641a9f940d188d6622559a36ee403a455c1672197425c5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech:4382"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFramedOverlap",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fb6e0ab1d01f47ea7cb0f4486296026febe3957665c58088ba617b008bad6829",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech:1060"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFramedOverlap_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "507423267f357ecc922ae7ea6e6bb201fa69bf60b728637a51755ab69b3a951b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech:1339"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFramedOverlap_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a09f7a1f75075bdb965d5db41de8439ebc3e12fe8eba146dc37b2d1f6aacfd15",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech:1550"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFramedOverlap_smul",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0da4f64f39d4b9fbdd0c4823f5658bb9561ea4f0cec678f3b390316a8e98f25c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars:3914"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFramedOverlap_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3ff35e34abdd9e2096b0f0f443b0cda4118b01d9d74d67fce601dc7795b5cf8e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech:1876"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFramedTuple",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dd64bec3a6f6b1578efa0908ba4272c94bc57fa83f0677947a4bcdb804717be3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech:2250"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFramedTuple_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "420d06a52d80c9a12d1b71183b38973302261c80980e9270cb05e13741e92a5d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech:2633"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFramedTuple_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ea65032366a37a8c87e3a49c65e399215308193a054d8cf51c1ebb61f8b1a60a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech:2982"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFramedTuple_smul",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0445e83ac44dc2acacd4f8f2f746b36405f99b3acc22f2efc1945e274701a9f3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars:4989"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFramedTuple_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6a39048f59130595913a00bb8db6c622b3d833766a2baedaabe6f4a1ae9ccc07",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech:3655"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateLineBundlePullbackIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinatePullback",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3d1d752e59478755a70657d8dbbf340d0d596eac2fc61dbda98f8b2a5e636dca",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinatePullback",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinatePullback:3036"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateNegativeFrameFactor_full",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9530589fb9aec0dce2804603c7c1f0c78eb605e53c69dd2d23585b5a97c3370b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeTransitions",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeTransitions:1793"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateNegativeLaurent_change",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "02c4ff194c992fd0872126ba7df84f7a03ae9108c33bb6991100ad5b1d18d362",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeTransitions",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeTransitions:2435"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatePowerFrame_hom_change",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a01335fc53238d331b6e56b7a439c2bea4c7be058716064205e8558466a0a487",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios:3561"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatePowerFrame_hom_change_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e55d56a3dec46c86593340d31f6bea86d2a21f8abac26baaacf2313cce32484d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios:6183"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatePowerFrame_hom_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b6f70544629ea989c1b23a8c0d20c1543e599c7e31dcf4a07c0acf8cb56ee909",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios:4755"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatePowerOverlap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "252da5b6365eb18c767424cc481393d707919c39e354981165bb24b05be3c995",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections:2540"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatePowerOverlap_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c0343653f58355b9e49bb7c5273654daac7fabe76a9fee933bd852de268ecf8a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections:2976"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatePowerOverlap_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3f8e731c98ab95f4128751d047b000aa1858a7f93891ee170ac95cdc9ab29d10",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections:3191"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatePowerOverlap_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateOverlapNaturality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6d0f605950ce8030c093f6ded4faebe77b6044933521fbf09d0fdb1af8ee2d23",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateOverlapNaturality",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateOverlapNaturality:798"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatePowerOverlap_surjective_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "02554aa70acb7cc914c5c1e36a746fe6d0274d5663aef8dca72dca95c06f5e63",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections:3539"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatePowerVertex",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "66ff87be710d748415d45f5279a38f18bfb92c2ade6c3b48323f7bc60707baba",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections:4601"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatePullbackFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinatePullback",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "227e237c5ac4df93d0012fa1171a0a488fb75f3c084ae3cd0bee6e793e18de71",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinatePullback",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinatePullback:1021"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatePullbackFrame_coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinatePullback",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8bd6c646c12b74cfcdc4cd067e77a7270e46747cf1ba1decc0ea719c52fadbbe",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinatePullback",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinatePullback:1539"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatePullbackIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinatePullback",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9fc97094347d4b0ac9065740deea22c1f93a8d759c4f3b0c4c88670866a628f0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinatePullback",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinatePullback:2660"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatePullbackModule",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinatePullback",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8bb7b393b662ffea77c591b7def70df0fa7b01b128ad686ae9d8880615ce2fa2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinatePullback",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinatePullback:669"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatePullbackSection",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinatePullback",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "62c68afb7423ea7095118669273a3d2c34c79c440128dbd7d8dd50c2a77668ef",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinatePullback",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinatePullback:843"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateRatioOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "013df5fb77f6c3fa3e076bda4c109d00929c159546a42f8421aba4deb026d9f2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios:535"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateRatioOn_change",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "17f3aa7dc7e39446e51b533b4a9358b42cbdfb5e151e555638901bf6c603a595",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios:1378"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateRatioOn_eq_coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "832389f993c0eec8909b06d6090a92f110ba8e93989d48c1011020b799e3aea0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios:825"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateRatioOn_reciprocal",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f9dc44f87bd72e60033b6da35d3da8600a72d8b6c540085f63b44722a0be9c75",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios:1900"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateRatioOn_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "431683d214b993940c01d20114e98735a87f15a63f4a9beb52ad60b5949b3666",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios:2200"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateRatioOn_self",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b360f9c4970fc5d61e2a897190711ab049b4b853574e8b257a2c081c7aac9783",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios:1159"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateSectionChartIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6d1c55336fb773f27e8d5cf0f5b216693269e7b088661541e264b8e62bd3bd0e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections:1774"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateSectionChartIso_factor",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3dc2f19d86dbf1b8aec1c8c5f14744a49b9783131734ab4fbfbc4146c6f5d355",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality:2095"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateSectionChartIso_hom_away",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c4e65125422e484cc692c11eda3a6543b34fba40ccc2927029eae29429c24a75",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections:2161"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateSectionChartIso_pullback",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d3ee8ac6224fb8218ff284ed8a8458767304cf97a6380b9b9049a6a63c2b06bf",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality:2734"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateSectionRingEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cad279d68b68eb03328ce9cba0e1d43192ed678053c66d7758946e6d9ecd4ba3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections:2611"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateSectionRingEquiv_constant",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateConstants",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "361eb3026a6972bc26fc98a9b972cafc4e28fe02c09cc4b01d6792744e657e95",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateConstants",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateConstants:4132"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateSectionRingEquiv_coordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4b067a4582c42014539e1bb143f5dc2eef7bf005770cd80eddf4a4151a956d34",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections:2924"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateSectionRingEquiv_symm",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f765e866669d05270453f523a2cae271a56df2f2faaf220125fb6f60e23f68d0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality:3467"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateSectionRingEquiv_symm_constant",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateConstants",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6b8067bcb4ba9b06e55a1663a5655dce5c0d04275b0dd670ae52b944c057109f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateConstants",
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
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartOverlaps",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartOverlaps:846"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinate_finset_preimage",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartOverlaps",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0f8e3554a88ed967fe4e1596f45bd2d2a10a7e635ada0cb05e0dc88b9a6b40e4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartOverlaps",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartOverlaps:2586"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatesMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "26b001e45d193ed7b14619ce6b7d106e22921c67c4a54d721b62febf4ea7333b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:6400"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatesMap_congr",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedAtlas",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0b0695b22669b61995f9a3f6f672b5d5d2b30be5d9590354a9f2035cff421b4a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedAtlas",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedAtlas:387"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatesMap_natural",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4b7874449f6688532323512535c2988dd94ca2cea74ebedd2150c61c5422c555",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:6978"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatesMap_natural_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5671001d91dc4699ba1f0a5e159224a2c01a9945353dcf9359e54160fbecfae7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:6978"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatesMap_over",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9b97ae3d0974941c16963fe298caf023662753006b5d23997559950a8092643f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:6631"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatesMap_over_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7644cc285cfe9e42a376c43b0b6dea3e9d9162a191adedf81c14fb6c8483ef5f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:6631"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatesMap_preimage",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "53974810bb71553427bd8f97e4aeea1cc33a254a8edcf6beb0598b6f73d4c7ed",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:8977"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatesMap_pullback_constant",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateConstants",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "01c4250dfe6a83744e19cf18f7acb2f83397429c09f77f45175ea73cd6d9ff91",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateConstants",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateConstants:1242"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatesMap_pullback_coordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateValues",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dd4ac194c13f7f90d7741119e6dc358a63c35d427240e4a015d7137aa5ceab9e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateValues",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateValues:896"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatesMap_scale",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "43bc0f8ff8608c58a028600b240db36301009e97abab58cccd1f312bf0246207",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:7571"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinates_X_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "70db76fdc3cb6e054b8d02645357000568ece31805bf5ebff7f37162cb8bab73",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:6287"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinates_eval_natural",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a23dc6044df09520f0761e4d915912934a096c6d7ad6545e559f4a39be7a0093",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:6716"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.dehomogenize",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b627f1203bd4976e05542fa5c34d2f8b810fbaadc7cfe5bbaea7aec6475d717e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:1700"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.dehomogenize_X_self",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7f03970097758d20d06212363102eeee77209abee4e6d042074a40dfb5c68fc1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:1848"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.evalAway",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6a664ff063f3e30b8e238038f864e3f0c92c08bbbf6837461fb0bc72226a1e8e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:453"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.evalAway_constants",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateConstants",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d7ca05d46dc2ff47e2fc464dddf71f0f082e8c1522825960fa4c730c281e2aee",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateConstants",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateConstants:413"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.evalAway_constants_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5eb3b2b49688dcf9f9749543e3c6fc5d5e59cc0b99456bdf8db2e4ad02f562f8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:5710"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.evalAway_coordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateValues",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "427ea52f74625ab6976ddca83bbf0c688b1d62902e916815166ab09a3d9e468e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateValues",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateValues:337"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.evalAway_mk_clear",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "17b3cbe33e906a9a41cd2dc73a48361fecd395bf2d7cf29184fcda57600999d1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:2156"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.evalAway_natural",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a89fdc37b5f89912da5ae4a6c0f1f108be6532ea4ca05a644d706a1f8e1454aa",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:1583"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.evalAway_scale",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "78d658d7c571f076d3621625850e4ab0d92b7e98fe16894ba3bdc65902fd9294",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:2685"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.evalAway_transition",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "466acf83441a41388148b6169f0807592956fc7b9c741b184e5f83b5960d1bd1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:784"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.evalAway_val",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c145259bd28591785b6b7d2258c33af031a036044ef5ad2202d9f0efde5acdef",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:646"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.finite_pencil_chart",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "89fbd5219c2fa8b5e66cea35b3dd5e738dfc2340e8e13f958bbead3ed38ae9c0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts:5640"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.finite_sectionsMorphism_chart",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "04b5106c297926088a420825db03a7a9dbc7ae9e441ce5290d4c267a604fed6b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts:3213"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.framedHomCoefficientsEquiv_change",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "83d8e3c47ebe6cf0c2b41640d506be24a0ebdcd54128fca9bdaddc66802cc86d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios:2593"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.framedHomCoefficientsEquiv_eq_of_normalized",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "36cabd3d90b7ad2b30e26938311aa888ec520f450a90c684673b17375e674ec7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios:4237"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.framedSectionsMorphism",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aa45472d4cfd674aca32d4958197c1ca8b950d9bde08452fce5033b87d9a6215",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections:707"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_closed",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cbdec25bf4129353c3a905e86099899ba711192b636ddbb401ac84566526e55f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections:2841"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8d1ca086038f147e9165ae7bf2cae9d6ad1934e8e25fe0a292e334a88c96a23b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections:4724"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_030.jsonl"
