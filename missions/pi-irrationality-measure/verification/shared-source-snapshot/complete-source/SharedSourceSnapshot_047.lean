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
      sourceName := "_private.OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart.0.OAI.PiExponent.ReesFrozenChart.coordinateInv",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "59e175e7f8508cd454b9476711383f3043c49143314f1a240d158deb2ddd521b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart:1110",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart:1110"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart.0.OAI.PiExponent.ReesFrozenChart.coordinateSpec_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8e113b87ce695abaa39c8081b5e1c91211e17905963b307c2da9307befee1aa3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart:1621",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart:1621"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart.0.OAI.PiExponent.ReesProductPowerSections.instIsOpenImmersionFChartCover",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "955c95fd9066e86445583fa3de13222d483808e465ef36bb819b950b877241cb",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart:1847",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart:1847"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Ampleness.ReesRelativeSections.0.OAI.PiExponentSeshadri.ReesGrading.map_comp_through",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesRelativeSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e41eb9a6c7f5e4896656b6b44bccb18b95e722c934fbb4471b96425c35993276",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesRelativeSections:1961",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesRelativeSections:1961"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Ampleness.ReesRelativeSections.0.OAI.PiExponentSeshadri.ReesGrading.mono_inv_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesRelativeSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "249a64412eaf7f3e3a41e55bb4f81c45370b227773c8e0ade9d7650e2fadb825",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesRelativeSections:1786",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesRelativeSections:1786"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Ampleness.ReesSectionInclusion.0.OAI.PiExponent.ReesSectionInclusion.chartMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesSectionInclusion",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6e7a18606ccaed5b5665b5c1f64ba96012db5ec389d0e522f195b8e8ad7871a4",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesSectionInclusion:962",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesSectionInclusion:962"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Ampleness.ReesSectionInclusion.0.OAI.PiExponent.ReesSectionInclusion.chartOpenImmersion",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesSectionInclusion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "848c13b126f8db9f0d72c16973b9a821abb2382e26cbf75ce4b018707d94ad16",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesSectionInclusion:1144",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesSectionInclusion:1144"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Ampleness.ReesSectionInclusion.0.OAI.PiExponent.ReesSectionInclusion.transported_augmentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesSectionInclusion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1a3fde2622847f6329cb0965c657136eeaf91e7e0150e755ba9e0044d1327968",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesSectionInclusion:1317",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesSectionInclusion:1317"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Ampleness.ReesSheafCanonicalValue.0.OAI.PiExponent.ReesSheafCechRecovery.chartMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesSheafCanonicalValue",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e480762d462723f93bdf9c9068f9837ee6d26e2493262baac3a7587998b5692e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesSheafCanonicalValue:848",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesSheafCanonicalValue:848"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Ampleness.ReesSheafCanonicalValue.0.OAI.PiExponent.ReesSheafCechRecovery.chartOpenImmersion",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesSheafCanonicalValue",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "579a0509bb8f817287a94eabad7c93590bd55a005f390e77b02d74e1be53ce93",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesSheafCanonicalValue:1030",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesSheafCanonicalValue:1030"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Approximation.CanonicalAffineRecovery.0.OAI.PiExponent.CanonicalAffineRecovery.bijective_iff_of_square",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CanonicalAffineRecovery",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "36efa11f7ef9673406628bc094066bb37bfb2ee1b29824f7d25ef194172490e5",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CanonicalAffineRecovery:557",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CanonicalAffineRecovery:557"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer.0.OAI.PiExponent.ClosedImmersionSerreTransfer.schemeUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0844faf36b4b67df5a2d0deea10e16e922e2d1fbdfee0d90652eb83135e0a683",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer:404",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer:404"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardAffine.0.OAI.PiExponent.ClosedPushforwardAffine.transportPresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardAffine",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8e43e4ea49ac095ba5643662c92dc415252524a4eda3f03df956d45770f3ba41",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardAffine:404",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardAffine:404"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardCoherent.0.OAI.PiExponentSeshadri.ClosedPushforward.presentation_transport",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardCoherent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5b5e5ee4b08f2771ee22ac6f812069cfa754c85b4f973acbd91340bc243170de",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardCoherent:3628",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardCoherent:3628"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Approximation.CoherentCokernels.0.OAI.PiExponent.CoherentCokernels.presentationOfIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentCokernels",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "52d1adc8dfbabfb1e74036ee0a6c22db9283c416e9298eafd209650d9e2b7842",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentCokernels:331",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentCokernels:331"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation.0.OAI.PiExponentSeshadri.Geometry.modulePresheafTensorRestrict_natural_aux",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "17738fe6825a180d8176ed527b3d6d398ce9556a0b827eb280ab576a9766c277",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:6899",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:6899"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation.0.OAI.PiExponentSeshadri.Geometry.tensorRestrict_natural",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c70e624057237b0d0413ab5a6fd04ae2fd3fdafdb426f1bdfd38bf39da1f02ca",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:6100",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:6100"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Approximation.CompositePullbackFrame.0.OAI.PiExponent.CompositePullbackFrame.mapIso_trans_inv_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CompositePullbackFrame",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f5e983e4efd9a75c0d3835f6bfa299e663ccf57470a6d29d464aa97ab7aed4c2",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CompositePullbackFrame:361",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CompositePullbackFrame:361"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Approximation.CompositePullbackFrame.0.OAI.PiExponent.CompositePullbackFrame.map_comp_iso_inv",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CompositePullbackFrame",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d8935bf4262366a6a4703a405903807365370630d0d25e3ab462bfcae53027dc",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CompositePullbackFrame:700",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CompositePullbackFrame:700"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover.0.OAI.PiExponent.GeneratorsSectionCover.epi_iso_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "38654ca1200d49917596147284fa280a938aff3e96e51dca5708c0aa53c6ea50",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover:498",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover:498"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover.0.OAI.PiExponent.GeneratorsSectionCover.schemeFree",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3a2d3e6b0d8bde0bec8196518c2cc4d02ad9f6c1250fdaddecd4f4eacc993e26",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover:674",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover:674"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover.0.OAI.PiExponent.GeneratorsSectionCover.schemeInclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7e01df56fed37ed2246deaca73525beb3bbb158799311c7693f4c868c43ad43e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover:773",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover:773"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Approximation.InverseFrameRestriction.0.OAI.PiExponent.InverseFrames.restrictionMap_cycle",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrameRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "058a4dddc8c9bd43224f81c0b1f3b1931286c2c4e1b51e8d89db36fc88c16836",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrameRestriction:2713",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrameRestriction:2713"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Approximation.ModulePullbackCoherent.0.OAI.PiExponentSeshadri.Geometry.presentationOfIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ModulePullbackCoherent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "35f6c5128ba987c7b8f257139b497f4296014cb9bbfe1aef2b3b8f250b674399",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ModulePullbackCoherent:342",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ModulePullbackCoherent:342"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections.0.OAI.PiExponent.GeometrySupport.PushforwardOpenSections.schemeFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fac25b1df2bc4b51efb4d480f7af5a0e0910f633b2624ae8d461cdb39cd23c31",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections:409",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections:409"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison.0.OAI.PiExponent.GeometrySupport.PushforwardOpenSections.schemeFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7b2bfa90ec69ade27586842ca4af39fdd136a78dfacee3d1683ad1325bd53797",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison:315",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison:315"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Approximation.RegularComponentSection.0.OAI.PiExponent.CurveCycle.sectionGerm_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RegularComponentSection",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5eb5739292a777239d143f7475693624c692e10b36414920c64c53a54e9f4543",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RegularComponentSection:1766",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RegularComponentSection:1766"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice.0.OAI.PiExponent.NumericalAmpleness.iso_inv_map_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c5968404b9c380d869acdd97c41091ee8b1dd217e6da9fae4161c908b0568582",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice:3196",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice:3196"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Approximation.SerreAssembly.0.OAI.PiExponent.GeometrySupport.SerreAssembly.schemeUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SerreAssembly",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "705da5e183d412f09d961afd0f9e399eb51df0b1f52b308190681e9663d3d705",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SerreAssembly:442",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SerreAssembly:442"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Approximation.TensorPure.0.OAI.PiExponentSeshadri.TensorPure.sectionModule",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c673903c7bdb2df92335a58a3c08212fb769c304b75752d7e8e2a87bc7b889b9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:326",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:326"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Approximation.TwistPresentations.0.OAI.PiExponent.GeometrySupport.TwistPresentations.schemeUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "171be4bb8c831f1d388d810afbe69cdf2eada84a0f808805cb430fbc751ca041",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations:374",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations:374"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair.0.OAI.PiExponent.NumericalAmpleness.CartierEulerPair.iso_middle_comm",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d00e6d7bfd526fb91978d17dac9c9167833e59e0f6b0e63cad55f4d184431793",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair:3435",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair:3435"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.CartierMixedEuler.0.OAI.PiExponent.NumericalAmpleness.framed_map",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CartierMixedEuler",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6d42a214a86d30464069631ee6128ffe54b1299c0e83394052dd6521bf740b08",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CartierMixedEuler:444",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CartierMixedEuler:444"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite.0.OAI.PiExponent.GeometrySupport.CechExtFinite.schemeFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7fc9703d08cbf36f1e4be8d68b3ff133bc544184d35314a68ebd43495053ef28",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:609",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:609"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.freeOpenHomAddCommGroup",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a0fab9aca4b6e7c7b7d56da18cf669e029753b7bda544d4577e098c96b52dc04",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:566",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:566"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.schemeFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4224c3b28974312e36fb3c35530b56b31e1b07c9bb09cf6225b5fc4cee0c3f95",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:359",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:359"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.schemeUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d98680d7ddf314cebe215b43eeddb2792bf80f506adefce64b1168ed3f42f248",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:467",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:467"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.CechHigher.0.OAI.PiExponent.GeometrySupport.CechHigher.scalar_differential_zero_degree",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "359b99620228080dd25f1de75ee615b7a1f56eda0c598b26aa0487c95d0691d5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:10473",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:10473"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.CechHigher.0.OAI.PiExponent.GeometrySupport.CechHigher.schemeFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9103a1ab97ce8db51030e874c028284e1ccc157bba7a2578ecd268979b230978",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:17833",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:17833"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.CechLinear.0.OAI.PiExponent.GeometrySupport.CechLinear.freeOpenHomAddCommGroup",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ff35d3ea1a19f87cce302c4d2758f022f4fc209fed13f2bfc0cb27ed2e04fb8b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:652",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:652"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.CechLinear.0.OAI.PiExponent.GeometrySupport.CechLinear.freeOpenHomModule",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9230c6f01b0777e00fcb8f6a9e823514abc263f7131f268fa9eb9c5122fe29cd",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:1212",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:1212"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.CechLinear.0.OAI.PiExponent.GeometrySupport.CechLinear.schemeFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f5f70d5136d3e3c2c971b379962a0b9871148ec05f3eb960a8035cbc739cd98f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:564",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:564"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.CechOneConverse.0.OAI.PiExponent.GeometrySupport.CechOneConverse.schemeFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechOneConverse",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6fdd5372f9808e2e94124786a2f0dfbb15571995650ff3e689fc92a488e7db10",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechOneConverse:2490",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechOneConverse:2490"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.CechOneConverse.0.OAI.PiExponent.GeometrySupport.CechOneConverse.schemeUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechOneConverse",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fb922e332b5e3e361b69d2d4353deb2f4fe1868274ee196912f901bcc6c15f6e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechOneConverse:2411",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechOneConverse:2411"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.CechZero.0.OAI.PiExponent.GeometrySupport.CechZero.schemeFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechZero",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cdcd4617fd74a74c270402cfec0e1fcd87a6f232c371d2dcaa7da63ddd321fef",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechZero:2541",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechZero:2541"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationCohomology.0.OAI.PiExponent.CurveNormalizationModel.parameterCurveUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4209b7d2bf521200a3f4455c0da8aedd35736086ed11f75d251406a2c5e0a4b6",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationCohomology:771",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationCohomology:771"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationEuler.0.OAI.PiExponent.CurveNormalizationDegree.finite_middle",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationEuler",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0dea22dcabd999e37c497e0cf16e79d9f1b6657c44017c4305ea0536c3f74496",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationEuler:1697",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationEuler:1697"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.EulerPolynomialDegree.0.OAI.PiExponent.NumericalAmpleness.difference_step",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerPolynomialDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c596e72f0663cca05127af7ab5c7bf8b3d461cc9128ff3fd49f938bbc97ed939",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerPolynomialDegree:1248",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerPolynomialDegree:1248"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.EulerSupportDimension.0.OAI.PiExponent.NumericalAmpleness.mono_comp_iso",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerSupportDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7d59eba2f2b43a68711a62fcbf7aa7ff47a9db1e7eb7a92f0167ffc20f6507c6",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerSupportDimension:1586",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerSupportDimension:1586"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.EulerSupportDimension.0.OAI.PiExponent.NumericalAmpleness.mono_iso_inv_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerSupportDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "803d719e9915e16e83c02cb057260d4ca6f12840c2c372376751ba44aa03bc0f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerSupportDimension:1770",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerSupportDimension:1770"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology.0.OAI.PiExponentSeshadri.AffineDenominators.schemeBasicOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "74b06c37034329c37988e8720a3a380e443ea20f0f9f7e45c8eb4dbd77d127a4",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:7585",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:7585"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology.0.OAI.PiExponentSeshadri.AffineDenominators.schemeBasicOpen_mul",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b3501e044bd495bc02811e0a518c288f6d723f5eb0f8d41f590e40319c017b3e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:7673",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:7673"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology.0.OAI.PiExponentSeshadri.AffineDenominators.schemeBasicOpen_mul_le_left",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a3fdf856d06fa640eb8ee03a6551892ce446ecfc6fda0633d60edfd636039f4b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:7831",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:7831"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology.0.OAI.PiExponentSeshadri.AffineDenominators.schemeBasicOpen_mul_le_right",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "db3ab1168b24247e248e0fdb2caf14197dd3e67b18e148ea20298df8883fc306",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:7985",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:7985"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology.0.OAI.PiExponentSeshadri.AffineDenominators.schemeIsSMulRegular",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ff8f2b5002c154695ea1b1279dd7d03b473b35d5ab6b3e739ee4b320673db570",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:8141",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:8141"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology.0.OAI.PiExponentSeshadri.schemeFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "17695b1d662e98281e1ae1d3f2d8bd191085034201af063e8f07f1722ec53bb4",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:30518",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:30518"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology.0.OAI.PiExponentSeshadri.schemeUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a18fd3a3d48c370e30c79643c3af78d2bb245d98eb43715bb6099fd4d348f3c6",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:724",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:724"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections.0.OAI.PiExponent.GeometrySupport.FreeCechSections.schemeFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "40340a8fd754445ffe3116a77dd0b3bdac953dfd0b4c8cd5ee88c71f857a4610",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:8740",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:8740"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite.0.OAI.PiExponent.GeometrySupport.LaurentCechFinite.freeOpenHomAddCommGroup",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f4581a8279368d5a46621186277009bab8ba0a788988c2ae8bc1d106e06158b1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:657",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:657"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite.0.OAI.PiExponent.GeometrySupport.LaurentCechFinite.schemeFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "50fa2fe73f9ff77fb8ee19a4d08d2a40886b1ba1b74077788248b4c2539ddcb5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:533",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:533"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.LaurentExtFinite.0.OAI.PiExponent.GeometrySupport.ActualLaurentExtFinite.freeOpenHomAddCommGroup",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LaurentExtFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fc235b0483087e4548c75822720e36a78f3fecfb59c17cea96b5ada8fcf5105f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LaurentExtFinite:664",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LaurentExtFinite:664"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.LaurentExtFinite.0.OAI.PiExponent.GeometrySupport.ActualLaurentExtFinite.schemeFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LaurentExtFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0002577504ab3d38c8567d900d35f978103e68a7391b27f2adc73f06f52e2a79",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LaurentExtFinite:540",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LaurentExtFinite:540"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.LocalIntersectionEulerFiltration.0.OAI.PiExponentJets.W28.LocalIntersection.finite_cross_add_to_integer",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LocalIntersectionEulerFiltration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3fdb795f30c2aabc80ad3c67115fc4f5f30d1f5eb77a51eb592fbf41a77ed631",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LocalIntersectionEulerFiltration:521",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LocalIntersectionEulerFiltration:521"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech.0.OAI.PiExponentSeshadri.Geometry.schemeFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d8e8a42982cd934bfde1ebb539a4d29fab6624bc390eb1ed1fa8243264b7b192",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech:2311",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech:2311"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech.0.OAI.PiExponentSeshadri.Geometry.schemeFreeOpenEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dbd8f67e9b966d105c42d60ca79d4f730dde9af0f2524538ced22961779a8e73",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech:2538",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech:2538"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech.0.OAI.PiExponentSeshadri.Geometry.schemeShortComplex",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "61194407becaf6e3d94dd9275b3a89f85251728a237e2123413c513e63634770",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech:2402",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech:2402"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections.0.OAI.PiExponentSeshadri.Geometry.freeOpenHomAddCommGroup",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "96bbb6b1d0cda2f642de4e1704adbc66d3b1b91db1a1d25242b1a34fbedd935c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:2289",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:2289"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections.0.OAI.PiExponentSeshadri.Geometry.schemeFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "76b25dcd100cdde24410f3b897b0c8af4fa79772995ab69971f5d8e73237fdb3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:2198",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:2198"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.ProjectiveCoordinateAcyclicity.0.OAI.PiExponent.GeometrySupport.ProjectiveCoordinateAcyclicity.schemeUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveCoordinateAcyclicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6eeed39db4480198ca7a63f6e715e388253ea4c227269e4c3988b8b3f1bd4e0b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveCoordinateAcyclicity:1115",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveCoordinateAcyclicity:1115"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech.0.OAI.PiExponentSeshadri.Projective.schemeFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "03bf20f228fb9aaa8d5a49050ac4f8f9c461779aa8d9a850f76711f4fc54bbc4",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech:969",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech:969"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistAcyclicity.0.OAI.PiExponent.ProjectiveTwistAcyclicity.schemeFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistAcyclicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "50bfad428fb3e5b92ced309712373c949af508f7eb32f8c414a0fbc6aab59bf8",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistAcyclicity:645",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistAcyclicity:645"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistAcyclicity.0.OAI.PiExponent.ProjectiveTwistAcyclicity.schemeUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistAcyclicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "33cd4f661e6b390e68380311a2edb529bdc67f2560cd3abe67f3f84887daf974",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistAcyclicity:733",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistAcyclicity:733"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech.0.OAI.PiExponent.ProjectiveTwistCech.schemeFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3044ca0488bb382197dc89a61920c9fb7438ae46daec5c88adc67ba085052e96",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech:370",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech:370"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase.0.OAI.PiExponent.ReesSheafCechBase.chartMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b4a5698d1f0768f3dc874b102edaa44575278dbe68fcca7b41f84166f3fa9ef2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:1580",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:1580"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase.0.OAI.PiExponent.ReesSheafCechBase.cochainAddCommGroup",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ff17783e5ef003831bdc746c7e25824335cb2db48729750a2cc17481e7df191f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:7338",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:7338"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase.0.OAI.PiExponent.ReesSheafCechBase.frozenChartOpenImmersion",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6b329e89cee7ff57d65e5fced24979e830c192fdcd4b310f021340144fc1ade8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:1762",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:1762"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase.0.OAI.PiExponent.ReesSheafCechBase.schemeFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "826bb818980726ae4dffee128b09a1d02f5ba6b7129a0a5a55f0c62cd63adbce",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:1941",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:1941"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechNaturality.0.OAI.PiExponent.ReesSheafCechNaturality.chartMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechNaturality",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c65c3fc9bf7e8e36b577eb0c1ebd4f5c3177a921597bbe69f0b5407d66a8a4d5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechNaturality:1644",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechNaturality:1644"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechNaturality.0.OAI.PiExponent.ReesSheafCechNaturality.frozenChartOpenImmersion",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechNaturality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "82632e90316d0f7d71f2d412e2c648e6e0164e4ae9b2b7351290498bf6ecf5d1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechNaturality:1794",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechNaturality:1794"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechNaturality.0.OAI.PiExponent.ReesSheafCechNaturality.schemeFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechNaturality",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b10b7e3194b158f56e4cb9fe6a13c9140f321b0c31e6fe89b1f293d57f3360a9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechNaturality:1973",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechNaturality:1973"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery.0.OAI.PiExponent.ReesSheafCechRecovery.cochainAddCommGroup",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7842a0c6a5c26c0d114b2fb03003aa48864d2df2ab5ceab7d715f9b9b9985abe",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:1572",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:1572"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery.0.OAI.PiExponent.ReesSheafCechRecovery.schemeFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "68513f5f0b62bf630df99933ce63862e37d0e44bf40c6f1f5aa9730d4e820c1b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:1468",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:1468"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.SerreVanishing.0.OAI.PiExponent.SerreVanishing.schemeUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.SerreVanishing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "62944c5f67c2b5080508e036d059276f891de4561aa7bd86458ced4154682e41",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.SerreVanishing:423",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.SerreVanishing:423"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Geometry.BirationalValuationStalk.0.OAI.PiExponent.BirationalValuationStalk.comp_eq_of_comp_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.BirationalValuationStalk",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0680c78d1bbae0ebe659120181e10091b1961d757d1626ea3cab6fa69cb47f03",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.BirationalValuationStalk:181",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.BirationalValuationStalk:181"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Geometry.CartierPowerFrames.0.OAI.PiExponent.CartierPowerFrames.frame_section",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CartierPowerFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6138447c3d15cdee02bc23850256ff88af9b55b9bbbc9de5e1728d285cdfbdce",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CartierPowerFrames:1195",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CartierPowerFrames:1195"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Geometry.CartierPowerFrames.0.OAI.PiExponent.CartierPowerFrames.framed_multiply",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CartierPowerFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7ff343cff0935a95cc08fe49917b8ea89471e3b1c5e578cbb42b19a31762b52e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CartierPowerFrames:1381",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CartierPowerFrames:1381"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Geometry.CurveChartFunctionField.0.OAI.PiExponent.CurveNormalizationModel.restriction_congr",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveChartFunctionField",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3591f759bafcfb3e0f9421ea175aef64b47422a8aab5199f6122947220a8ac1e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveChartFunctionField:1462",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveChartFunctionField:1462"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Geometry.CurveEffectiveTwist.0.OAI.PiExponent.CurveDegree.generators_isZero",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveEffectiveTwist",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f668df8922194e8e3cd36bfd2fc18dcb9847e55abce1582cc4521117f6911ac5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveEffectiveTwist:917",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveEffectiveTwist:917"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Geometry.CurveEffectiveTwist.0.OAI.PiExponent.CurveDegree.id_eq_zero_of_iso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveEffectiveTwist",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "69c92d1f5eebe5f099159f92164363c5acd942a228efbb121c4330c6c4d59151",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveEffectiveTwist:626",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveEffectiveTwist:626"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Geometry.CurveFinitePushforwardCoherent.0.OAI.PiExponent.CurveFinitePushforwardCoherent.presentationOfIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveFinitePushforwardCoherent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "acf6d04a0c8d2b4cf42ca25f44ff2392406287b4bdbb7f277b73bebd71180d9e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveFinitePushforwardCoherent:406",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveFinitePushforwardCoherent:406"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Geometry.CurveFunctionFieldCompatibility.0.OAI.PiExponent.CurveNormalizationModel.stalkMap_eqToHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveFunctionFieldCompatibility",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3c5d5566d85799fbe602f47d4ef3ea3b8d5447f22771db2070e14ed4dc18fd48",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveFunctionFieldCompatibility:1338",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveFunctionFieldCompatibility:1338"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Geometry.CurveFunctionFieldCompatibility.0.OAI.PiExponent.CurveNormalizationModel.toStalk_eqToHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveFunctionFieldCompatibility",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4684b6761a91a9ec74e232575c1f354454bf3eedcefcefc7879e93a822f2c169",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveFunctionFieldCompatibility:2193",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveFunctionFieldCompatibility:2193"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Geometry.CurveModelGenericPoint.0.OAI.PiExponent.CurveNormalizationModel.affineRestriction_fromSpecStalk",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveModelGenericPoint",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d7d7b9f6f6f76d2a420f82eab09e89ef8d1550546476f0759b387cfaa1affd30",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveModelGenericPoint:1592",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveModelGenericPoint:1592"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Geometry.CurveModelGenericPoint.0.OAI.PiExponent.CurveNormalizationModel.eqToHom_fromSpecStalk",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveModelGenericPoint",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e5eb5dc5bb90a3450d9ca8ce3a9a7f808b1c0ec81107df3f17481d97a2dfafe1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveModelGenericPoint:385",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveModelGenericPoint:385"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula.0.OAI.PiExponent.CurveProductFormula.zeroPoleOrder_eq_of_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b0e82fb76f476e7ca13c5887a9c088ae85d2c99526b7fd78be805ed0c02785d8",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula:4431",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula:4431"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole.0.OAI.PiExponent.CurveZeroPole.transcendental_ne_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1a6d97b8ebdae92b6b4fa524dfd4008a30a4b013c1a5b18eceb7bec500f01703",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:338",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:338"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Geometry.FiniteOfNoContractedCurves.0.OAI.PiExponent.NumericalAmpleness.positive_dimension_eq_nat",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FiniteOfNoContractedCurves",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dcccce0e9b5d95c6768642b5b1505f5dc9e3112e5f6b198e086c7400b26fb8fa",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FiniteOfNoContractedCurves:285",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FiniteOfNoContractedCurves:285"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturality.0.OAI.PiExponentSeshadri.Projective.relabeledOverlapEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturality",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f2251e8e9392dd69dfb14721cf99188d10db685008889efd686e479754c41470",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturality:469",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturality:469"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturality.0.OAI.PiExponentSeshadri.Projective.relabeledOverlapEquiv_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "809271e7eb1daee9e1fa59b35c98a9d82a0af8fdac60164d0eb444d426ce2996",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturality:744",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturality:744"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore.0.OAI.PiExponentSeshadri.Projective.chartIso_pullback_top",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9ae53b6e2e2321d006be3042f090a92a98da5144e36ba277830c2188c6a582a8",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore:1406",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore:1406"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore.0.OAI.PiExponentSeshadri.Projective.relabeledSectionIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c4a3ed9afe8ee67b4b277bcb8370bd3b1308c6ff10dfe06286a00e8eff1100f9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore:3428",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore:3428"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore.0.OAI.PiExponentSeshadri.Projective.relabeledSectionIso_inv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ee00fb0c126e6caf4a7c56ebd56c09b1bb4ec1146d60448b6e2b2960d865f044",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore:3704",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore:3704"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections.0.OAI.PiExponentSeshadri.ProjectiveChartSections.schemeFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "87af831cd03d9af51a3cc1d3add304c7be47478b316576dd58bd61d3e553d16e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections:499",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections:499"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections.0.OAI.PiExponentSeshadri.Projective.schemeFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c80027f905096b7bcee7554ac3083ac0b7dc0b382f7b9e8fa99f4da43cb5f9b4",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections:906",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections:906"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars.0.OAI.PiExponentSeshadri.ProjectiveChartSections.schemeFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "638619e36c358c36000a13278370b69b991d415d554dbd59e0dfdfc38a505235",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars:408",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars:408"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections.0.OAI.PiExponentSeshadri.Projective.schemeFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "52015283810346b5d56c8a4f53078a868f33c655eb7763adea1c259781469a51",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections:1162",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections:1162"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineReciprocal.0.OAI.PiExponent.ProjectiveLine.infinityEvaluation_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineReciprocal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ed2a49ace1e29f15c28f7a3d554768824973ce8c6d9f18296a2b4ad1473cccbc",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineReciprocal:1037",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineReciprocal:1037"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineReciprocal.0.OAI.PiExponent.ProjectiveLine.inverseCoordinateUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineReciprocal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "37b7f8630b0514ea1b86a0ced6174ccefd773fc4f1f28bd1b9f01fb599c25527",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineReciprocal:420",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineReciprocal:420"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineReciprocal.0.OAI.PiExponent.ProjectiveLine.zeroEvaluation_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineReciprocal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f9d5bc35d802c523b8c20db7c64eead0abb18885c8df1448d4d2bbc4b6156f2e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineReciprocal:676",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineReciprocal:676"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeScalars.0.OAI.PiExponentSeshadri.Projective.schemeFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeScalars",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "47eb5082f1aec492ceed085fa4014c813c77e5eda6aeb88a277ce49c3a26ded5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeScalars:566",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeScalars:566"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceSerre.0.OAI.PiExponent.ProjectiveO1.schemeUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceSerre",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ab334b54b01fb9632351007b7b9bf928899577ea7d5070c6cbc7269d19af5ec2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceSerre:456",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceSerre:456"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts.0.OAI.PiExponent.GeometrySupport.ProjectiveTupleCharts.schemeFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f05dfbd1532146b1856b59477bcc930ebba480f0a6ce88594aaa8c0803a44fc7",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts:3250",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts:3250"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Geometry.SectionCartierRegular.0.OAI.PiExponent.NumericalAmpleness.mono_iso_inv_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SectionCartierRegular",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ebb760c71d1cebaff0d6b7946fad522398c98817289ac488cb93e3b4b0048336",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SectionCartierRegular:306",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SectionCartierRegular:306"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Jets.AffineJetSupport.0.OAI.PiExponent.AffineJetSupport.map_bijective_of_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AffineJetSupport",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1a8738d672dab10f34a2fed608408b2b13cba831d2a417418beeeab478cef861",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AffineJetSupport:472",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AffineJetSupport:472"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Jets.CommutingTaylor.0.OAI.PiExponent.CommutingTaylor.factorial_normalize",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "885ec6b5b7fb5d2ed15229eab25a0a0b5d51fc082c0f60223966c6b3fb34e910",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:1541",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:1541"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Jets.FormalLogJet.0.OAI.PiExponent.FormalLogJet.derivative_log_mul_one_add_X",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fe2209770a7ed97eb73024caca5d590a88533189faa432c9477ae16d5c8bef08",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:2219",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:2219"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation.0.OAI.PiExponent.FiniteGlobalPresentation.presentationOfIso",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "73f6fa39183756532d78a68fed1b40630a2aa46f2526871716c3207a5a7f50b1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:1374",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:1374"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal.0.OAI.PiExponentSeshadri.InvertibleLocal.mono_iso_inv_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b7ff6285f59d203870ba99ad8cf6ee1f15f6fd6d3a7f44a483c236bcca09be4a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal:1602",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal:1602"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackOpenSquare.0.OAI.PiExponent.IdealSectionRestriction.appLE_congr",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackOpenSquare",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "18683532af87c0ac07a35fba87759c786065ff42834965dfc601b2f9c0592b74",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackOpenSquare:660",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackOpenSquare:660"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackOpenSquare.0.OAI.PiExponent.IdealSectionRestriction.bijective_iff_of_square",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackOpenSquare",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f00004c4c2da2434e91a65d514c355bf1ae5e1aca7070466c7e9e27462d0fc69",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackOpenSquare:265",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackOpenSquare:265"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.LocalAlgebra.IdealTensorPowers.0.OAI.PiExponentSeshadri.Geometry.affineMapCoefficient_id",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealTensorPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f09ead83a9a674608f15201648faecceeecd22713fc8a4e381f26756ca360298",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealTensorPowers:2019",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealTensorPowers:2019"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealAway.0.OAI.PiExponent.InvertibleIdealAway.isIso_of_comp_iso_hom",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealAway",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eb4d917eb3719e838559a6b5b11eaf56ec9a776c8b3264b969fa1de65a006e46",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealAway:510",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealAway:510"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal.0.OAI.PiExponentSeshadri.InvertibleLocal.mono_comp_iso",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7a5cca81213da9a21c6a05863af615af6b8a637d846e05a5f8d7a19535b1209c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:2219",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:2219"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal.0.OAI.PiExponentSeshadri.InvertibleLocal.mono_iso_inv_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1ab7ceb54f0cd5d3b2a6bc7fe1679753a3fbd20f5e5f7c20b0a747c5727dc5cd",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:2369",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:2369"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionMinimalSum.0.OAI.PiExponentJets.W28.LocalIntersection.subtype_indicator_sum",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionMinimalSum",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "77e0572f2edeb018f20dc48f87209b2b07f9a4093adb23e231c629fb9c1fd608",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionMinimalSum:283",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionMinimalSum:283"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.LocalAlgebra.OpenIsoFunctionField.0.OAI.PiExponent.CurveBlowupImage.eqToHom_fromSpecStalk",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.OpenIsoFunctionField",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "22ddbc8e391431517b97e52eab6eb7c50fde6a6c9b7ca8bee39ccef0b96604e1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.OpenIsoFunctionField:1189",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.OpenIsoFunctionField:1189"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.LocalAlgebra.TensorIdealInclusion.0.OAI.PiExponentSeshadri.Geometry.frame_inclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TensorIdealInclusion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a5cc1bf8e11ba793d75d697fa8d9044d2d9d60f84591e8d80c811290ee62da9e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TensorIdealInclusion:1692",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TensorIdealInclusion:1692"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.LocalAlgebra.TensorIdealInclusion.0.OAI.PiExponentSeshadri.Geometry.frame_square",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TensorIdealInclusion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ee60965a6b626de54c4446717c7c7df4d24fe05b018237423c640b46f2863df3",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TensorIdealInclusion:1132",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TensorIdealInclusion:1132"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_047.jsonl"
