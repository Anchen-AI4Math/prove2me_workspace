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
      sourceName := "OAI.PiExponent.NumericalAmpleness.power_nonvanishing_sections_of_divisor_lifts",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NakaiBasepointFree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f03d78d121a92ec06419e6dcb8655cba02ed947bd19d7cc27a2c0bf9db79ab14",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NakaiBasepointFree:530",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NakaiBasepointFree:530"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.projectiveSpace_cohomology_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveEmbeddingCohomologyBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8c3b94ce30054f7e726bd2c0e975c8ac266e6afc5921f65b14909e52c4ebd2b1",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveEmbeddingCohomologyBound:490",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveEmbeddingCohomologyBound:490"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.projective_line_cohomology_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerPolynomialDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7c54aa66ad3b530660a15dd99c0da43bbbd3778a1cedb639cb1b613ae7f2c1c9",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerPolynomialDegree:1722",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerPolynomialDegree:1722"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.pullbackCartierMiddleIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerTwistTransport",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5bac1cf33f28e5a79aab76ed70f0ae1899bcf2fdffb27669adeb96eaa4bb0f1e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerTwistTransport:1073",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerTwistTransport:1073"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.pullbackMixedPowerIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerTwistTransport",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3cf05518b509059006b09ba4fa333a9e3260582c9a480a890b62dc86f1d8bdfd",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerTwistTransport:388",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerTwistTransport:388"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.pullbackSection_surjective_of_unit_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NakaiSectionLifting",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d7962baf89dc81a39d1f88e0b637d47e5c32fc6c23af388ce47621f8fd00860f",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NakaiSectionLifting:310",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NakaiSectionLifting:310"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.regular_ample_sectionZero_dimension",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleDivisorDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e812b6dafe7eaf6e5c106c639e6ccca0ee5379c2ae3ddcb93677fe06ded4e7e5",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleDivisorDimension:3257",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleDivisorDimension:3257"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.regular_cartierPower_restriction_shortExact",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SectionCartierRegular",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "72b5ae5531be8be0b4221f026cbec9e4584ed71ee7b78685cd5b88a98837bacc",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SectionCartierRegular:833",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SectionCartierRegular:833"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.regular_mixedCartierPower_euler_difference",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CartierMixedEuler",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c603fbdf3d6871290fd4b992864e2abf4818e3761253bac82c9b2d5c858a6fb0",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CartierMixedEuler:8398",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CartierMixedEuler:8398"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.regular_mixedCartierPower_restriction_shortExact",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CartierMixedEuler",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b7e9aba6e787703580bf3930a39f454a24100087350cd7217a9a70fcfd942f02",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CartierMixedEuler:4764",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CartierMixedEuler:4764"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.regular_sectionZero_dimension_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerSupportDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "315f246baa6a08c3ee54f1895112f633a6fae1156a1b4de88122bf18c2060ac8",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerSupportDimension:3422",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerSupportDimension:3422"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.regular_tensorSection_restriction_shortExact",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "082120728ac29366ca294306b30cda457838e94b4a8f547fedfd9ecf2bd180ad",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair:443",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair:443"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.scalarEnd_mono_of_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionMono",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ea482ebcd1a57e9145fe9a015cc4f101e449e1f7727cf791ee3e63ccb28bf5f5",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionMono:1470",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionMono:1470"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.sectionLinearCombination",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "75f9fb383075b6d3f8ff24a7093b8a84b46c3547a49ef4bda82a692997d0c29d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice:4518",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice:4518"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.sectionZero_dimension_succ_ge_of_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleDivisorDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9298045c1f0b41e4e63624f4b56e21869ab27790b8c57075e4f71c82b32da04e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleDivisorDimension:1373",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleDivisorDimension:1373"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.sectionZero_pullback_dimension_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleDivisorDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "657c37f451241be086223cd59a60efd50d166f776e856ba61e481af027ce2db8",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleDivisorDimension:523",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleDivisorDimension:523"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.section_affine_coefficient_nonZeroDivisor",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerSupportDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "553dcd74422e8a573428f346c052feace06d6419f611c06fb907739503b03914",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerSupportDimension:2905",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerSupportDimension:2905"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.section_coefficient_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerSupportDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cc65f39e982a6a3d4dd50413521e76e11343a421c01b30f0a97425bd941c4d18",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerSupportDimension:1958",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerSupportDimension:1958"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.section_mono_of_regular_affine_frames",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionMono",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "668646215a02f08e56abdbccfbca756c1d1a4c275d847634b4f09e6f6409cd6a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionMono:2283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionMono:2283"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.slopeBundle",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "40c87339a3dbb6f7f4c6db57df9ba1b04529e46e4cf4f5478996a14b4a10557c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra:445",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra:445"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.slopeBundleAddIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f87ecd8ec71d1b9ee333cb18493f98bbc544e2abe87988d1847cd3b7c7cd4557",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra:800",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra:800"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.slopeBundleCongrIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8cc1735277b48647e3625b24b6353858ccb4b2b2d2011ad23be04eb47f9c7009",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra:1069",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra:1069"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.slopeBundleCrossIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f54980b5c1cffc2256834f823daff6d9141251c03ceee9a4cbd52321543fcc41",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra:1279",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra:1279"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.slopeBundlePowIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cb92ce2aad9c11012b177fb9e717f5b453d40bc50368ecd2b81faf0a6239011a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra:545",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra:545"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.slopeBundleSubtractIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "24292d1aa13898efa91897fe5dd3798e5c6465c06acd03ee060de4d4c0ad628c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra:3046",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra:3046"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.slope_lower_closed_ampleness",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.NumericalSlopeInduction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "53b095ae7621af4b436e749f8e7b358e9693281a5ca8791f99a4fe4ee1970cbe",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.NumericalSlopeInduction:788",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.NumericalSlopeInduction:788"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.slope_zero_isAmple_iff",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeTopology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7f723b74089430a9b57fe15017a80f418a43ef9699f8e2c6ea12674dd6680fa5",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeTopology:2382",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeTopology:2382"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.structureLineBundle",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "699dcb58769c4d01d0007007c2b5a5e1b6f612c4d346561c7e8efc51c708d0cc",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:250",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:250"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.tendsto_atTop_of_forwardDifference_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerDifferencePolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6467b2c4e90e4d153ebd4202dbc78970082dbcace6213f654fc7747e105dcd60",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerDifferencePolynomial:3890",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerDifferencePolynomial:3890"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.tendsto_choose_div_pow",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerDifferencePolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e43c05c65316823776fa9ec835d31012f30170e06a3bbaba005f9791b5573782",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerDifferencePolynomial:1817",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerDifferencePolynomial:1817"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.tendsto_normalized_of_forwardDifference_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerDifferencePolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e90fdd9ad5e040366619887687eea17cce8b99b7f2355c87d08d0105191b17bf",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerDifferencePolynomial:2834",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerDifferencePolynomial:2834"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.tensorDifference",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "db20840077238abd01c25cbdfea59410e94002e877e454361bb71ab8b6cccb6d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra:490",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra:490"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.tensorDifference_commute",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "86d18526004733a74b3a06968ef81b33e6fdac6efbbbc398e1bb5e789bcfd0cd",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra:3738",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra:3738"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.tensorDifference_sub",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dc113bacde807d401f357ba90fda9112931f919b717e183e97f662af34089e79",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra:1370",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra:1370"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.tensorDifference_tensor",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4f9315345fcb8a27651a6ccc534e6b763b870a5b27bac9acfe6a17f0d7a546aa",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra:6286",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra:6286"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.tensorMap_framed",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CartierMixedEuler",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4c148393adad2ab83a3a53b89d3b3811d40c68fe818d1fe536b0a22ff00e2876",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CartierMixedEuler:1064",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CartierMixedEuler:1064"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.tensorSectionComplex",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fe73e59c19cf036c45fbf56dfbeb7e1618a4f1c6199c5f83cd1bb2cc5beac87f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair:1473",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair:1473"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.tensorSectionComplex_shortExact",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "11d17b0d1af37ce94a2751969522b7d4d49c94014597ac764fb932e4cf3dd8fb",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair:1845",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair:1845"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.tensorTwistSwapIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "285d55c57f25881390b72dd4ec258eff8bb39eee5a3c808b9006b5893d240c6e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra:1097",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra:1097"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.tensor_euler_difference_cartier_pair_of_ample",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerCartierAmple",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "711516b414e6dc75756961e0148b31b98860e40e4f5fd6ac25aacc620d37b284",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerCartierAmple:493",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerCartierAmple:493"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.tensor_euler_difference_regular_section",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "91003bf170570a455c26e5cb756667b2e40fd0062ba722c48807857e8f055060",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerRestriction:378",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerRestriction:378"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.threshold_lt_of_ample",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeTopology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aadfebef4e5a482c9cb8896062089a246e8bcd19dbba1112bd8e3b7a5f241a69",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeTopology:1737",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeTopology:1737"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.topEuler",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerTop",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f43d09a9ec18a6799672156d93ced07f606f4212928467a0665275412fbe7838",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerTop:344",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerTop:344"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.topEuler_iso",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerSlope",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ec7c71578cfe6c76ce767dd124fdd80cabe5fa75ff65e22cb983d0f9f08c3467",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerSlope:763",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerSlope:763"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.topEuler_pos_of_ample",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPositivity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "86f672630af5bbd539275b5a662d32cb0845b448e4213d23de078d983766c3ac",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPositivity:3931",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPositivity:3931"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.topEuler_slopeBundle_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerSlope",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "23d10c84c674aaa0820574749489f2b1ee6d5502e269c8eb83e546fa5f3453ff",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerSlope:2469",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerSlope:2469"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.topEuler_slopeBundle_split",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerSlope",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "65f55002c0e749dc9537c077c173f89aac1f3bb52fadd00df2add93c836afdd2",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerSlope:6924",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerSlope:6924"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.topEuler_tensor_powers_binomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerTop",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8f912f0df699b00d9266575bdb4e41d8521f6b99a92726074aebb82cebc5a1ad",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerTop:2552",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerTop:2552"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.topologicalKrullDim_irreducibleClosed",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.IntegralCurveExistence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d0f5e3b7a54ed710e7edddeca6c52d2cc4207e4f8555fcbe6636e3132d3f36db",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.IntegralCurveExistence:2370",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.IntegralCurveExistence:2370"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.uniform_curve_margin_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.NumericalMarginRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f1edaf6811f0b2733ad937f87ec6e233dc9e9f24e98261f4feed93980033122e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.NumericalMarginRestriction:1445",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.NumericalMarginRestriction:1445"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.uniform_margin_tensor_powers",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveDegreeLaws",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6f7edf229ea3f9ab61c07e2a2be4cda6d26965976fcfcab2549a3a9311eab99d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveDegreeLaws:2742",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveDegreeLaws:2742"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryAuxiliaryJet.branchCoordinates",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryBranchEvaluation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b334029e19393e2e9608e7b6257dc47fbfa71cd43e9bed623f16b3c287dbb5de",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryBranchEvaluation:240",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryBranchEvaluation:240"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryAuxiliaryJet.branchCoordinates_hasSubst",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryBranchEvaluation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e1c2829b0f69b038790355a1adcdf8e5d1c70a6f7c2afbb03aac32e56342898d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryBranchEvaluation:398",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryBranchEvaluation:398"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryAuxiliaryJet.evaluation",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryAuxiliaryJet",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "52ab387ad4b41fb796b2dcb3f30eb8f584b6cba38a2cb44d6d00035718c86c95",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryAuxiliaryJet:521",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryAuxiliaryJet:521"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryAuxiliaryJet.eventually_exists_auxiliaryPolynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryAuxiliaryJet",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fa3a8d02f659741dfaf285922b6fd11ebc1432ba69d5e431c9c0f3dedb9b2be9",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryAuxiliaryJet:1425",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryAuxiliaryJet:1425"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryAuxiliaryJet.eventually_exists_auxiliaryPolynomial_nat",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryAuxiliaryJet",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5df2dbb581d5d0be64b44614875720e1657a0060b4859ceb33a91e654976f454",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryAuxiliaryJet:3163",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryAuxiliaryJet:3163"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryAuxiliaryJet.formalJet",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryAuxiliaryJet",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a0d733b12e7ed84026a0c5eba173c8f3c83a1208ed3ba0ab53309ba2d49eba08",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryAuxiliaryJet:326",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryAuxiliaryJet:326"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryAuxiliaryJet.formalJet_pderiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryJetDerivatives",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "082eddfa6da52e58b960bd957b32b17b3fa6f67a1df2b493a7b56eb418bf86a6",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryJetDerivatives:269",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryJetDerivatives:269"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryAuxiliaryJet.formalJet_subst_branch",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryBranchEvaluation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4ea1885437cf2fcbba69cdd1bb06aa42e6bc06e00efa09078f80670ee8ce157d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryBranchEvaluation:781",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryBranchEvaluation:781"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryAuxiliaryJet.formalJet_word_vanishing",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryJetDerivatives",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "68ffc87981e78ce97fbe83766ed2e63eab187574a3a32ced2f383ae840b54ccf",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryJetDerivatives:724",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryJetDerivatives:724"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryAuxiliaryJet.ordinaryWord_branch_order",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryBranchEvaluation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d1022d81881021736009e8fde1e9ea4a946b437a1c9890efcda9ed2ff64b7c18",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryBranchEvaluation:1517",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryBranchEvaluation:1517"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryAuxiliaryJet.polynomialOfCoefficients_supportBound",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryAuxiliaryJet",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e18157d19ea069928396941689c49db8d4283d59591c3c2c587a1f8b3056dd4c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryAuxiliaryJet:873",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryAuxiliaryJet:873"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryComponentRigidity.NormalProductComparison",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.OrdinaryComponentRigidity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4f02b969d1dfca851018b4060f67ba56362536c3d63882ebab1240e21ed3db93",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.OrdinaryComponentRigidity:410",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.OrdinaryComponentRigidity:410"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryComponentRigidity.PersistentNormalComparison",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.OrdinaryComponentRigidity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5ef2002dd80e5cae9df5386637ba3f023df4262ee985832c220b449c2b1faff3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.OrdinaryComponentRigidity:833",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.OrdinaryComponentRigidity:833"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryComponentRigidity.coordinate_constant_of_persistent_comparison",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.OrdinaryComponentRigidity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4d3fb51fbd11ac1230babe649ce822e54ae4b4884122498fa596ecb3f7327822",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.OrdinaryComponentRigidity:1591",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.OrdinaryComponentRigidity:1591"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryDVRBranchJet.contact",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDVRBranchJet",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "79c9e23bd27268c58b3298f1a6252febdb5f72d1f7f49ddb5eca4b05c56aeb01",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDVRBranchJet:1957",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDVRBranchJet:1957"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryDVRBranchJet.contact_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDVRBranchJet",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "30d857a3da2fd6c38ddaa00fab1e96eab78d8d4187b299e2ea6abcca826be6e0",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDVRBranchJet:2175",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDVRBranchJet:2175"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryDVRBranchJet.coordinates",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDVRBranchJet",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8cad82046bbac8156ee96b14a173de4e097b55a4b3bdd197a3ef05846811e39c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDVRBranchJet:943",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDVRBranchJet:943"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryDVRBranchJet.coordinates_centered",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDVRBranchJet",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bf9f10a94b0a80d0f2691f88ed195684753e559a54cb68692a3ca80f105e358d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDVRBranchJet:1112",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDVRBranchJet:1112"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryDVRBranchJet.coordinates_nonzero",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDVRBranchJet",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "abf9916e77f27076591a12cef4bf0378fe59e4664b59a02087e6fb5117071c55",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDVRBranchJet:1548",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDVRBranchJet:1548"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryDVRBranchJet.expansion_aeval",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDVRBranchJet",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "05aa286ca6f66f42b19ec65382fb5060c26163cec299df205d415d1ec02880bb",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDVRBranchJet:487",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDVRBranchJet:487"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryDVRBranchJet.ordinaryWord_addVal_lower",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDVRBranchJet",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fd031bbde142e328f88de49f6ea7d75bc9626f41c36ca8b4bc8221d730f46bd1",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDVRBranchJet:2517",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDVRBranchJet:2517"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryDVRBranchJet.ordinaryWord_addVal_toNat_lower",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDVRBranchJet",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3bf9b7d9ab92a45285ff3662790b9b502d03862ad21aa555b8fadd72a7556c31",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDVRBranchJet:3446",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDVRBranchJet:3446"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryDVRBranchJet.ordinaryWord_colength_lower",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDVRBranchJet",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c3ba4eca0a2680092ce8c07e05312a147a526eed79da390f0f2591acbff12aed",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDVRBranchJet:4353",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDVRBranchJet:4353"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryDerivatives.BoundedWords",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "929fb25d43ed1a7e8f3de947e8f8af1a87892ba9148bcad8e75779df296dc2e8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals:2832",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals:2832"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryDerivatives.Polynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "65604b211d391bc41950560b57c2e4e60f7105f18c8117acb1501ba806bd9205",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals:344",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals:344"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryDerivatives.equation_supportBound",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c9f9a3e2c1222129d7b941a94e608b71a613982d21bee4ab2e27d2dfcd7816e8",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals:3476",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals:3476"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryDerivatives.equations",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a9b888f56bcdb3a3e4743e3ec0f01adbb80fa780e1c9b5642284ba0b5f570eb0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals:2956",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals:2956"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryDerivatives.exists_persistent_component",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d7a5a2690cf5ccb3640547d99bf223b32ae0ac7cf67c5b674dd9b7ef55f672d0",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals:3800",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals:3800"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryDerivatives.ideal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0c49c155af29701bc93151e2a6c7fa5a27b13f6e2a2edd084b184b04619a412a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals:1677",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals:1677"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryDerivatives.partialFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c6c5455286805d386d819c2c5e6ef344f52f86f41f24bc3eb63d6db3e08ed8ea",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals:403",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals:403"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryDerivatives.span_equations",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f2336368bba6551dd772f4ed8f27213ed1f48c1d2353e76a54424d996405ae63",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals:3112",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals:3112"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryDerivatives.supportBound_pderiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "523356e273dc00b55fcbf11c9dd1d5dbc051dade7f9c2a124ed7393a57e63fa8",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals:1831",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals:1831"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryDerivatives.supportBound_word",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b0cf0cd6e43f704b6da60105ed87b05cbb1ee082301b6eb95444a8710203f305",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals:2438",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals:2438"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryDerivatives.word",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4acb49286ee38ec51890763f1ce677cce540680d842fdab400580e2b2f4d1b66",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals:1322",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals:1322"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryDerivatives.word_cons",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e94a79cd79dcc88912f620c66e28ab23c5daebc244f2f1f049f4cb55d8d6d2e7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals:1519",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals:1519"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryMultiplicity.localTaylor",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.OrdinaryMultiplicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "352f9a61fe1d1224cba823cf0b5c4725d1b7ce2f96a552c179e73bc96703323a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.OrdinaryMultiplicity:1155",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.OrdinaryMultiplicity:1155"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryMultiplicity.localTaylor_constant",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.OrdinaryMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "19ac4ccf65e071fd9e7d779c526d974032aeb983e9404c5eb41ae767bbc07609",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.OrdinaryMultiplicity:1504",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.OrdinaryMultiplicity:1504"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryMultiplicity.localTaylor_firstCoefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.OrdinaryMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "23d9defbaa8f3fc01474ab82ae75d9b81163856d8cfcbd045aa3a253ed04ac35",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.OrdinaryMultiplicity:1987",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.OrdinaryMultiplicity:1987"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryMultiplicity.polynomialTaylor",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.OrdinaryMultiplicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fb5d42027413dc1969c2690c975ad7fa56497d0a7f064f0b5819d827107ddb96",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.OrdinaryMultiplicity:338",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.OrdinaryMultiplicity:338"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryMultiplicity.polynomialTaylor_constant",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.OrdinaryMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "13bdac3b6667c516b919f5043bd94f7da683cb15b989b1e52a2edb2e5b420870",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.OrdinaryMultiplicity:668",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.OrdinaryMultiplicity:668"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryMultiplicity.prime_rectangular_length_lower",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.OrdinaryMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f41c6dba3c8f6d9f41c9cb08b97c92bd165d65dc14adb679829bab4a873d1238",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.OrdinaryMultiplicity:2798",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.OrdinaryMultiplicity:2798"
    },
    {
      sourceName := "OAI.PiExponent.OrdinarySliceComparison.comparison_of_normal_basis",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.OrdinarySliceComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ba1876f59b0014aad78a95e69219a0c2e893fbf9bb15cbfc5c86d53efc855d6f",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.OrdinarySliceComparison:438",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.OrdinarySliceComparison:438"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryTaylor.derivativeWord_wordCost",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryTaylor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dd93b590e995702dc856437a118ff31337c1656ec986896f9d156497589f83ff",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryTaylor:1463",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryTaylor:1463"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryTaylor.derivativeWord_wordCost_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryTaylor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b93889caca506ecc4a8abe758dbff22a9772f145442b1cb6640f1f0a2eec3e82",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryTaylor:2068",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryTaylor:2068"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryTaylor.mixedIter_eq_wordDerivative",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryTaylor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0d8bd3e28b27f19d2127de6f1223016cc58557fa04aa9167e72b294b0e705f11",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryTaylor:997",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryTaylor:997"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryTaylor.ordinaryTaylor",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryTaylor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9fe3a8b7f098e199eaff673f9c09309a46969e5e9783fef7d61a59e5bbdfd757",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryTaylor:4106",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryTaylor:4106"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryTaylor.ordinaryTaylor_ideal_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryTaylor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "70463dab88665c02a86572ba1b76bc5c852c487a6bfcfdf5da60ea175b6c4c9c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryTaylor:5414",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryTaylor:5414"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryTaylor.ordinary_residueTaylor_ideal_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryTaylor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "da4f867a52168e4e8686d8459b137409b6d49d627ec45c329e89397227c050c9",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryTaylor:6066",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryTaylor:6066"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryTaylor.residueTaylor_ideal_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryTaylor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ab710433cbfa1fbdf2ca683cfdbdb658332f336d26de37c5d65e56028f95f88d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryTaylor:2604",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryTaylor:2604"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryTaylor.wordDerivative_append",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryTaylor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f59869dce435ccb06d590f5a8600be055b56ff9cb2aa399ed31a94d4c46d1d6e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryTaylor:415",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryTaylor:415"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryTaylor.wordDerivative_replicate",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryTaylor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "40ced0cc7a03384af824e6691927b9bc6a14fc360a00065bd025ce703a4cc117",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryTaylor:704",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryTaylor:704"
    },
    {
      sourceName := "OAI.PiExponent.ParameterResidueField.parameterChartConstants",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterResidueField",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b86ec5607b7fd5190b85191f34ebe8d47261c54e0cdafcc0aed397c9ae178030",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterResidueField:657",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterResidueField:657"
    },
    {
      sourceName := "OAI.PiExponent.ParameterResidueField.parameterChartConstants_tower",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterResidueField",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2a164031af3b7152d10dad73af3f977a5609c1afe4a7ff24e48445aa0c2ca832",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterResidueField:935",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterResidueField:935"
    },
    {
      sourceName := "OAI.PiExponent.ParameterResidueField.parameter_residue_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterResidueField",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "68e20109655b3b8835b1a6769b3745ba56bbf0136fd445c1799449cdb84ca53e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterResidueField:1347",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterResidueField:1347"
    },
    {
      sourceName := "OAI.PiExponent.ParameterResidueField.parameter_residue_integral",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterResidueField",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ad35d10006c6099840da22d361497969a6d09a0108a885da9e88f80ffb648032",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterResidueField:2389",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterResidueField:2389"
    },
    {
      sourceName := "OAI.PiExponent.ParameterResidueField.residue_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterResidueField",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4a721469262df2068e12703e1fad9a218d20c7ec254c2088a73ee6562ac9d027",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterResidueField:235",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterResidueField:235"
    },
    {
      sourceName := "OAI.PiExponent.Parameters",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "inductive",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1959ebb3f2aea65f610a6dccebb1d76370724d77f59615a8613f6fde38207407",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.A",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a4b59a8b4862dd1436e6b185c6ad40d37c8a10bf6b7128048cbdff8c4ba8d1c5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.A_lt_B",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "104640a061689cc71fe999651e3c55424ecf9a4e77ecd24cc21c0769b0f4970c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.A_lt_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5b83f59dad8ec95a479b1dab1ca23ddc5b74aaa0e40f6bcf38fb67c5267a6b14",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:5586",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:5586"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.A_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e48c067080464a6cdb88ca55f08a0eb904b2d7cc9fe26638ff1062af38950cb6",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:5380",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:5380"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.B",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ce4bf30b3ed54f9be5151c2a8405547f6049288790361cbc1dcbf2fca8ece291",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.B_lt_C_theta",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8321e192bb45c64f18380c423651fdaf474e0ebcc1e0d827e539199d8c59592f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.B_lt_inv_C",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "93c64801fdd7a5307b83f52be8c091143d8da52d2d5b9011a879767655e555c1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.B_lt_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "692e10f8930e2164c2799f0e0b4727a1fee6feb0770a8ec33e6bf53ca834a61f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.B_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1583d05f58cd83d31da1ebe0310f6938534e208b9a82a56845cb09cfaa9efb6d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:5452",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:5452"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.C",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "78f8bfd96546f52acaa6ecc5403daacbd937489beb030bcd3667d170ea4230c9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.CB_lt_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "16622c257f9ce1c96b78ae85270fa38466916b8f68e9d38610e435bed1d6b591",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:5738",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:5738"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.C_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c2d6f857c81cc4953c3eff2c079eff710dccea35e06a012479a1e7bc7a039b4d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:5516",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:5516"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.C_theta_lt_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9c1e892f80d53d1583368c914bd05959fba4da7100a7c59b921c4ed990099270",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.approximation_gap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fd561b73e671cc3c7dec530c3242cbcd45a158917a9a2427bfb700951d1a8206",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.casesOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "414e266917c5ab0795344618c5171503fbe89f8fd4de3f4c795e862355a05d13",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.eta",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "91809a058c30f17b25f47973836bfcb627bbf45aa2b5d7a58df2b495bc848f0a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.eta_lt_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "083f67995d6b489dd477f85539829ae0f909e017b7b2ae98d79c97d17bc86a1b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.eta_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b7ad4122c2a230b73caa0b6389cc6104fb061ab5dfefa3e9b39bc3605a8f3628",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.gap_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "df664f2d63b6b8c38fc17236e4ce5feafffd4c8434f85135c3d44d2f63d9c3e3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.mk",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "ctor",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "96d047fab06b0c5b26def512360adacb9bb5b285bede888273d0adac5e69b4c8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_020.jsonl"
