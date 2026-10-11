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
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangular_monomial_mem_square",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b3e49ca45571174fef1e2a4ca9e5e95ec10a314ed2fe62d553984ae059bed196",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent:3307",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent:3307"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangular_quotient_length_le_of_residue_cotangent",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "312094aa320541b50e0a3123864ac7842066da4b191ae26b8969b256e14ebef0",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:10780",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:10780"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangular_reconstruct",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "59f9451704d7ca0a607a85e1cb98a5f6e337cc3bf3086aac6f255b3651964950",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent:2434",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent:2434"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.unitRectIndex",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7b9dd5ebb28fc990edf4ad5287d0e40aa55dec3c072cfc5a506f0cbd47b2ce01",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent:833",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent:833"
    },
    {
      sourceName := "OAI.PiExponentApprox.derivation_finset_sum_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0395f07cd3bc4210efafa19ac17b4937adcfc3669bd3b53a8ffa316c5a2d9c1c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame:785",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame:785"
    },
    {
      sourceName := "OAI.PiExponentApprox.derivative_vanishes_on_persistent_ideal",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "07811dc2afa0a54322899a7621760c4f52dba0705637add3ca7708cc858c344f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContact:4595",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContact:4595"
    },
    {
      sourceName := "OAI.PiExponentApprox.exists_persistent_frame_component",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bdef4aa840c145e319f4beaa18b57b75ec04246cb3383b9ece5d86b8c9e83b42",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContact:5640",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContact:5640"
    },
    {
      sourceName := "OAI.PiExponentApprox.frameDerivativeIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContact",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bb0e669215647ab637117c0a336dc66d61136881ddde9168e633473910ad70f8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContact:1006",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContact:1006"
    },
    {
      sourceName := "OAI.PiExponentApprox.frameDerivativeIdeal_levels_monotone",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "968e5f43bdcbdaa11c6aca9d6efba467a16e7c5bef1dfbbd81453cf400b80527",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContact:5278",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContact:5278"
    },
    {
      sourceName := "OAI.PiExponentApprox.frameDerivativeIdeal_mono",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4a621d4bf037907179fcb220aad776c86fb8c033fd5d8191d803af096fbf3d27",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContact:1574",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContact:1574"
    },
    {
      sourceName := "OAI.PiExponentApprox.frameWordCost",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContact",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "156b9c04d76718559be42fc6f000cfaf6286f41e2dec022ea6ef082f4d66e22a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContact:279",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContact:279"
    },
    {
      sourceName := "OAI.PiExponentApprox.frameWord_mem_derivativeIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f332876c0dabab3f8de753278c1e855388a2b6765e573d99166741dcc4a31085",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContact:1253",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContact:1253"
    },
    {
      sourceName := "OAI.PiExponentApprox.geometricDegreeWeight",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d43756fb2019c569b0f5f3df6970576af9c2e129ab564ce6619e03ac407d3e0a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparation:328",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparation:328"
    },
    {
      sourceName := "OAI.PiExponentApprox.geometricJetWeight",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6a2c4b6969e64d885af0d2ae263876fb387e967666327e00b75d6dbd9127e01f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparation:434",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparation:434"
    },
    {
      sourceName := "OAI.PiExponentApprox.geometric_weight_products_of_normalized",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2f36f0f720e37ae7cf447a406532e94bac9cfc14e212450a7ef33bcbf1a02d1b",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparation:1005",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparation:1005"
    },
    {
      sourceName := "OAI.PiExponentApprox.geometric_weight_products_separated",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5c009c06da0811299f640bd755a74fe4d8deddc2728369484eeee3e51022354d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparation:4817",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparation:4817"
    },
    {
      sourceName := "OAI.PiExponentApprox.logarithmicDerivation",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fce7b3723cd7851ac8c95509a236c0370596ceb10d3d35eceb636b1d4ccccd2d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame:321",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame:321"
    },
    {
      sourceName := "OAI.PiExponentApprox.logarithmicDerivation_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "44308d461dc12c26d81543e8361de71f41726114d908db62bf0b96b0583f882d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame:1247",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame:1247"
    },
    {
      sourceName := "OAI.PiExponentApprox.monomialWeight",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "01f36c75bdf6fe96787cba2023e52f0479a6f634b366d2f13e44d10c1c7da5cc",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:174",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:174"
    },
    {
      sourceName := "OAI.PiExponentApprox.monomialWeight_add",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4a01e6720c14b43b01d7176658132d60e089d1954571468873d509489497fd31",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:477",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:477"
    },
    {
      sourceName := "OAI.PiExponentApprox.monomialWeight_single",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1e5c9f37295eaf2563b9544691aa44de00848fce4eb55c16c75372555547aabc",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:750",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:750"
    },
    {
      sourceName := "OAI.PiExponentApprox.pderiv_support_shift",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "53db4743b7904a9d344f0b152696647c811da2f0649a09b2f8107edef92f198c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:2313",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:2313"
    },
    {
      sourceName := "OAI.PiExponentApprox.polynomialDerivativeCore",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContact",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3a7fb658fffb8b658a5f60faa03b28520e53957b592838d8e4f0ec397980f329",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContact:2162",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContact:2162"
    },
    {
      sourceName := "OAI.PiExponentApprox.polynomialFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4fce4c5386239239ef3c8e18c9f6fe72406fc4ce79b0b88769ea2d9d88f9ca1f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame:601",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame:601"
    },
    {
      sourceName := "OAI.PiExponentApprox.polynomialFrameWord",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fb40371d38df407c3065224bf9705ad4f52f6d2e088eb1274cadbb4f084d67d7",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame:5814",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame:5814"
    },
    {
      sourceName := "OAI.PiExponentApprox.polynomialFrameWord_cons",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5e8fdbabf360bcb758caade37ffe45e9b48c04483042740cb5662c67674ed687",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame:6104",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame:6104"
    },
    {
      sourceName := "OAI.PiExponentApprox.polynomialFrameWord_mem_derivativeIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f9edf5d4a1a26d9837b41bf51057523eb2531e3943a3e0be1b0e05af902617c2",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContact:3814",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContact:3814"
    },
    {
      sourceName := "OAI.PiExponentApprox.polynomialFrame_mem_derivativeIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "717b8cdbcc4c8249a43bb5ff143d5e5b7883d7dab885125e369956419f9acbaf",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContact:2888",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContact:2888"
    },
    {
      sourceName := "OAI.PiExponentApprox.polynomialFrame_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "874dc525cd8f3a3f800dcc303118b7d42d6b211c33107df999e0474625d20317",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame:1769",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame:1769"
    },
    {
      sourceName := "OAI.PiExponentApprox.polynomialFrame_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5102f453d803051bfc1f7c2564095dd8b1d44bbea298b999fb5c9ad81b00d354",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame:1619",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame:1619"
    },
    {
      sourceName := "OAI.PiExponentApprox.polynomial_mem_frameDerivativeIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1419a315fab5aadc99f5081eb80dc906aac09eb8f470d2df9542653b83b527ce",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContact:1904",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContact:1904"
    },
    {
      sourceName := "OAI.PiExponentApprox.weightSeparationFactor",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "63133c54b6583c5e64b866394545b1371ecfcfffa89c6007ba6fc620405e9e92",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparation:551",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparation:551"
    },
    {
      sourceName := "OAI.PiExponentApprox.weightSeparationFactor_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b065852b2d81112dc4977aa29a87064c13a80469805f7a0509720ab85807a502",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparation:679",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparation:679"
    },
    {
      sourceName := "OAI.PiExponentJets.EndomorphismEuler.cokernelMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4caa80bc5c33ad12efce38b3b11b66df6ebde8c0bf825b9fbde85fc3d8e0b56a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity:1187",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity:1187"
    },
    {
      sourceName := "OAI.PiExponentJets.EndomorphismEuler.cokernelMap_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "478fc5ceed9dc4849136418591e3d0a3ab7209fabd7bb313c86893c640720220",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity:3293",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity:3293"
    },
    {
      sourceName := "OAI.PiExponentJets.EndomorphismEuler.cokernelMap_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f603b83e6c2048d8b288648375a0959685092b61707e1da48b852e573e402c45",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity:1759",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity:1759"
    },
    {
      sourceName := "OAI.PiExponentJets.EndomorphismEuler.connecting",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "66420eac8e08ef52140978405809aa41d3b7747d50650ec301da787e7b6edf8d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity:4527",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity:4527"
    },
    {
      sourceName := "OAI.PiExponentJets.EndomorphismEuler.endomorphism_euler_cross_add",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d031776d2e49ee7d5cfdd3152377a6bdee4372adba812e031b05b98e30741ced",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity:9175",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity:9175"
    },
    {
      sourceName := "OAI.PiExponentJets.EndomorphismEuler.exact_connecting_cokernel",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "da0395c2ea3841f083c36627eb7363acf6d16a3a5e84d889c6eca4ca39bcbcd8",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity:5585",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity:5585"
    },
    {
      sourceName := "OAI.PiExponentJets.EndomorphismEuler.exact_kernel_connecting",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8109c27b5558bab0acc47f67727e61ad1526d8e0c2f8207135c09e4af031ae8c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity:4846",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity:4846"
    },
    {
      sourceName := "OAI.PiExponentJets.EndomorphismEuler.kernelMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bade52a78e90330358b2719ff63f748bdcd72833c8f84c20362f510aae250087",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity:311",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity:311"
    },
    {
      sourceName := "OAI.PiExponentJets.EndomorphismEuler.kernelMap_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b48c3bdcc8006aab4462be48949bc5cc85a24260dff791229ee373950075cd31",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity:2663",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity:2663"
    },
    {
      sourceName := "OAI.PiExponentJets.EndomorphismEuler.kernelMap_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e4a8718c75e1fa5703bf021d4c77ee5f8fb7132bf01c8ae07f6bc4c1cd345a98",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity:899",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity:899"
    },
    {
      sourceName := "OAI.PiExponentJets.EndomorphismEuler.length_eq_kernel_add_range",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a9d4adfb8eade4aac529197e6de99e511db62ca6b55ed80f2faba149c4d36f68",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity:6468",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity:6468"
    },
    {
      sourceName := "OAI.PiExponentJets.EndomorphismEuler.six_term_length_cross_add",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cfe935df0c817551563c163afc0f2e583b2e0ef8c4eb233ef3802db728d17bb0",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity:7351",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity:7351"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.CoefficientClosedLocal",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a847089723690bd29c586290e92dc6cc7d762c87155be931f3c380ca380c512b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv:1243",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv:1243"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.LocalPolynomialResidue",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialLocalResidueResolution",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1ac3b17b5b6aeea966107f2104f20bf30f7753b53beedc40ee2c2c106d1ac3f2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialLocalResidueResolution:2562",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialLocalResidueResolution:2562"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.RemainingCoordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "08971ec9b03350c8329e439a8e8a6b4462e160d4c556ece18daad15539018e38",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting:454",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting:454"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.SplitCoefficientField",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f455f1e38c8560569bdd9c95cd0bd284f5c9500094af39e9945cad0e216818ab",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint:566",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint:566"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.SplitLocalRing",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2d7a07dc363f0ba59a828a9aa78d7b51f8642949238453910347254fcfeaba17",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint:478",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint:478"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.SplitResidue",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c8a1dfc2dfb2e2dc2ac48db4aa1744937c07df968c7053a21a968c1e874a0183",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint:527",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint:527"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.algebraic_field_kernel_isMaximal",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoefficientLocalizationMaximal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5d82ce83d54b9e68b8cdd3c03ca763e2a6184c09784dd3239c5992d93ba5db93",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoefficientLocalizationMaximal:471",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoefficientLocalizationMaximal:471"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.closedLocal_isLocalizationAtOriginal",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8425e86e61c357f7e06caf5390b2e37265ea1e18dd24bbd13e17359ca51657e0",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv:1338",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv:1338"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.closedPointEvaluation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c9bc883fee017890802dc5184e608c2c0e03ee2b0a2f8022ece691167a997287",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint:1745",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint:1745"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.closedPointEvaluationRingHom",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fdd0a59fe280b1695e8f301910cd66169c49610a93442b0344f903f1af4969d5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint:2138",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint:2138"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.closedPointEvaluation_coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9278936a66d6d06fcb1a15a036b7a7331c30e277190869272a766ab33dd6acb6",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint:2674",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint:2674"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.closedPointEvaluation_kernel_maximal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "351aef086fdddc99a14ef4f2d88f18642c199f862356631face586f421f289ac",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint:2366",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint:2366"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.closedPointEvaluation_original",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitClosedPointCompatibility",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cd492d20a2cb882cfc8ac475c3454966a62e1b8553a27524c682c5725ed22346",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitClosedPointCompatibility:351",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitClosedPointCompatibility:351"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.closedPolynomialIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ffe4ac214a1d8173b58da81be7270399dac35a2b46b4c17442cfbade18e889f4",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv:2588",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv:2588"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.closedPolynomialIdeal_isMaximal",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fc7c7cae920a9812af506bfb105b51c6bb4e6608b43e94a2ed23fba22582c650",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv:2808",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv:2808"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.coefficientClosedPoint",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ff33796b22b1ce938de553f32f05c0031c675dd01ba7307e581297ffbb9f3158",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv:499",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv:499"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.coefficientClosedPoint_comap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitClosedPointCompatibility",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aedd016aa93c9bc7eab52d33be77d3486886fd1835077a333987a62041924a83",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitClosedPointCompatibility:3603",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitClosedPointCompatibility:3603"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.coefficientClosedPoint_isMaximal",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f2e5f1faa2a68398674c9a66e860169633abdec828c3452a43aa6717426dadf6",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv:767",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv:767"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.coordinateBasisClosedPointEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "42b15c24b0bb9a9d28223ffce5e70bff157dc33a08f5eeef7d2388ae99bd06ce",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting:3172",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting:3172"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.coordinateBasisLocalEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b439945a319e67599676fdcb4bb2b3feb22a938360c04491b7554f22954b2aeb",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting:2950",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting:2950"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.coordinateBasisRenaming",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "65cbfe9f35d4f5d2c4e15d01142e1d48c15a4e3cc9c0ee351aa673762f14b432",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting:1094",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting:1094"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.coordinateIndexSplitting",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5ee0c86f6a04f6b6346be553bbdda53175335e41c377e21cefb1d0d4f4b72774",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting:520",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting:520"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.coordinateIndexSplitting_inr",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0fe07e50460061460258acba5f85587af3c6cc4a020b31c795b4494a7110c7c5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting:770",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting:770"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.coordinateIndexSplitting_symm_selected",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4b286bfd7024dcfa71b76f10a12cb2393830cbce601ab67501926122b1856e20",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting:888",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting:888"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.coordinateSplitPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "165a7816840fba579c2edc8b7b2de44cd36a3e144a57d904eebf6320a1f7ec92",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting:1618",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting:1618"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.coordinateSplitPrime_basis",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "433291f6092099e57234d0432e5809eb5102be260cc9481f0781fae0ef0b05b5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting:1701",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting:1701"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.exists_coordinate_basis_indices",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "610360e978912e132ef428a8c38b2abf72f36458657bc0d945f8f494d98a8645",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceLocalization:2195",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceLocalization:2195"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.exists_coordinate_residue_basis",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2cf4d871691b3e54e4958b554da9727a8ebf5d04f1b881b8d0a74ab8e01995be",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceLocalization:1408",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceLocalization:1408"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.exists_regularParameters_actual_height",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialLocalRegularParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "740498f8df81f23f094dbfabda5b3fec627969c9db7f3a97663e0a9d76c38f21",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialLocalRegularParameters:436",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialLocalRegularParameters:436"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.extended_kernel_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoefficientLocalizationMaximal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ea75e9d4753d02b3176ead05a8d989f7fbd7baa0b8cb3ae02e6641dee6915b90",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoefficientLocalizationMaximal:906",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoefficientLocalizationMaximal:906"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.originalLocalCoefficientLocalEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b925e9fe738fbd32166ae83e3836a3f2d251a89d2bec5122100a219a94e93a4e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv:2279",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv:2279"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.polynomialPrimeClosedPointEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d10185d32c051fd85d41934230c680ce478d952cae286040c598b0d7ad1ce65f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv:3177",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv:3177"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueAlgEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeResidueAlgebraEquiv",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a3fa0b13e0944ceb621ac6031db4c7561fd0a089a32ffcd9a363d1a5a86bdfd0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeResidueAlgebraEquiv:1441",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeResidueAlgebraEquiv:1441"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueAlgEquiv_algebraMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeResidueAlgebraEquiv",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2fbad1468fe3cb344af5db2bc826207d9e3329e99e19e0a6e12ca26354bb199d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeResidueAlgebraEquiv:1866",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeResidueAlgebraEquiv:1866"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueAlgEquiv_transcendenceBasis",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeResidueAlgebraEquiv",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fcb862c7d9185294214814eaa22680bbaa8bb676b1b95e80dea2fb23f760afa5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeResidueAlgebraEquiv:2095",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeResidueAlgebraEquiv:2095"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeResidueAlgebraEquiv",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1c81f0e56f0dbf17f9e140881f8649b226f01f2a3b1c6b192904c0843a71733c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeResidueAlgebraEquiv:454",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeResidueAlgebraEquiv:454"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueRingEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeResidueAlgebraEquiv",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6c8d84d9efca2ecd1de51f2bcf05fc1cf995e7d0ccfe6d78ae6afa97d2f36a74",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeResidueAlgebraEquiv:557",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeResidueAlgebraEquiv:557"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueRingEquiv_algebraMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeResidueAlgebraEquiv",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "05b86e7702b843d9a7c2eb516fc8dd79b62682e2df01fb13434cf70ffb89e0de",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeResidueAlgebraEquiv:750",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeResidueAlgebraEquiv:750"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.rationalResidueEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.RationalResidueCoefficientField",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9c0d7578b5783b8340ca7665b0b3faeac5fdeb4ef2a899239d1ba989e835cfd5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.RationalResidueCoefficientField:482",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.RationalResidueCoefficientField:482"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.rationalResidueEquiv_polynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.RationalResidueCoefficientField",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b4bf8f05353820bf4c6cd5e379cc051fba1f18b95670bb93398d7acb0707dd32",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.RationalResidueCoefficientField:692",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.RationalResidueCoefficientField:692"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.residueCoordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialLocalResidueResolution",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "db0576c00e1bbadc20f8d9f1763322d9feb54f01be4dd961a2b00d655d733c41",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialLocalResidueResolution:2743",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialLocalResidueResolution:2743"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.residueCoordinate_adjoin_top",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4668385a0a59dbb677752bc8675088414d8619f9e4e43c90b94b542898886fcd",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceLocalization:826",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceLocalization:826"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.residueCoordinate_aeval",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0efb190e2569117f0a038b14da9f4a47409bf8139f527f966315ada44879e811",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceLocalization:383",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceLocalization:383"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.splitCoefficientResidueAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f810edb698d83c572c43fcbfd0c53f85b987d6573a4d9c19df49fe360e49fdcb",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint:1005",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint:1005"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.splitLocalBeta",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "561d949a870cd02b3c641b050e2f0d4f6981a8bc36a5755de6f0c747135b2a07",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint:634",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint:634"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.splitResidueBeta",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "948e1535449624e4e385ca62808ec91d327db243d9997e6f0658bd5e20ca2526",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint:794",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint:794"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.splitResidue_algebraic",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5838da1488e0134c150299eef258a4f6463e60fb3f5efa14c5fdb1cca6c71bcf",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint:1304",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint:1304"
    },
    {
      sourceName := "OAI.PiExponentJets.RegularSequenceQuotientTail.principal_image_eq_scalar_top",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceQuotientTail",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c5f2fbabfdf3cd5ff8954135a724e575c2a7ae6ac21d60f82e64350e5c2c2fbb",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceQuotientTail:278",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceQuotientTail:278"
    },
    {
      sourceName := "OAI.PiExponentJets.RegularSequenceQuotientTail.quotientTailEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceQuotientTail",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f246f330714c409e754d695f95a4635180fe15a8d489c90194ddbb07eb55069a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceQuotientTail:674",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceQuotientTail:674"
    },
    {
      sourceName := "OAI.PiExponentJets.RegularSequenceQuotientTail.regular_quotient_cons_iff",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceQuotientTail",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "74b6ffac18840921f36826a7ef9f9c66d1346b684059313e3787b444f56b487c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceQuotientTail:1173",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceQuotientTail:1173"
    },
    {
      sourceName := "OAI.PiExponentJets.RegularSequenceQuotientTail.regular_quotient_tail",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceQuotientTail",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9adced5db5741fc6935341633f83eb52b15528c0ee7c493bf468a8b5f5b18986",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceQuotientTail:1491",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceQuotientTail:1491"
    },
    {
      sourceName := "OAI.PiExponentJets.W06.colon_pow_succ",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.StabilizedColonPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c2ed06724bc0662e5af28b9165f29fa868caf8272bbeb447b0e29ebdaabb8a6b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.StabilizedColonPowers:510",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.StabilizedColonPowers:510"
    },
    {
      sourceName := "OAI.PiExponentJets.W06.colon_pow_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.StabilizedColonPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a6f45ef5d7dd451578858c0c7f614051964ba82a8169b5f13a5a416af0ba6e7d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.StabilizedColonPowers:351",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.StabilizedColonPowers:351"
    },
    {
      sourceName := "OAI.PiExponentJets.W06.colon_powers_monotone",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.StabilizedColonPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "310cd9485270e67da02a543d47b8945baf8b0e0390100c5465090d6ad8628f28",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.StabilizedColonPowers:751",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.StabilizedColonPowers:751"
    },
    {
      sourceName := "OAI.PiExponentJets.W06.exists_colon_pow_stable",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.StabilizedColonPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "28cc2b322ce485d5dc466f64f8f60b0b12a92f23c3510582883ba578200795db",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.StabilizedColonPowers:1736",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.StabilizedColonPowers:1736"
    },
    {
      sourceName := "OAI.PiExponentJets.W06.exists_colon_powers_eventually_constant",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.StabilizedColonPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a4761dee6898b581d329722a2942ebc007b217b62327f4872369cc5fe9adc795",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.StabilizedColonPowers:1293",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.StabilizedColonPowers:1293"
    },
    {
      sourceName := "OAI.PiExponentJets.W06.isArtinianRing_quotient_parameter",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterKilledFiniteLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "705f8a0cfb48cc7b06f74a1d66620cf4a20a65efe6b60526ba628d0195dac586",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterKilledFiniteLength:275",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterKilledFiniteLength:275"
    },
    {
      sourceName := "OAI.PiExponentJets.W06.isFiniteLength_coker_parameter_mul",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterKilledFiniteLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3e1a91f482a7077cca609525d56e65ee939656100aeef62c93ec3d8845b57e16",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterKilledFiniteLength:3144",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterKilledFiniteLength:3144"
    },
    {
      sourceName := "OAI.PiExponentJets.W06.isFiniteLength_ker_parameter_mul",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterKilledFiniteLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2406e4e0ea796b256eb74428188fd9a5ef487fd47edea25b398d0a846e5b03f2",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterKilledFiniteLength:2733",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterKilledFiniteLength:2733"
    },
    {
      sourceName := "OAI.PiExponentJets.W06.isFiniteLength_of_parameter_killed",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterKilledFiniteLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "688e7b4f4fe414b0190995f1b3cafbc8d605c094b2763f9e88fcaa4443f55e25",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterKilledFiniteLength:727",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterKilledFiniteLength:727"
    },
    {
      sourceName := "OAI.PiExponentJets.W06.parameter_kills_mul_cokernel",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterKilledFiniteLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "54ab237977ca194536cb755b82221ccfcca85174123bbedfb0eb22b35b8096a3",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterKilledFiniteLength:2332",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterKilledFiniteLength:2332"
    },
    {
      sourceName := "OAI.PiExponentJets.W06.parameter_kills_mul_kernel",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterKilledFiniteLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "51641b1e536e293c5a3fd7329342f3666afe13473b768d0273d0e4f7175f0531",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterKilledFiniteLength:1992",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterKilledFiniteLength:1992"
    },
    {
      sourceName := "OAI.PiExponentJets.W16.regularPrefix_quotientMul_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularPrefixLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "08b2acc333dab3dc09ce3ed19608a17b47acdfe62fd79b0fef23d2d71dbafcd6",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularPrefixLocalization:2245",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularPrefixLocalization:2245"
    },
    {
      sourceName := "OAI.PiExponentJets.W16.weaklyRegular_atPrime_mono",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularPrefixLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "931964fd6d0ea596267a27f52c962e448a31030d7a91917387ccba4d18bc3e51",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularPrefixLocalization:358",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularPrefixLocalization:358"
    },
    {
      sourceName := "OAI.PiExponentJets.W18.associatedPrime_nonzero_ext_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FreeResolutionAssociatedHeight",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "13811f3a4f9f885c590ca9db7cba721cfd5a20a2a4bc46ef0700894055b5f4ac",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FreeResolutionAssociatedHeight:3267",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FreeResolutionAssociatedHeight:3267"
    },
    {
      sourceName := "OAI.PiExponentJets.W18.associatedPrime_nonzero_quotient_hom",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FreeResolutionAssociatedHeight",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b068f33d7c7f48af328f5406d0c447de9b9a0129ac401ebb534d0e7249a1e504",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FreeResolutionAssociatedHeight:2893",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FreeResolutionAssociatedHeight:2893"
    },
    {
      sourceName := "OAI.PiExponentJets.W18.augmentationRangeShortComplex",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExtObstruction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0cd8db3fc0887716e2361a956ac11c97dacb1dc5ec4d12cc99be6495f0351658",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExtObstruction:1628",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExtObstruction:1628"
    },
    {
      sourceName := "OAI.PiExponentJets.W18.augmentationRangeShortComplex_shortExact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExtObstruction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5487a9e0ed7f61f0c4ef18fa381e753a6c100cd45ada251219ad1b7fbe9a6c2f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExtObstruction:1959",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExtObstruction:1959"
    },
    {
      sourceName := "OAI.PiExponentJets.W18.differentialRangeShortComplex",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExtObstruction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f74c6b047ec8eb8a651c91670ac76e0e5d66f009e34bc2fd6155804858ad4ee8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExtObstruction:615",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExtObstruction:615"
    },
    {
      sourceName := "OAI.PiExponentJets.W18.differentialRangeShortComplex_shortExact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExtObstruction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "21ec077a8aecee9c9db0a745145ef7c2cbee88308c5820d3b1832562dd9e0f33",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExtObstruction:983",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExtObstruction:983"
    },
    {
      sourceName := "OAI.PiExponentJets.W18.ext_subsingleton_of_shortExact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FreeResolutionAssociatedHeight",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "775d08af8a7b48c5f053543f8ca3e7d599b01dc4cda74484b0579242bb325ecf",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FreeResolutionAssociatedHeight:559",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FreeResolutionAssociatedHeight:559"
    },
    {
      sourceName := "OAI.PiExponentJets.W18.ext_subsingleton_of_subsingleton_module",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExtObstruction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0520db7b6f2de6e778bc55044e3017fd060a3f90777c9ff45789054a1acc8877",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExtObstruction:2576",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExtObstruction:2576"
    },
    {
      sourceName := "OAI.PiExponentJets.W18.not_isAssociatedPrime_of_ext_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FreeResolutionAssociatedHeight",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ca9dee8fddd68235e6d361114bf28ded097ddcfdfb58920aa57a76fa4f1a1391",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FreeResolutionAssociatedHeight:3725",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FreeResolutionAssociatedHeight:3725"
    },
    {
      sourceName := "OAI.PiExponentJets.W18.regularSequenceDifferentialRange",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExtObstruction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e8bdc11f441b16f8fe5ff2949779c71c2a086c75649edf8ba24ef3c98be9e43d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExtObstruction:3024",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExtObstruction:3024"
    },
    {
      sourceName := "OAI.PiExponentJets.W18.regularSequenceDifferentialRange_top_subsingleton",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExtObstruction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9cc4ed98f49473e467405f2d01d64abe2291988c851de31b12a6d756ebb32403",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExtObstruction:3195",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExtObstruction:3195"
    },
    {
      sourceName := "OAI.PiExponentJets.W18.regular_sequence_associatedPrime_ext_obstruction",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExtObstruction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "609e00ba5b55a5cb65111c3b9f3973236386f8e927bbbc79b977afb9bfeb9786",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExtObstruction:5701",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExtObstruction:5701"
    },
    {
      sourceName := "OAI.PiExponentJets.W18.regular_sequence_ext_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExtObstruction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e44b385d6f0680656c5a6c0703637108154a0e0383a0003deb7348ee931d3b83",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExtObstruction:3597",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExtObstruction:3597"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.ActualRegularCutHistory",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "inductive",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5eb2e70d1a30b374f5fd1ab2ebf0d88968fe7068ccf937009c7234d154de26f9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:2635",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:2635"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.ActualRegularCutHistory.casesOn",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aadca363642a976d9cd90d814e8a565309df4eef1cca30f5be646153e28b6f16",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:2635",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:2635"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.ActualRegularCutHistory.degree_bound",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9725bf4d2dd50fa31ee3d03de2c20ed41f9475df11b9a8b5ec32ff65da5dca6f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:3133",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:3133"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.ActualRegularCutHistory.local_length_bound",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5047c1cd2b09225a0286803961b8afb3dc354a549d6cf8e9596d49a1822dba3c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:6565",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:6565"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.ActualRegularCutHistory.nil",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "ctor",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cb79fb17dbc6eeab2b6ddfd536a3370c3d660f7e038f6c2f79077438feda3dd2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:2635",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:2635"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.ActualRegularCutHistory.rec",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "rec",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "74bdff2ee32bc187c6306b2e2a63d25704892bb08c378878d33c7beabcb63819",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:2635",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:2635"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_030.jsonl"
