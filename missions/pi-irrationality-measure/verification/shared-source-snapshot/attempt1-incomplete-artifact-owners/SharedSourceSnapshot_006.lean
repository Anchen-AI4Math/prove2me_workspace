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
      sourceName := "OAI.PiExponent.CurvePlaceCenter.fractionSpec_isDominant",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cfe55c9b70fb2b22a23b7f0139da7bd0ca9490dd052134eb0d740f40ea604245",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter:422"
    },
    {
      sourceName := "OAI.PiExponent.CurvePlaceCenter.hom_ext_fraction",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9754c7a95627b49bc79541f138e56aa6351cbc761592e30588d760678142dd79",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter:1039"
    },
    {
      sourceName := "OAI.PiExponent.CurvePlaceSectionDivisor.degree_eq_euler_difference",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceSectionDivisor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a9ff9a6026b10ba737794c40ec538e82107103d202b78484dac8f5af6c009d16",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceSectionDivisor",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceSectionDivisor:1450"
    },
    {
      sourceName := "OAI.PiExponent.CurvePlaceSectionDivisor.degree_eq_euler_difference_full",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceSectionDivisor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5c49cb78379e9581e982b8e92a4fe35674cee36d8c3b0c1e223232217deca690",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceSectionDivisor",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceSectionDivisor:2828"
    },
    {
      sourceName := "OAI.PiExponent.CurvePlaceSectionDivisor.divisor",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceSectionDivisor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b7993485cfb309e74a5995e6797816b4b35d66542c2ae1c6469d5061df90cc50",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceSectionDivisor",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceSectionDivisor:641"
    },
    {
      sourceName := "OAI.PiExponent.CurvePlaceSectionDivisor.divisor_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceSectionDivisor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6b1517907fef002c11cb671fb6c1b771ee87db4c9c571caf5d5ac05fa289f836",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceSectionDivisor",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceSectionDivisor:1022"
    },
    {
      sourceName := "OAI.PiExponent.CurvePlaceSectionOrder.divisor_eq_local_order",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceSectionOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3e5fa47dfdea36f4ec20dd2e483eb26c674d13fa602124f2a24a07c41ae1f834",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceSectionOrder",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurvePlaceSectionOrder:736"
    },
    {
      sourceName := "OAI.PiExponent.CurveProductFormula.finite_support_placeOrder",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9bf551c1668f040d70e20f83d65e27a697a74ad855e66215d8d467dfb68bdb9f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula:3125"
    },
    {
      sourceName := "OAI.PiExponent.CurveProductFormula.order_ne_zero_iff_positive_or_inverse",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9aa6aaea2b44eacfdb3cff0de4a674fcb43c5f0117a65583d0a62950da4af120",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula:976"
    },
    {
      sourceName := "OAI.PiExponent.CurveProductFormula.placeOrder",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5d9d947710bd904306b0982f1f5154f8fdfd9bf1e7270447a65bcb078f953de8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula:384"
    },
    {
      sourceName := "OAI.PiExponent.CurveProductFormula.placeOrder_constant_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0d50173a7be590faac2f206be311e0a60f7af506bcee6880b61961be1ff82edf",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula:8180"
    },
    {
      sourceName := "OAI.PiExponent.CurveProductFormula.placeOrder_inv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b1f9e5772a7a25dfa538b98f51f3f6d8c09976d2fbb0046e56d84b529b348685",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula:527"
    },
    {
      sourceName := "OAI.PiExponent.CurveProductFormula.positivePlaces",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "04ba19c7f1ac58557c69aeb4ac5253d25dc66e103587e22cf9debe4e6020cec8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula:1354"
    },
    {
      sourceName := "OAI.PiExponent.CurveProductFormula.positivePlacesFintype",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "971cb0c51d4d6178123977e64b79d05d4aaf4228a863caaca9095e93c503e91d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula:1965"
    },
    {
      sourceName := "OAI.PiExponent.CurveProductFormula.principalDivisor",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f4609e3cffbccd87d121ce0600773a6c717b5968822aa4573c55b6bf66f80ec5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula",
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
      sourceName := "OAI.PiExponent.CurveProductFormula.valuation_constant_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1c3a8217983d464cc4981d2dc43cf1ab9d5334aeed02ac19bebf7bca844b7598",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula:7404"
    },
    {
      sourceName := "OAI.PiExponent.CurveProductFormula.valuation_pos_iff_order_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9dbb2bf06bb46cfa590e64c7f4dd87c5bf748f6264c4e9642e202506354c06d3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula",
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
      sourceName := "OAI.PiExponent.CurveProperImageDimension.dimension_eq_one_of_proper_dominant",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveProperImageDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "469a07d616ca772ef641d7cf14292d1b2960b91a02c4abe1a1826f67f6c63567",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveProperImageDimension",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveProperImageDimension:1209"
    },
    {
      sourceName := "OAI.PiExponent.CurveProperImageDimension.genericPoint_map",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveProperImageDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f5d193e75273581acc3451226b77afa0765d273c2b83c787b5674a1697c3305c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveProperImageDimension",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveProperImageDimension:301"
    },
    {
      sourceName := "OAI.PiExponent.CurveProperImageDimension.image_dimension_eq_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveProperImageDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "63b25b58566fa174ac32c82f58242c8ae5aaa79af023c0383181907867cc21ec",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveProperImageDimension",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveProperImageDimension:2126"
    },
    {
      sourceName := "OAI.PiExponent.CurveProperImageDimension.image_dimension_eq_one_of_nonconstant",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveProperImageDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fa5a5327b609f35a48da86009791e681ecd2335bd64abb5040cc90070e1e5d63",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveProperImageDimension",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveProperImageDimension:3174"
    },
    {
      sourceName := "OAI.PiExponent.CurveProperImageDimension.image_nontrivial_of_nonconstant",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveProperImageDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1cf2b8761a845e5aa0111699584a0c2989610cd3fcf36630d1224e80dfac2c7a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveProperImageDimension",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveProperImageDimension:2587"
    },
    {
      sourceName := "OAI.PiExponent.CurveProperImageDimension.target_nongeneric_isClosed",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveProperImageDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "faae0532afd31ea575794b76454280ac8dd64bff1aa38bc36ebdd5c60234dc5c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveProperImageDimension",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveProperImageDimension:680"
    },
    {
      sourceName := "OAI.PiExponent.CurveSectionDegree.AffineFrameAt",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      graphKind := "inductive",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "013cec1aa9e18efb9717629fd4e4fa43fedc210608e90e71116169b3a37dc931",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:361"
    },
    {
      sourceName := "OAI.PiExponent.CurveSectionDegree.AffineFrameAt.casesOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5677cc2ca62be934276133e522499d58158b0e2d16afe7832fddd49de5e3a81e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:361"
    },
    {
      sourceName := "OAI.PiExponent.CurveSectionDegree.AffineFrameAt.frame",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "36bd4b156d6022e493183c3c763c61d836ad7c024c4bd249aaf1358cf5140b8b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:361"
    },
    {
      sourceName := "OAI.PiExponent.CurveSectionDegree.AffineFrameAt.mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "baac86b0f5a139d078db1374bf54780f8a1649a1c6c50af45971e0e3f618059f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:361"
    },
    {
      sourceName := "OAI.PiExponent.CurveSectionDegree.AffineFrameAt.mk",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      graphKind := "ctor",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8b038f00a50d143814beb51e220a584d6a46f6732810097bb1e7f9aa2eaa60a4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:361"
    },
    {
      sourceName := "OAI.PiExponent.CurveSectionDegree.AffineFrameAt.mk.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0f0fa670cb6f96e8c2a0d348d5327142638928a42bfcbaa01bafa42e376cbdb2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:361"
    },
    {
      sourceName := "OAI.PiExponent.CurveSectionDegree.AffineFrameAt.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7312e2f51948b01a0df968ddefd8fd8ed6a72a229eaa591e217f33d682f34bab",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:361"
    },
    {
      sourceName := "OAI.PiExponent.CurveSectionDegree.AffineFrameAt.openSet",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "58a4b2626eb0886393104247746ae6472fc80700b166240c9f953a1bf609b558",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:361"
    },
    {
      sourceName := "OAI.PiExponent.CurveSectionDegree.AffineFrameAt.rec",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      graphKind := "rec",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dfb0a29e5e9d8f5caa72a7eaaf335566926ba0dfadd6ecb3eea23e4fafbbd86c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:361"
    },
    {
      sourceName := "OAI.PiExponent.CurveSectionDegree.AffineFrameAt.recOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "53343d9ee44b59610c705c9d80770ad6861e0989c087f08bd86300772308d496",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:361"
    },
    {
      sourceName := "OAI.PiExponent.CurveSectionDegree.affineFrameAt",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e2fb4fdec283ce21034477c4366a51fed8833f92f16fdbb0f521d73e96297a6f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:830"
    },
    {
      sourceName := "OAI.PiExponent.CurveSectionDegree.coefficientGermAt",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "975a9b92c5cdab0acb7ea8ae7ed8fd1801b4175ad5506d291f562c22bff7c77f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:950"
    },
    {
      sourceName := "OAI.PiExponent.CurveSectionDegree.euler_difference_eq_sum_zero_orders",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2f8fb94aa4ce0f941128e435f8f0d28544b744cfddb91befc9f25881833b077a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:1958"
    },
    {
      sourceName := "OAI.PiExponent.CurveSectionDegree.nonempty_affineFrameAt",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "df8da54ca0d5a617c015f821ca039d7b218e0731999276bce8f5cb8a0928b488",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree:540"
    },
    {
      sourceName := "OAI.PiExponent.CurveSectionDegree.zeroPoint_ne_generic",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "129fc78132b066cca0d635f580ab80ab0e053e32c8c0b9575a1c85e917050506",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree",
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
      sourceName := "OAI.PiExponent.CurveTwoAffineVanishing.cohomology_subsingleton",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveTwoAffineVanishing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e98b191271364cfbe6ddae1bd385936c7e34007c81377b1d1c97fd70317351a1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveTwoAffineVanishing",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveTwoAffineVanishing:421"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.NormalizedPlace",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "inductive",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b49daf27e6eb76ce85c5e56816f323ef076d91223e4180e60acb06024f57cb00",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:12391"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.NormalizedPlace.casesOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "58ae96bbc2c4f28a7d2e9593d32f97d7eade328152c5328ec7d3ae1709e6e77f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:12391"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.NormalizedPlace.constants_nonneg",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8fa6fb436fe8b2cca4185d0d3449577078c86c80924a6fce8c93fc40f26acdb9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:12391"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.NormalizedPlace.ext",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "66b8f22cb5e565332e6b360593d0e654a8589cee50965e94614a12a38701d8b4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:12664"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.NormalizedPlace.ext_iff",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f4b2a492a9f3f6ea8f4c4a8d0fabdd9ffb5ee3e36a4ffc939620b1f7cb96dc3a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:12664"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.NormalizedPlace.mk",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "ctor",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a06dbdec6544ccb5b69d0e4c39234b6eaa490edb10e0453ae04fe19933751b64",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:12391"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.NormalizedPlace.mk.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b1cb4ce38d5209173c21adef2462356099df3d6c52a470a8059c69661ccc69df",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:12391"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.NormalizedPlace.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cc5f63dc9891a10b5bc38daf5787ad36a2bd8d98df255f6389044295a4d7df74",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:12391"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.NormalizedPlace.normalized",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3822d4707462df8968f9a18080183c2a955ceda0b791fd1f9926f7b2cdc52891",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:12391"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.NormalizedPlace.rec",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "rec",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "182df821a76cb14cbf1ac1ef75a2e2b59a1650555c4d82baaf57b47c14842b38",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:12391"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.NormalizedPlace.recOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0388ebd52809b20df79ac2c333ee7616a9ec6ba0733dd5051a2f0599caa86663",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:12391"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.NormalizedPlace.valuation",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a285d34c761e2214b2c258463431087499366aabf54ec6ecc221cbce40b190dc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:12391"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.aeval_mem_valuationSubring",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0b9090040b95e4220196c3c413fae420ef242f28e40536895591b9f360f7c2f7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:1104"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.enatToIntegerOrder_pos_iff",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9b3d4a78f098509dc35bf36ab7f9488c57a5c0c9c5707d1e853c32348d23c4c1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:11490"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.finite_positivePlaces",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "de7464f30981fea596025f24e02b1558093cfa2f38fe653bb2792790c1fe257a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:20455"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.integral_mem_valuationSubring",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a81b1fb6dabeeedeb7ec1139946fe1c14835251a6474dcae886a7e9d5050ad06",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:336"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.mem_parameterValuationCenter_iff",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dee809e21793b4f2bb6b26a05dd89500051685b05cf5e6f897619cab5fd69b5b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:3493"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.parameterCenterLocalHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a1f9e81cf65d88123cf9e92334e85d3427e56ccebb595aaecc7d1ffc39b1f33e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:5216"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.parameterCenterLocalHom_algebraMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "75591df01c434e98a4742145a8158c7e1e6a62c9a3ebfb75848e7e2f3acceb25",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:5942"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.parameterCenterLocalHom_coe",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c1e2025dd41d0ebd02381a3d324015dd90485f890e3ccd89493df65aa3bf02b5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:7204"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.parameterCenterLocalHom_comap_maximalIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ec3cb6b65280d923fcead2ad40ca37734c02bbcbbedc8d52ef8111f5cecdf55b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:6391"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.parameterCenterLocal_nonneg",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "65a2315c462c564f3dcaea42d2c5aa3477df82e59d8944d902781d6295030a41",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:8273"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.parameterCenterLocal_positive",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5880247837bbb60dcb1d1159aa9feed628e14f3200c291c831c7e3087b4b76f3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:8938"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.parameterCenterPlace",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e08ca1ec5c4c42fd547511a45c593407336a56f4a5971f54b3031a4dbfe6f334",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:4779"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.parameterCenterPlace_parameterNormalizedPlace",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "de066a221275c1d25e00bc2a02a95f543ecee8c08647430f00609f0f50006703",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:18612"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.parameterChartValuationHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "48dc7efa9ffbe370819b4b08160a4c67473d670e4308bf1b3843b9779c9ec59b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:2283"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.parameterChart_mem_valuationSubring",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d77a4e778894fe7134c1af8d67d44963bccdd7a01d607fd17046cef04eaede11",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:1734"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.parameterNormalizedPlace",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1b8bda5c94157b9595e68394eed0dd5ed55448b172d182255f6dbc034c8fee7f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:17791"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.parameterPlaceValuation_constants_nonneg",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "25f8c3233347d9f02daea389bacc03c7148b2a299ed67bd37f794e9aca34a6ef",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:15461"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.parameterPlaceValuation_positive",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d88c4d9fef05604e94e38abb26fd800f763ffa6e55b67e40d630bdd47b1812f7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:16492"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.parameterValuationCenter",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f5e968aab0deeba6c84b1c61f80d90b261104b81311b7c15b94963e4c1c449d3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:2742"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.parameterValuationCenter_isPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b5d5db0ec2b9f50b365b28b9cb494015ca259907dc2e3157a4073bbfcdeffc82",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:3122"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.parameterValuationCenter_liesOver",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fb77044fd03dc30335a92d012655b4ef5495b9590ea725a3a52b3ab460dc1f43",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:4007"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.positivePlaceEquivZeroPlaces",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b4544e8ce3570fb02f0b1b0621131968af7fcf0f8571abc89d00bd1ed88453bc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:19726"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.primeFieldValuation_algebraMap_localOrder",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ea755fb6f987a4fc53f476f4a3e07fa5c33144749cc47b3f62f561b6ad87d823",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:9818"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.primeFieldValuation_algebraMap_nonneg",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ef60ac7bd8a51e2ed9561810b0e365737c750cd0f23036d00e4f631d6dc188a8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:11076"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.primeFieldValuation_normalized",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "805b9caaba6fb54a6c7a0c96b24d6b532aae0d55643962d832fe0de595f00f73",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:14601"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.primeFieldValuation_positive_iff",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ef94b9784555a4ada7f7167bdc9a10b3c5d7aaa5f4f0b5831c2e160b687b223a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:11732"
    },
    {
      sourceName := "OAI.PiExponent.CurveValuationCenter.valuation_eq_parameterPlaceValuation",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c59519adba995ebe28f4f49ba00daf5ee1397967aad5a9110891b231ad52f93b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter:12874"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.adjoin_inverse_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3e8eb8e5891f76dac4433b6626de6a62e7ea0dd57406c7be7121b0e137c059e7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:2331"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.baseParameter_nonzero",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6819afd473b165c7a4e253041480d7d6f6366bb2dddcbbfe9920e3fd96a4c3d9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:15764"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.constantCoeff_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d1caae8e22b6a8c2285fd98e3af7267213ab350c539039521933d4a193e1b016",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:7608"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.fiberDegree",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f7e8dd405aedcd1b760ca454ea552e64cc46ea319b2e1a62e0d9e3454931f554",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:536"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.parameterAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a7488a2cc3e4e35f72334afd5076524b2dd404d94f7c2e1fcdbee770b145e04b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:3651"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.parameterChart",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "554eba76f277e7511d87d36c7f722f2084074b64df62f86dac8f2d27a915b079",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:20257"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.parameterEmbedding",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "69e78f1f513f647e45f560067ba18dc3af349ac4ac31f9e936481c405bf3c0b2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:3190"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.parameterFiberDegree",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d7eb0a91d4629f07524357dca5b969a1050cb3792ab05870ec0c972c01f111fc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:5767"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.parameterPlaceValuation",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c2b9de6969beb6edab848bd7efdded9c3f905fe01a48105166d70d3763dd393b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:21189"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.parameterPolynomialAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ac300544d890795cbc06646061ca43fcb28564ea92daff73b17bc476ec063c65",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:4807"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.parameterPolynomialAlgebra_map",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0234f52de28fb1a4782baa3e81255009e46c7fe09458e1a03c58dc9d5b26431f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:21888"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.parameterZeroLength",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "51590c2413fc35de014d49dfed0bdaf6c3495fe9311dd84e7ab1e16026f3fc07",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:10218"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.parameterZeroOrder",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e362567b92f532989adbe7c1ff53e5fd7e3f9443b75d93b80d1d72bf89167b83",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:18310"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.parameterZeroOrder_eq_sum",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8c6bf2e56fd220528db1b10514e8befd6d257ca4aa801ef686c64c1aeddd9ee0",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:22478",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:22478"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.parameterZeroPlaces",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "17e58e5fbb7a13423db88c11fe383902d4a52884e935c52a90f498f1369bc184",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:20458"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.parameterZeroPlacesFintype",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "356c30b280aa985e8eb31e6415357a7433d2843abff3e1cab9a4572b9fcf16ce",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:20678"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.parameter_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9b5bbd5509fae2837c9f1fcb42e860843247e089852dada0c17233986b4502be",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:4243"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.parameter_scalarTower",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3e6b58bef9390a26b0f1ff7c3c87962572e4ef45670004ddf5c8b77838be7b50",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:5037"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.primeFieldValuation",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4ccea6215d11d380716e88de8479ef984e0ce93f722913a82f4aca25a6d81ecb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:11882"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.transcendental_inverse",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bd9ed53df00d9987036031a20b3ad3c01fa5acdee0b57e17d4eaf17a0e0fb995",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:6741"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.zeroFiberHeightOne",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e17bfb741cc5a835b738d77a694b37b349c568e4f7e14e2774155f51d84e2031",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:15487"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.zeroFiberIntegerOrderSum",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ad37cb0c9c35b5716a0c0ed5e78b3b62f9c3456254c075f82f2ce46ac627afb8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:16242"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.zeroFiberLength",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "02112d2ed7e4ef08876cc9a0070808f9632e534504ffc3f49c660592e2b845e1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:8822"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.zeroPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "de006358f975e2928216f3f396debd62d600364af5c76f3336e174cbc44c0f1c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:5413"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.zeroPrimeQuotientEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "510d7379c4076626254f39af6a5521b8b6abb9a5d9c1e015e90457051deaa7b3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:7967"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.zeroPrime_eq_span_X",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a27b3889719eb97fcc57ab60898fa2997b07edc5c63f59c5cb6f4ed63e5b509f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:5635"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.zeroPrime_isMaximal",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "45c57e299b8a7c1797dc6c01c267e017c3ea5fe59e72aad1219b5cc7997b465a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:7791"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.zeroPrime_isPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0ee5954ee71b7138130a1278b23312eecd3209283212bfe08153e5818ef93f5d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:5508"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.zeroPrime_ne_bot",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a27db56e47a4ec1466f3c6104d305bee54ed503236f934d359baf63cc3c03b8a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:15216"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranch.expansion",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranch",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "595dd38b31deac5271e3cf0790a2d0b42f0d92f9c29dd7bf565a44b1f4bbeb04",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranch",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranch:1336"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranch.expansion_constantCoeff",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranch",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5e9ccc64c6454893fe9f715cd9c3755ddee579e54e69c18d0a41100bc827a677",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranch",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranch:2141"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranch.expansion_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranch",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7a76f567a9134b3cdf805010c7a029faae9bc2cc0603ceb202350d894ad212f3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranch",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranch:1942"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranch.expansion_order",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranch",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "585ac84fa9f9d820256b203e96d8e85f3f1b3d3f0db37eb6c4d629db7c70156e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranch",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranch:1688"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranch.expansion_uniformizer",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranch",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f8e9a13166eaacf951963aa78992a10c44374171d07a73ff838a179561605d39",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranch",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranch:1541"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranch.residueCoefficientMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranch",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4bac5aeb10198c53eb4734a90c1cc002a975ea2078fefb0a3bf58eb7ea1cff1e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranch",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranch:396"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranch.residueCoefficientMap_ker",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranch",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "976adea9d80d7aa2b654dd4326816b701f5036c4792bcc173691826310e5f631",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranch",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranch:538"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranch.residueCoefficientMap_ker_span",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranch",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "90bb40a0969098e68ad12ca0d2e4c182a58f86c45efb28d3ab48a5a11d70eabc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranch",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranch:1123"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranch.uniformizer",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranch",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ffe104b200499049d55eb60a8a639bc25973374f72264b15ae4c0628575ce38d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranch",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranch:893"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranch.uniformizer_irreducible",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranch",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "614be130ce726ab77f209231fd8075da4a071f6be51dfeed9476be53e1ddc1d2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranch",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranch:983"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.coeff_expansion",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d66d87581718c7b564973c46ff58dab04404abbea490b250d577da03af0d28b3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:3166"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.constantCoeff_expansionHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e5237b645134a0baaa491c6c29d7d18ae85a8a723e5a6c6637b0f72d19539a8b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:6805"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.expansion",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "167e90d0004a5e724bb1573a5cd5ccf8ed9d2afc41c91eb08cafb85453e6876e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:3062"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.expansionCoeff",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fbd70e6f831e73689e8f17fbbbe54e5eab16d17cea3fe220b374a6ebe3879464",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:2233"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.expansionCoeff_add",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e69d6c84db94aa316eb164feb8e3dc343012178603d9a47a269cd88f32dc1a1b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:2664"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.expansionCoeff_smul",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b6b3e529895570c215147b07f6a478b34e038f90e004e9740c494eaa5bb00f2a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:2877"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.expansionCoeff_succ",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "86558c878a77de55ba0d8be373e6c83da07e094cad31ca5b6ce35be814bb8261",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:2421"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.expansionCoeff_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "22e214fc7ed023d199bf36c35aa0fa7feb0fd1dc1130c3b1376a637615e459ee",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:2324"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_006.jsonl"
