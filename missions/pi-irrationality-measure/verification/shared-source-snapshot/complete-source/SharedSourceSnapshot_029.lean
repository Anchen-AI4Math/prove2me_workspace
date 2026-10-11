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
      sourceName := "OAI.PiExponent.primeLocalDirectional",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f8b110f79e5faa72c4e61716a0b887f050ce2da13a9eb666d6a745e2ba45b135",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent:4615",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent:4615"
    },
    {
      sourceName := "OAI.PiExponent.primeLocalDirectional_polynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeNormalKernel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "77a55d2c2de68d021c4b5313127a147a4f6fc34f63c3f4001ae20d82c3263867",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeNormalKernel:234",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeNormalKernel:234"
    },
    {
      sourceName := "OAI.PiExponent.primeLocalPartial",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ed0f8f6fcef2901576ed591c4b0b656c9b26fa6aa9ac9444a354f69da13f81c0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent:1827",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent:1827"
    },
    {
      sourceName := "OAI.PiExponent.primeLocalPartial_polynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "548d89b0031c571a0722570e35e91de9e1fe33f703460461fb39614a49f2a866",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent:2185",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent:2185"
    },
    {
      sourceName := "OAI.PiExponent.primeNormalPairing",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c258ce972788f4243edee424ac750917cd8b368302b0c6949fbd8e0f1654642b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent:2978",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent:2978"
    },
    {
      sourceName := "OAI.PiExponent.primeNormalPairing_ker_le_tangent",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "adbf0ff8b3a4ad97b6880b65ff02ba916d7ff1f6d5532dfb8c4ab8d11c5ee1bf",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent:4127",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent:4127"
    },
    {
      sourceName := "OAI.PiExponent.primeNormalPairing_linearIndependent",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f50fd6556accb0bc1d76061495566bfc393ca6b8d42bb6b522c73b64d2d55a3d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent:5368",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent:5368"
    },
    {
      sourceName := "OAI.PiExponent.primeNormalPairing_polynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2aee10be7ae99c383ec9dd23dd0bdb1bf506a1a3d471b2d6a54281c1a48e3456",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent:3597",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent:3597"
    },
    {
      sourceName := "OAI.PiExponent.primeNormalPairing_toCotangent",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3b19e03f767645f06e0fe4b9568df3791577b9ea86f555532386fc8b8fa81d42",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent:4775",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent:4775"
    },
    {
      sourceName := "OAI.PiExponent.primePartialNormal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4c942cf84c0fd8c028ea2056dde8aeeac2af18d0164cdde697c3263ca421993d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent:2750",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent:2750"
    },
    {
      sourceName := "OAI.PiExponent.primePolynomialCotangent",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c57af2ebf262fcba389dda96d530ba01d4e14b68a6c52ce2760b7ad6d3972413",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent:3297",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent:3297"
    },
    {
      sourceName := "OAI.PiExponent.primeRectangular_maps_maximal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PrimeTaylorCotangent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5f442215085963f6991c6edbe7c3873273f0e36f6c0cddf99516f810c859603c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PrimeTaylorCotangent:419",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PrimeTaylorCotangent:419"
    },
    {
      sourceName := "OAI.PiExponent.primeResidueMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "118697b7b6ab1b97d205706562044b5ebb7fb6621b14dfb4d3e5e0836bed8533",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent:1693",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent:1693"
    },
    {
      sourceName := "OAI.PiExponent.prime_cotangent_evaluation_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bddc82c08874916276573fe9004aa4fad23a5f045d711c94bdb6fdf37d278be0",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent:6240",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent:6240"
    },
    {
      sourceName := "OAI.PiExponent.prime_frame_rectangular_length_lower",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeFrameMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "52014b1a0052858fd8b625f6d71c8762146478aea617d0a188702cdbb78b3d53",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeFrameMultiplicity:415",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeFrameMultiplicity:415"
    },
    {
      sourceName := "OAI.PiExponent.prime_localizedTaylor_firstCoefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PrimeTaylorCotangent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "00e5446e1a8fafb58db32eafab0e46f333541f1b44ef55f76ddb2dbee8d132e7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PrimeTaylorCotangent:2586",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PrimeTaylorCotangent:2586"
    },
    {
      sourceName := "OAI.PiExponent.prime_rectangular_mapCotangent_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PrimeTaylorCotangent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2b465d4e38620e70455da81f48423ef3cbf4d5957c300779689b604032bbbf64",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PrimeTaylorCotangent:1120",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PrimeTaylorCotangent:1120"
    },
    {
      sourceName := "OAI.PiExponent.product_dominance_of_lower_indices",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparationProducts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ecbe1272c2b354e930b0df0698f6fc2c72bd83f03b8c408657a5561e1fa3a6c4",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparationProducts:199",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparationProducts:199"
    },
    {
      sourceName := "OAI.PiExponent.projectiveGenericPoint",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveDenseChart",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "892e305475e2c616b62c3f617047efbf014ea1b999a25a8603424ac6787ecc34",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveDenseChart:356",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveDenseChart:356"
    },
    {
      sourceName := "OAI.PiExponent.ratFuncDerivative",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.AlgebraicLogarithmicObstruction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a2f5aa5c7be533cf2469f856b386850adfef183ab701bb931f73853729c96846",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.AlgebraicLogarithmicObstruction:1322",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.AlgebraicLogarithmicObstruction:1322"
    },
    {
      sourceName := "OAI.PiExponent.ratFuncDerivative_X",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.AlgebraicLogarithmicObstruction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b044f34f3c60923f64ece07562e816edc071533ec16dfbe32d0a60b9a1abd108",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.AlgebraicLogarithmicObstruction:1570",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.AlgebraicLogarithmicObstruction:1570"
    },
    {
      sourceName := "OAI.PiExponent.ratFunc_derivation_ne_simple_pole",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicObstruction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e013f0c9beccb36a0e3cb7368baed09634af074d84fe1f9a801d2a4393d286f1",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicObstruction:3140",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicObstruction:3140"
    },
    {
      sourceName := "OAI.PiExponent.ratFunc_derivation_polynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicObstruction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "52dcd9bf1ac9b461f6bad87bf1d2ef0be099829bc0f485589c1f194a80c4d719",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicObstruction:2805",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicObstruction:2805"
    },
    {
      sourceName := "OAI.PiExponent.realWeightedSimplex",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "350f9e7abdb193382b0ec5588da613ef47e9087e3d1e7b88292d3f1da317619a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:6443",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:6443"
    },
    {
      sourceName := "OAI.PiExponent.realWeightedSimplex_scaled",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "530ee9d98e40c5db706a5eb10a02aca9cb5412e7306f2142087a777c20204f8d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:7939",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:7939"
    },
    {
      sourceName := "OAI.PiExponent.reciprocal_sum_le_common_bound",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightErrorMargin",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e4f9002649baf06da3a6325e3da7d72953039c80c455fa83dee0ec80e22b97b9",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightErrorMargin:804",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightErrorMargin:804"
    },
    {
      sourceName := "OAI.PiExponent.rectangularCutoff",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "680fa678c00673d3b7023b5a008f7469e98cc0e142888445440d6ce7b4012226",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume:122",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume:122"
    },
    {
      sourceName := "OAI.PiExponent.rectangularCutoff_coordinate_weight_lt",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "da49c7d4f0c2b5fd74bf12778a528ee8700997ede9d93756e6e8657cbd8affbc",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume:1537",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume:1537"
    },
    {
      sourceName := "OAI.PiExponent.rectangularCutoff_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e9e022d9d07453da9b8d7b41ff0eb626e5c7406377b6699200f88860b399a6fe",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume:258",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume:258"
    },
    {
      sourceName := "OAI.PiExponent.rectangularCutoff_product_lower",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "07b0058ab20a268d4cc5f6df2974435e2bb88ca0494caae8ac7121b49fbf958e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume:2927",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume:2927"
    },
    {
      sourceName := "OAI.PiExponent.rectangularCutoff_weight_lt",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5323b915bbf957691b4b43cd0d09437043213775faac40d1f109be9827b3d6a2",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume:2104",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume:2104"
    },
    {
      sourceName := "OAI.PiExponent.residueRectangle",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e95203858fdc52a3d7d2d4cb1550fdd0dd580e94d7c480d13c886160d33176c7",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:1021",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:1021"
    },
    {
      sourceName := "OAI.PiExponent.residue_polynomialFrame_eq_frameBasis_dot",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameResidueDirections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "85c7470f7c52da32af876b607f01bcadb1e0e7666ade8e32be2093d0bf6fe557",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameResidueDirections:259",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameResidueDirections:259"
    },
    {
      sourceName := "OAI.PiExponent.reverse_logWeights_prod",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SuccessiveApproximations",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c1d3a2baa0fadcdf830d939e9783e5ad29875a7b890e3c4e8b5f3c723b037121",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SuccessiveApproximations:3805",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SuccessiveApproximations:3805"
    },
    {
      sourceName := "OAI.PiExponent.rpow_neg_le_exp_ceil_log",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ApproximationCenters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0eb50d812d03e1f589a87dfd2837cf94d719afbc6db10994841438159a2757de",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ApproximationCenters:2225",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ApproximationCenters:2225"
    },
    {
      sourceName := "OAI.PiExponent.simplex_count_lower_sandwich",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "32550919c6a092b470e3882ead26d4db3780d662f8eeea7df5bbc198c495ca0a",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:1506",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:1506"
    },
    {
      sourceName := "OAI.PiExponent.simplex_count_upper_sandwich",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3be5d197c182f42e1ef1b28687c97b8527ecfe640d86659f6b56dfa96d9e9f44",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:2826",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:2826"
    },
    {
      sourceName := "OAI.PiExponent.specMap_stalkMap_isIso_of_isLocalization",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FromSpecStalkLocalIso",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "72c7cd7171c21f3254e0f545ffd39be9452e5c6f704b803c734b006daed74a38",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FromSpecStalkLocalIso:163",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FromSpecStalkLocalIso:163"
    },
    {
      sourceName := "OAI.PiExponent.strictWeightedSimplex",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "509ba2c89601bf4b66d6dc9eb6f9989d284493cda0e870d16af28d904f07addf",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:6702",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:6702"
    },
    {
      sourceName := "OAI.PiExponent.subringGrade",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedSubring",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8016e0fac12384c6d895adc8cd9a66db58504d68d3a90779bab2ddac8b916bb3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedSubring:250",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedSubring:250"
    },
    {
      sourceName := "OAI.PiExponent.subringGrade_independent",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedSubring",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2f48b7e3854372fd2982a949a96264ca31afd45303a9782ac11b560614734645",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedSubring:359",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedSubring:359"
    },
    {
      sourceName := "OAI.PiExponent.subringGrade_spans",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedSubring",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "122c750d088ce1c039ee1e90c0f190a63f72f67835d6c03a643ade86091f7e17",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedSubring:955",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedSubring:955"
    },
    {
      sourceName := "OAI.PiExponent.subringGradedAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedSubring",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "037bdae973f27e26a62eb29c6eed779e9a7be3eda1f41c5926a36bea80f32739",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedSubring:1617",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedSubring:1617"
    },
    {
      sourceName := "OAI.PiExponent.tendsto_card_natWeightedSimplex",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e76a614393c0b41d06d2b460c406de4461fc3b9192f368e1e67781009882b5b8",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:5000",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:5000"
    },
    {
      sourceName := "OAI.PiExponent.tendsto_card_realWeightedSimplex_rational",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexRational",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9656856d850b653f78ee7c151ad1e7c08e72daf7b4b31ca522cf721830d9b0c1",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexRational:999",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexRational:999"
    },
    {
      sourceName := "OAI.PiExponent.tendsto_card_realWeightedSimplex_scaled",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7e194929217dea4a0883488afe790553f6cd33d5100ee60f591ecce7f5bf9847",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:9279",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:9279"
    },
    {
      sourceName := "OAI.PiExponent.tendsto_card_strictWeightedSimplex_rational",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexRational",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "77b032f8d7d8cec774a72df7bdf901b0f9874bbc0c97d14504e1dcff15f7d5e3",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexRational:1596",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexRational:1596"
    },
    {
      sourceName := "OAI.PiExponent.tendsto_card_strictWeightedSimplex_scale",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.AuxiliaryPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ea8363ec9a78794062902657e4eac10ef8f7a6b8a31c7250df88f2506868e33e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.AuxiliaryPolynomial:3944",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.AuxiliaryPolynomial:3944"
    },
    {
      sourceName := "OAI.PiExponent.tendsto_card_strictWeightedSimplex_scaled",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9bcbdf73c502b767e770d56544588cf0a1eb5aa8d8c8d9b688430f08199a8a0f",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:9837",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:9837"
    },
    {
      sourceName := "OAI.PiExponent.tendsto_card_unweightedSimplex",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "17367159d1d669fdcb3048f40adc9a3c33be399837c0dd543c17787fcdb6ea89",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted:3702",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted:3702"
    },
    {
      sourceName := "OAI.PiExponent.tendsto_card_unweightedSimplex_add",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9d0d7cae99aac1178dbcce1f818f7d9cf238d7e183f7f3d70ac51e58cd8c1bb0",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted:3970",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted:3970"
    },
    {
      sourceName := "OAI.PiExponent.tendsto_choose_add_normalized",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f3154e730a3708ea4887f24837dff71fb9b443a979db28c15dfaa5f549aec9d5",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted:2924",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted:2924"
    },
    {
      sourceName := "OAI.PiExponent.tendsto_choose_normalized",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2bc3f7569452caa6d03f6293b22fedece8d6b13903a9e0ab03a5dcbee8eae397",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted:2321",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted:2321"
    },
    {
      sourceName := "OAI.PiExponent.tendsto_collisionRemainder_of_normalized_pow",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.Collision",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4eb4098f2655b8394c8fd486f33dd15664afd8f3e478dba2b429e8e01b59f844",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.Collision:2609",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.Collision:2609"
    },
    {
      sourceName := "OAI.PiExponent.tendsto_dimension_collision",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3a47a2e00d232e268750f1ab684015e6658ac21ae46336cc1ef125386a4f3a61",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:5582",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:5582"
    },
    {
      sourceName := "OAI.PiExponent.tendsto_dimension_error_majorant",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e809a217631d2200b9bc510a00d76f3891de12b4f34e72f0c9fb3436b8cb8b93",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:4772",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:4772"
    },
    {
      sourceName := "OAI.PiExponent.tendsto_log_add_div_of_normalized_pow",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexLog",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0b5d150d25d237784b1f00b53dc1ba48d88a5f18fc1fee3b1d15c365cb1ce9b3",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexLog:1069",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexLog:1069"
    },
    {
      sourceName := "OAI.PiExponent.tendsto_log_div_of_normalized_pow",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexLog",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e765cae5ae5ee9a5ab96fcc46444d29f413cc25989919d685dfe168b04e954c1",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexLog:157",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexLog:157"
    },
    {
      sourceName := "OAI.PiExponent.tendsto_log_translationTermCount_div",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.TranslationCountLimit",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c1bd3775215584caf310d1cc82c1cf0ab524f3dcc3364f466f4a848487fceba5",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.TranslationCountLimit:1505",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.TranslationCountLimit:1505"
    },
    {
      sourceName := "OAI.PiExponent.tendsto_natFloor_affine_atTop",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexFloor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6a115ed6ba4a6ab3667260e0cf20d104ec5ce7cb428826aca63459718f295837",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexFloor:115",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexFloor:115"
    },
    {
      sourceName := "OAI.PiExponent.tendsto_natFloor_affine_div",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexFloor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a645952e449e46d2e1bf4b93d68de9a0d9e8329301bb6a5661f89dffd85f99c6",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexFloor:372",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexFloor:372"
    },
    {
      sourceName := "OAI.PiExponent.tendsto_natFloor_mul_add_one_div",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.TranslationCountLimit",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1744b64415c70ea8206265fd8b9602869d70693373d378a016b4b0f04fa18ff2",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.TranslationCountLimit:313",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.TranslationCountLimit:313"
    },
    {
      sourceName := "OAI.PiExponent.tendsto_nat_add_one_div_pow",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.DimensionLimits",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "04ff41ea53ef48b255485ee74fd10dbcaaa0681cb6049318860da58a100b4412",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.DimensionLimits:115",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.DimensionLimits:115"
    },
    {
      sourceName := "OAI.PiExponent.tendsto_normalized_natFloor_affine",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexFloor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1aa63b34e5cfa5765689216c94242e1cfddd918e86a7b33f18cdd6e602ac375c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexFloor:1383",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexFloor:1383"
    },
    {
      sourceName := "OAI.PiExponent.tendsto_pow_div_nat_add_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.DimensionLimits",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d192258e7e163e75d2aa456208b667e8aff6babf468f75487dd352bb63f37c53",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.DimensionLimits:458",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.DimensionLimits:458"
    },
    {
      sourceName := "OAI.PiExponent.tendsto_translationTermCount_normalized",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.TranslationCountLimit",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dc8143062543b3815c51cb9509b6cbf0b4a18f999c393c0fee8f58bba7dab249",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.TranslationCountLimit:640",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.TranslationCountLimit:640"
    },
    {
      sourceName := "OAI.PiExponent.totalDegree_pderiv_lt_of_ne_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialNormalNonzero",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4975286430a0d453d14c003fc7941e029aaf5d42ddf510c3eb2ac6df46324151",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialNormalNonzero:186",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialNormalNonzero:186"
    },
    {
      sourceName := "OAI.PiExponent.translationTermCount",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.TranslationCountLimit",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0c7896882e41a877f297b07b7f4362dccc7f0e1dd4a11370a28470c3e84f582c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.TranslationCountLimit:187",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.TranslationCountLimit:187"
    },
    {
      sourceName := "OAI.PiExponent.two_le_rectangularCutoff",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d716a86b4d00c902f5045bc2dc0c266f25a18f8bb615c4980d2212733655416b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume:559",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume:559"
    },
    {
      sourceName := "OAI.PiExponent.unweightedSimplex",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "038ab30ff7c2537f5dbb153ad137d4922b0bcdd3e92eaaa581ef2a4303a968ab",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted:168",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted:168"
    },
    {
      sourceName := "OAI.PiExponent.weightErrorCoefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "322c4bc9061dd34804a634f9cd9814ce4f61a73741c1d6b5beef10ae5177516f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:939",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:939"
    },
    {
      sourceName := "OAI.PiExponent.weightErrorCoefficient_nonneg",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "edccb9d4588db630233d7f04ce37d332c056a1bcba69a15077f466439d176c33",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:1102",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:1102"
    },
    {
      sourceName := "OAI.PiExponentApprox.FramePolynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d88fadc83b3ac8ead76e1aff1472aa2752c2a572d8d01766f330be8a2af8e327",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame:251",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame:251"
    },
    {
      sourceName := "OAI.PiExponentApprox.HasWeightedDegreeLE",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3362a18e5d51e6ddf686b09a93ebf6931988c7b35cf5775efb34c0c353216e69",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:303",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:303"
    },
    {
      sourceName := "OAI.PiExponentApprox.HasWeightedDegreeLE.X_mul",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4204ba343dc70a89f4bfb3c10568072d290ddf9f0c32afc73f86dd892c488add",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:3146",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:3146"
    },
    {
      sourceName := "OAI.PiExponentApprox.HasWeightedDegreeLE.X_mul_pderiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0907538fcbfd918f839157c57d341ae39ab4be378a0eeddc24c6d261a7b3bf61",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:3692",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:3692"
    },
    {
      sourceName := "OAI.PiExponentApprox.HasWeightedDegreeLE.add",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "103a2bf3155dcd580208d6f8962ac658498056e4d926e0e44b486f3638eeeba4",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:1386",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:1386"
    },
    {
      sourceName := "OAI.PiExponentApprox.HasWeightedDegreeLE.logarithmicDerivation",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2233f4681383889a2b8dc3605e4c7e0f4181afb66f47f3d265ef3f42e1cbc84a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame:4904",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame:4904"
    },
    {
      sourceName := "OAI.PiExponentApprox.HasWeightedDegreeLE.mono",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "de87bff23abf78a87b11fbb58436e33bc87dbd45727852243952e3a9850d4148",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:1140",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:1140"
    },
    {
      sourceName := "OAI.PiExponentApprox.HasWeightedDegreeLE.pderiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a7971ed83d60f91a0e034a3b00b4b1daab8a39e227e550671b335f8f5b243b1e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:2712",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:2712"
    },
    {
      sourceName := "OAI.PiExponentApprox.HasWeightedDegreeLE.pderiv_preserves",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "95981be8a7715db650464fe1909f6e24d79667e6758da0588ff24e8a4864678c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:4016",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:4016"
    },
    {
      sourceName := "OAI.PiExponentApprox.HasWeightedDegreeLE.polynomialFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d268c61710b80ca9c77d4f64ec28f9804572b5e4933188e87a3cb8a3982f0ca1",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame:5349",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame:5349"
    },
    {
      sourceName := "OAI.PiExponentApprox.HasWeightedDegreeLE.polynomialFrameWord",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4147ad07ab40f8b23f07588be788c83977c31e39767e6728e8f8629cf62c3d87",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame:6761",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame:6761"
    },
    {
      sourceName := "OAI.PiExponentApprox.HasWeightedDegreeLE.sum",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7db2c2a0cc1ed1d981bfcf01cbcfe4e1f3469e9d89a939a79a0885a6667e34a3",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:1754",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:1754"
    },
    {
      sourceName := "OAI.PiExponentApprox.HasWeightedDegreeLE.zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "29295d8889b92748852be70073e15298451c39c042e52c92d5b32208fedbd9f3",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:954",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:954"
    },
    {
      sourceName := "OAI.PiExponentApprox.SeparatedWeightGrowth",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3f4c737c6a3a7b54f4c5083cb137eda92fa06e4fc75472c942ce6546c838117e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparation:4666",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparation:4666"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.RectIndex",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a11d469125951e4afc5cceacb9d3bc4c2de65365624336a194da526e3cb5f06e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:569",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:569"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.RectangularRing",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "57463454d27842b808868170d74afbd08d84628135494cd0db4116703aaa3362",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent:353",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent:353"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.card_rectIndex",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8a795d8b20b683e325dfee3366d0c93c3a3417ccabe5e653de4a197228d7a82c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:4073",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:4073"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.finrank_rectangularQuotient",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "13bf76069dac54a9fa70ebd2fefc384ce7271f8cad1f50cf913bebc1045113d1",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:4450",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:4450"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.firstCoeff_mul",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7e7db475d204270f793c1f28cad96b6cfcb0fa9e4e0b2d08e20328aa110321bb",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent:1874",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent:1874"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.length_rectangularQuotient",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9ac1269aab47a644db19377833566248e80fcc98baadbe4a9a15b4f9389c289e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:8344",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:8344"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.linearCoefficient_mul",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3ed3a8469fc2fad45023f6d460500a255b7a3fdf14f7434265499a0fe4396c24",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:16819",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:16819"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.localizedTaylorMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f77d2d08e8faa9ee411d58bb5b6ee0b439a6d65cdf5ef54d9eee3fe8acb886d4",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:15304",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:15304"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.localizedTaylorMap_algebraMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "91b968cb7d34af3cdb4659524000d990508d6b7eb16ef95edd5677e7901f985d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:15790",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:15790"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.localizedTaylorMap_constant",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d9685934d7e5b776d05d69bae02c7462b3dc3c78adb7b508d5917dfe3de5b98b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:16257",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:16257"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.localizedTaylorMap_ideal_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6678bb550424bc686b4af9fba28e5abd826b5a9d5f0bc35d8d27b6d73ed0b889",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:18905",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:18905"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.localizedTaylorMap_linearCoefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6ce1ae6755960acd216b07bc3cac2d752d4bd67ebec165254fbdbb7bcd2bd245",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:17393",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:17393"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.ordinaryIdeal_le_rectangularIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ce3b6f7c62f47618eb7cb84c863b3030542c01b105ccab042d1b465f2c2212dd",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:5995",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:5995"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.ordinaryOneIdeal_eq_constantKernel",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1c9eee8bb627b4e2cf6d42c711546257c93a9778192a95030e895b3fcca786eb",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:6443",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:6443"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectIndexEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0fc9e12260154a314e9fbb4b477ffe79e36873d6e1023b438a591b0df5037962",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:3559",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:3559"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectIndexFintype",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d29596ae273761760216c7b1a3bef23f63d8695f43c3bac08d35b982767eb278",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:3938",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:3938"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularAugmentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "25d517ee405bdc8fd8b16503c24b6e2200919ea807e6a5f83bd1acfec2d31678",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:4716",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:4716"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularAugmentationIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4a0734f4f1025e7647e0299dd3fd36c7a6c84e2832a27143a5e0d8c7733fef16",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent:632",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent:632"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularAugmentation_algebraMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fca76420303913b08c97fd16d2778fe5e28bd4b0317158fff1c45a56a4092667",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:5292",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:5292"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularAugmentation_ker_eq_map",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fdba32811392be1cdcf43eda4ceaa14cd124f6ff72d909756694047dfe735e5f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:6777",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:6777"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularAugmentation_ker_pow",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c01eb3876d4e5e0021bd5ba0f5e17c06578efd2139e57035ac826e56955232c3",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:7443",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:7443"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularCotangentFirstCoefficients",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f70865191c072535e1d84f12528ee0410a638e5be800bfb0900c1e7cd553818b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent:7233",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent:7233"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularCotangentFirstCoefficients_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a7b2095d10e8a1a6aaf58259ba2d4ae6d911172cb69e8630c5ba504d669d5cde",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent:7914",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent:7914"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularCotangentFirstCoefficients_toCotangent",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "94fbc8e39cfcbcb4a454a286787f7cced3a739029e826046cfdc7d2703ca9730",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent:7529",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent:7529"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularFirstCoefficients",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d4c424984d2c131b064247fe5b3db6beacaf7d49f38d687da68a9d8b126cf58d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent:1138",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent:1138"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularFirstCoefficients_mk",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e99d93ceab40800bc641b57e41432079f48781dcbc7d0d354736c6cf34bac561",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent:1572",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent:1572"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6cfd8012a9c05af95d1c36e0a3626bbc4aaea99ff643e2780c208057a1c77e0f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:646",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:646"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularIdealFirstCoefficients",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6916cb44a2fb22bf10ad962403e0fa32425a54573b9d768008497331175e00cb",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent:5960",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent:5960"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularIdealFirstCoefficients_mul",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "86b5724ea1e188a124ed570a9d6b97758b82b3323f7d21079f146ef7e18b6a8b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent:6247",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent:6247"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularPacket",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0f8bd9258536dd7381366bc314b0ac1a9fb7736927fbe857520af9d3a535879d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:1318",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:1318"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularPacket_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2aaa7fce012ed96304f97af5f23142ac528dd16561feda235db0ca2941da7a10",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:1552",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:1552"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularPositive",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d92f0a6fbba59063eb4895b0a13f8b3ca5a970af3d8e3f0406b4295c636ab4a7",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent:453",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent:453"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularQuotientCoefficients",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eee503db8eb88e83c05a16b094c61b35a7720d64a553a5b8b88938e31fe4f9a9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:2029",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:2029"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularQuotientCoefficients_bijective",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a3099c4f206bb91a730ea20fc9c8b328740c3acf5d54cd0d07a0aa15d443d56c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:2661",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:2661"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularQuotientEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d5979a3a2293c8b3b919b6cf7aaa449b2b071e97bea0880cc30ee00c04c121a7",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:3303",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:3303"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularQuotientFinite",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "607c9cd75a5ca4ceeb90926f2a1c3339cdb6dbd4c6675d552a3033f7fa0823fc",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:4259",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:4259"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularQuotient_isLocal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1d4a9029a9f245f27cd0ebb8f90eba720f1259e37c7b6aea1189a3ea7ba523eb",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:5629",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:5629"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularTaylorAlgHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "81943523125ac1576101207d3d013839336273385883c7c0514076aed93ebecd",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:12595",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:12595"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularTaylorAlgHom_augmentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "66b0d6e477455475489f38d2b52a6d871c5003fc2f313247b6e9620503237f05",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:13202",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:13202"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularTaylorAlgHom_maps_residueIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a05096b8bc92229bd3b00094fa2ee160e8a89eb13668e1afa346f98801ff366c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:13630",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:13630"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularTaylor_length_lower",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "22f1c3ccefaeb803166f0e7736ea4bcc2d72b944593b6c55283a34858fcb99a4",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:14169",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:14169"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangular_mem_square_of_first_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0a54576b949058f4ebf1f22f13e61a0fe12ca81bc57f068d51afc8384312702e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent:4836",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent:4836"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_029.jsonl"
