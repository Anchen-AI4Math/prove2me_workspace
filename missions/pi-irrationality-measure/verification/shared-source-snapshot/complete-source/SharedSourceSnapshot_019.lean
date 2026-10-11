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
      sourceName := "OAI.PiExponent.NumericalAmpleness.eulerSlopePolynomial_pos_of_ample",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.NumericalEulerSlopeInputs",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e5cee02cb99f7a84c0c126207b87780b0cedf4fda27f9d3d10e23a8ccf7aaa75",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.NumericalEulerSlopeInputs:407",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.NumericalEulerSlopeInputs:407"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.euler_power_dimension_difference_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerPolynomialDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fbb2a2b7f4f47a4e69f4fc60210196542732d321d8eea4ba430dab8e94e17ac1",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerPolynomialDegree:9018",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerPolynomialDegree:9018"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.euler_tensor_power_difference_aux",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerPolynomialDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9ba4e36e74c284349d45840b683aacd1cff5ca00da0bebde369993493a147e90",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerPolynomialDegree:2356",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerPolynomialDegree:2356"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.euler_tensor_power_difference_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerPolynomialDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "99463c9dcf8d17e82f9ccad1ef7bc80587cb0d7843a65da73ea8f519bc5850ce",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerPolynomialDegree:6458",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerPolynomialDegree:6458"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.euler_tensor_power_dimension_difference_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerPolynomialDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f4a4a615b3cb618a7dbab5c4c49161b5d93b7b1fb11c08a11168bf621adca87f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerPolynomialDegree:7975",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerPolynomialDegree:7975"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.eventual_cartier_restriction_section_lifting",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NakaiSectionLifting",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b7937af9d521535f1c0e7875fe282a1b945865f825b7a9370c9476a40541df6e",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NakaiSectionLifting:1479",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NakaiSectionLifting:1479"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.eventual_closed_cartierMiddle_cohomology_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NakaiStationarity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "db70a8568cfb1d305639fb4866246f1ea62d949812ba3a72796da28599e845cb",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NakaiStationarity:658",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NakaiStationarity:658"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.eventual_globalSections_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.NakaiCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2ddc54383968274c6f2c8d8cbab87b0f84ad72a874c7722870d9fef489fb2ea2",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.NakaiCohomology:2993",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.NakaiCohomology:2993"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.eventual_mixedPower_cohomology_stationary",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NakaiStationarity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1dc5d5341c06ade1d31e98ce07d2f51ef4fecaea9e692d447b88195077140f90",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NakaiStationarity:1729",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NakaiStationarity:1729"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.eventual_power_section_cover_of_ample_zeroDivisor",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NakaiDivisorAmple",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6f56057e7568305da242e2c64c1b003f6d0bf3423693792a0b71852f5e379817",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NakaiDivisorAmple:2335",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NakaiDivisorAmple:2335"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.eventual_power_section_cover_of_divisor",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NakaiBasepointFree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c820d423a23a049fff59c701d6c808d77a737331fa702e095f107701019a5bd9",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NakaiBasepointFree:2871",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NakaiBasepointFree:2871"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.eventual_zeroDivisor_power_cohomology_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NakaiDivisorAmple",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b66178ee4e191119f5913162c4b2416a3068a0fb41c324f2936d191cc5125674",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NakaiDivisorAmple:1571",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NakaiDivisorAmple:1571"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.eventual_zeroDivisor_power_generation",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NakaiDivisorAmple",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4b2982623db834f3c70ea34d570772fe33ca382367b30932f288108f54bcf31b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NakaiDivisorAmple:473",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NakaiDivisorAmple:473"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.eventually_constant_of_antitone_nat",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.NakaiCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "59f2b5b33d7554ceee3e2a33270b134f55fa1cc1dfef9736c6052953b7681f66",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.NakaiCohomology:2645",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.NakaiCohomology:2645"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.eventually_nonzero_globalSection_of_euler_growth",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.NakaiEulerGrowth",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1f2986fe8b42b1f91345674b6103e16fccdbddc81dcff3e32a6b2fbaba92e867",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.NakaiEulerGrowth:1568",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.NakaiEulerGrowth:1568"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.eventually_nonzero_globalSection_of_eventually_stationary",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.NakaiEulerGrowth",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e2c9a98591cf65998d07330d6bb1cdf447ebd185646500beadbb01f7b995f30e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.NakaiEulerGrowth:3109",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.NakaiEulerGrowth:3109"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.eventually_nonzero_mixedPower_sections_of_growth",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NakaiStationarity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8d8e3546566537140f0af7cb53b652e775c815a5b7350dd66127332b9f766605",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NakaiStationarity:3581",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NakaiStationarity:3581"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.exists_ample_slope",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ee43dc35d89098f8f86495ec71ddd10fd7132b9271785f23d222e005c84a91d3",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra:4356",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra:4356"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.exists_common_tensor_generators",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerRegularTwists",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aa237aac061f80be23977e80e32e6335e5b2442dd5fcc31cef4e9e7b9ed614f6",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerRegularTwists:336",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerRegularTwists:336"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.exists_integral_closed_full_dimension",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleDivisorDimensionBase",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4c71d6c77d7f394261e49938c6ac36b83e7e0f4ea31ec347b8321a70526a8fcc",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleDivisorDimensionBase:1154",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleDivisorDimensionBase:1154"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.exists_irreducibleClosed_dimension_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.IntegralCurveExistence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "51441406eb59a503d7c9818668fe808c8d2380130a1cc4d415098cf3395ffc92",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.IntegralCurveExistence:2696",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.IntegralCurveExistence:2696"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.exists_irreducibleClosed_full_dimension",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleDivisorDimensionBase",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "59738d94837fb673ba239b060ca01540c17cf1cbd8a5ee85ec784a3e35ed8f1e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleDivisorDimensionBase:481",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleDivisorDimensionBase:481"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.exists_mono_linearCombination_of_finite_cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e6c492dde672041e9540a327a3d1b8fc2052e82036c7ae8333c7d18656c372b6",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice:5324",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice:5324"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.exists_mono_section_of_finite_cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "835b21555d746ca612532002379cd0e098d0fa5f285751664dfdd1cde6e2798c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice:6809",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice:6809"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.exists_mono_section_of_generators",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerRegularSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "380426ebb3b41cfe060218be3f2ce1feaeab03a34663513422ca0c058a953f75",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerRegularSections:395",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerRegularSections:395"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.exists_nonzero_globalSection_of_cohomologyDimension_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.NakaiEulerGrowth",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5fda4c5ae6b2dc4052785a76f10bd788bb47a009bf8f0ab0ea751057b004f908",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.NakaiEulerGrowth:305",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.NakaiEulerGrowth:305"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.exists_nonzero_power_section_of_euler_growth",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NakaiEffectivity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d405cbfb559c1c3da883fa4001d0c071b176af987e39c9db1f6070dc9f6a009a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NakaiEffectivity:805",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NakaiEffectivity:805"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.exists_positive_power_regular_section",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPositivity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "485d6db50cb56d1eaa01b0fa5b8cb04edca9c2dd11b9a68793155fc702f9a410",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPositivity:346",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPositivity:346"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.exists_positive_rational_below_of_polynomial_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleThresholdPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3af161325a0dd65fcbfd749b0359305e60d72b939ee386f1d16382c871a91124",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleThresholdPolynomial:4467",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleThresholdPolynomial:4467"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.exists_power_section_cover_of_euler_growth",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NakaiEffectivity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "567d71188f1885d7063540153ee5c6ff0bcfab8c77a06765792a7f9fbaa0a1f6",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NakaiEffectivity:2987",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NakaiEffectivity:2987"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.exists_regular_twist_pair",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerRegularSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "803d09ace6b68d838db5410d1e77f869e9176483bf62272b99f84c0257579992",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerRegularSections:773",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerRegularSections:773"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.exists_smaller_ample_slope",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "08366faab44158fb840d7ddbb0b36b75f9be70e89a9cf38a07a9f32cff521932",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra:3340",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra:3340"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.finite_affine_frame_cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "680676e37f05f2d7e35dcde2ae4c4cde850c10470a4ee0791fcfe275dfe545b5",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice:563",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice:563"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.finite_closed_fiber_of_no_integralCurve",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FiniteOfNoContractedCurves",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8bf84dd4d53e1e355707de5380f42883af1566e794bc48f28e92b54acddb0507",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FiniteOfNoContractedCurves:1688",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FiniteOfNoContractedCurves:1688"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.finite_of_dim_le_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerZeroDimensional",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c3d05c03dba8c5a126394bbe3deae084ada1a52baebf5952011f91a1d8241bc4",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerZeroDimensional:590",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerZeroDimensional:590"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.finite_section_cover_of_pointwise",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NakaiBasepointFree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ff86597d5db4a8a38529bda614610f378feef3f7a097e1aa760d189d169eeb92",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NakaiBasepointFree:1935",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NakaiBasepointFree:1935"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.forwardDifference_eq_zero_of_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerDifferencePolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6bf36d08003811e8a45c8463f22f06c995f21ef1afaa8f9b4b27def863b702dd",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerDifferencePolynomial:179",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerDifferencePolynomial:179"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.framed_section_mono_of_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionMono",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f7079ea96dd3064f603f34b71fc7305b7d68f57bff39f80dfd4e30afd946c891",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionMono:1832",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionMono:1832"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.fwdDiff_eulerCharacteristic_left_pow_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerTwistTransport",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "33e9903a413e02bb71464a45c25d76d159baaf3f1ef48fc722b29370fb28218e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerTwistTransport:2013",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerTwistTransport:2013"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.globalSections_surjective_of_h1_stationary",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.NakaiCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "60ea28c2a45a3ecc199cc587145d7822d7dfe1ab44a4060cb6524357a4866132",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.NakaiCohomology:877",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.NakaiCohomology:877"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.integer_newton_sum_of_forwardDifference_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerDifferencePolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "72eabe519298be3ae2812ddfc98ca45417f0229dd62073edd8b23a0d5454ddb8",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerDifferencePolynomial:1481",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerDifferencePolynomial:1481"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.integralCurveFromClosedFiber",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FiniteOfNoContractedCurves",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b3bf3558fe32e2f9e6de01a0cd87d477533023d4b474d9b95a2545c7288e7010",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FiniteOfNoContractedCurves:806",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FiniteOfNoContractedCurves:806"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.integralCurveOfIrreducibleClosed",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.IntegralCurveExistence",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dbd507984da18ac0d70395f10d44be984120f0242b0e363b5bc9b50bfb4eeb92",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.IntegralCurveExistence:4271",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.IntegralCurveExistence:4271"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.irreducibleClosedRestrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.IntegralCurveExistence",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d60e3dd0f9833b71e90cc1ce67dc8ee62c7eefdb4ba312c7616b9fefa4ed7894",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.IntegralCurveExistence:276",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.IntegralCurveExistence:276"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.irreducibleClosedsBelowEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.IntegralCurveExistence",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "218634d13025012c3dc91424ad599538d52422270e77d472fe78a39e99951764",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.IntegralCurveExistence:1057",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.IntegralCurveExistence:1057"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.isAmple_of_global_frame_affine",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ZeroDimensionalAmple",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "74a6fd387b4ec7b8a0f4394a7ea0661ba87b41c7ac1fad40fd04bbc1c1a83e97",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ZeroDimensionalAmple:422",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ZeroDimensionalAmple:422"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.isAmple_of_integral_closed_restrictions",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.IntegralComponentAmple",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7f74169527dacc8832c1ed1592d3bedae5f6fd057f5a8c853301b3ff4ab2ad64",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.IntegralComponentAmple:338",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.IntegralComponentAmple:338"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.isAmple_of_lower_ampleness_of_euler_growth",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NakaiInductionStep",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3c33e5da16cef5dd37e4544fe4480b16e5bfac9814ad25e3c12bbe4f3f596885",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NakaiInductionStep:481",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NakaiInductionStep:481"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.isAmple_of_lower_ampleness_of_topEuler_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NakaiInductionStep",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "35dbd6fcc0b970b2db1d64104b0ce8b868fc8a8b35a330a355151744c549f673",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NakaiInductionStep:1575",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NakaiInductionStep:1575"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.isAmple_of_lower_ampleness_of_topEuler_pos_of_margin",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NakaiInductionStep",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f839f658102e59512af92b590b0ff2cad2f14c2059b756d64523c894429777bc",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NakaiInductionStep:2841",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NakaiInductionStep:2841"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.isAmple_of_lower_criterion_of_euler_slope_polynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.NumericalThresholdStep",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f28a4aa56a95a232d840f644e3c699e15a01f3ada268f5e7ea9a7c0aa49d0d37",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.NumericalThresholdStep:412",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.NumericalThresholdStep:412"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.isAmple_of_lower_numerical_criterion",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.NumericalEulerSlopeInputs",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "54e4eaecca6617ec7014071b51858d76574aa0bcd61e304d9d3cb62a341281e8",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.NumericalEulerSlopeInputs:3475",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.NumericalEulerSlopeInputs:3475"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.isAmple_of_proper_dimension_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ZeroDimensionalAmple",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6842c664d46921a1a013f8ad47abb39ca7a07e276a3a4227d462acaff2afc9ad",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ZeroDimensionalAmple:1514",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ZeroDimensionalAmple:1514"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.isAmple_of_section_cover_of_curveDegree_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NakaiAmpleFromSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "96107b2e9a97acf4c6d882f75c0c30463a4914383ac08cb5a4407d818ac397ee",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NakaiAmpleFromSections:2605",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NakaiAmpleFromSections:2605"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.isAmple_of_uniform_curve_margin",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmplenessTheorem",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c76644dff27681d1f7684786890c49d9c97ca40037c8a6ce4d5245c9e8db3403",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmplenessTheorem:3169",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmplenessTheorem:3169"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.isAmple_of_uniform_curve_margin_dimension",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmplenessTheorem",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "67fbd9e083ccb77d3cbee9b71ef7ab27dfe643d9472d0de5423bc50c0cba1481",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmplenessTheorem:534",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmplenessTheorem:534"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.isFinite_of_no_contracted_integralCurves",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FiniteOfNoContractedCurves",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0e979f7ad223484c48bcc436541c73e188caf2619b09d3be52e7890ca4879929",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FiniteOfNoContractedCurves:2625",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FiniteOfNoContractedCurves:2625"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.isFinite_of_proper_finite_closed_fibers",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFromClosedFibers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "76d6198b42ca5b5605745d7df952913f5c9e974b396f1510ebf01bd7b34fa804",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFromClosedFibers:260",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFromClosedFibers:260"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.isIso_of_locally_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1295953e5ebb94efc9f0c296a136166b067fb8e98b527c2d1019f43c08f83b08",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws:216",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws:216"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.isReduced_vanishingIdeal_subscheme",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.IntegralCurveExistence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4acb45b3ce5926b96f594aaba76673e3fa41c85b09583c58867de3dc8b66ccd4",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.IntegralCurveExistence:3561",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.IntegralCurveExistence:3561"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.iterate_fwdDiff_sub",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerPolynomialDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b9d1ac1d059aba163edd3747ef1229c5336bb4c7348abcadc256e6385249ccb5",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerPolynomialDegree:948",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerPolynomialDegree:948"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.lineBundle_cohomology_eq_zero_of_projective_embedding",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveEmbeddingCohomologyBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c26cdf1f455756211b7cdaa76c7aeadc3d095b73ba9a5c254abb4f1179b05425",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveEmbeddingCohomologyBound:1621",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveEmbeddingCohomologyBound:1621"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.lineBundle_cohomology_zero_of_dimension_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LineCohomologyDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "516422e811ebdac1eb6f06a4b536daeb685b22a2b11f78fae12fa67815860a45",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LineCohomologyDimension:856",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LineCohomologyDimension:856"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.lineBundle_trivial_of_dim_le_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerZeroDimensional",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7e409d828473df53cc2c31cda15f5ec3a920046fa503bed332a4414713d6daf5",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerZeroDimensional:806",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerZeroDimensional:806"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.lineEuler",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerDimension",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "52c5a52f4c47bd0b58825f52bbcc26f5eb324d185eadfb4c84516cbde7b571b8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerDimension:393",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerDimension:393"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.lineEuler_isoInvariant",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "443a503f641aead23e3cdf751e64b43223c394f5dd519c0d4e40025b652d6e12",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerDimension:540",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerDimension:540"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.lineEuler_mixedDegreeLE",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerTop",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "83ccf487ceb38533d2c13eb9ba323b089ae53a369a081ef47bbd63586ab198b0",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerTop:1137",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerTop:1137"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.linePowerTensorInverseIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "de61fd40752d0556cd95ce2367b0b50432899d72a2a5e17b9ff1703db0a62418",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra:2617",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra:2617"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.line_cohomology_finite_of_ample_all",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.AmpleLineCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4c8abb83a6f7272a153e768481e8a16bdb910c18b644025cb4411a7ac9bdb116",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.AmpleLineCohomology:379",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.AmpleLineCohomology:379"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.localCoefficientAddHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "80bc108116c8073ae9e63d2198e994720ef2f5a574755bd7077c194ebe82859a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice:2652",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice:2652"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.localCoefficient_linearCombination",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f3115c92a1d10e51220fa7f1db235c882b6c97cd6c7ef2a2f5d50f4294b77142",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice:4742",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice:4742"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.localCoefficient_scalar",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "23b4bf1cd64e39da5a8d9251fa694ee0261cb82aef6263eaa0f5f9cc1c7be473",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice:3522",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice:3522"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedCartierPowerMultiply",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CartierMixedEuler",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "62c7fe69b7ffeb5d746ede835a75188d83104c792dc57aadc571ba8f87428634",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CartierMixedEuler:3011",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CartierMixedEuler:3011"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedCartierPowerMultiply_mono",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CartierMixedEuler",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3c80af3b191cfa790141b324b683a184b55337119ed1cc5b098b64d1a1425cd6",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CartierMixedEuler:3246",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CartierMixedEuler:3246"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedCartierPower_zeroIdeal_frames",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CartierMixedEuler",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8d71d44ab93102afadba3506d9c3df2b7a4a716fbe2e217379ec0d0b3f3ffa0e",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CartierMixedEuler:3529",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CartierMixedEuler:3529"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedDifference",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c470ba23ba26ca910afaafb68ccf6e042c220248b71fe59f3cd255b2503da871",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra:619",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra:619"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedDifference_cartier_restriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2193a27981b2becaf2b2e1dfc6cbee909f23222fea3213c2769eb905c2c960f7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerRestriction:2259",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerRestriction:2259"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedDifference_cons",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6505ba66cc625c88af06b760adfe76791ded7539b802015f235bd79fec8d8590",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra:893",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra:893"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedDifference_cons_commute",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "46e119b228f9e2327c1ca146b9cee8211c246e589b68749a7801c312f23d9438",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra:4046",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra:4046"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedDifference_eq_structure_of_degree",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "58d0d138c53b4aad4fbfbb0cd15e43c8844af89d3c7ed1ceda0f7b73afaa1e0c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:2427",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:2427"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedDifference_iso_cons",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "492d0bc90a7836090bb5d3338fcde457c13d98bc48a766acce49d609a68c09ed",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:1025",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:1025"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedDifference_lineEuler_of_ample",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAmpleDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9a8416d6fccbe4d9d47df3b3c638cf1a4bf44b10ae1b1c41b913bad68b909b40",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAmpleDimension:4011",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAmpleDimension:4011"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedDifference_lineEuler_of_ample_aux",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAmpleDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c521eb02e43b39b686025c8d06c549fbfbeca280a298f9a7aa38cd31567ad644",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAmpleDimension:400",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAmpleDimension:400"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedDifference_perm",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9bb83a8f252d11611438c5b8638d878d55931d40446b21d30af6fb29aaaa4116",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:595",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:595"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedDifference_pow_cons_of_degree",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7671665894958a1445878090bb3a6962f3e2b8bdf09198253ac5efd133e4a295",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:3812",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:3812"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedDifference_pow_zero_cons",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "02d52c09f2c101d3912bf1f7d6f88d11e4e2adeba3f5a04c3fc491c3412c0e0e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:3421",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:3421"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedDifference_pullback",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9faaa7d8d9900d33ad0b94766790212d7ca392289fd9e78a61b510afe3000e04",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra:5210",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra:5210"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedDifference_pullback_tensorShift_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6811c299dbf39a6b5195757eef94b997cc36407940c7921c6de948535d5c45a8",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerDimension:744",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerDimension:744"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedDifference_replicate_pow",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "73e825a617cc3e6631830a098d1825f1a03641bc3eccc63e6c4e38d2127297dc",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:4457",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:4457"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedDifference_replicate_pow_append",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0780abef888ad551840e8fe8ba3f520b753e4706cc31b6bd4489131b8173919b",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:8223",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:8223"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedDifference_replicate_tensor_append",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "15233f33a118f755c29586b67c3daa4effdc7ef11913080ee61dd077fd2bbeeb",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:5575",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:5575"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedDifference_sub",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "641c91fcb8cce73a7456276e731f064eca9c3008d7000364c02dedec05b991a8",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra:1602",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra:1602"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedDifference_tensorShift",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1b0d1ea8950bb33b4872fa2edbc992eb529868df7671c0a31ca08b3f521d0625",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra:4597",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra:4597"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedDifference_tensor_base_of_degree",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5090abea92e3ccefd6a1d93b04093f226ca168aa84069efccd3485e1c9938256",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:2079",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:2079"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedDifference_tensor_cons",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f90434ae7187ce02655a11473f155d8050b6bbdde16de45823efbf49357b0d27",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra:6730",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra:6730"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedDifference_tensor_cons_of_degree",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bb128850b99d0c572b60236095bcc75592921efa1f9e5baf4319138ed98fd89a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:2954",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:2954"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedDifference_tensor_cons_of_next_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "77e4b75250ba122431aef82b0b9e5828c8ac1687e9d0f70894876594e561bc3a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra:7111",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra:7111"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedDifference_two_powers_append",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9c4a0349b9efa1fe95236b13edaad6639669de583dcfa7d42efbae10239264d5",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:10904",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:10904"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedEuler",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerTop",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "61a9748539af73aca907a0b346e5e45b047898d4de27010ab322b88e2d678a8b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerTop:516",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerTop:516"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedEuler_perm",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerTop",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9c94bb531bad10599dca39b2ab17ad3348d2e5cfefce0a92a20b50ad94201b33",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerTop:870",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerTop:870"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedEuler_pow_cons",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerSlope",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a15e183abdf3e08c7be4e5c795c53ec7af9dccd08132f1451d1fcafc13c167e3",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerSlope:6278",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerSlope:6278"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedEuler_replicate",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerTop",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9a6d9405f76e9bc3c7495e661f5ca8500c0802d54491743f33e343a6e329737a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerTop:651",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerTop:651"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedEuler_replicate_iso_append",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerSlope",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "839f5247987c692abd0f6545be8e92c123ca0322e358ee45c7627ceb7719d6d2",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerSlope:1170",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerSlope:1170"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedEuler_slopeBundle_eq_append",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerSlope",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6e66fac0147b076c3eaa46567af6318feebd18529b9947c940668fb10372a6c4",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerSlope:3254",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerSlope:3254"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedEuler_tensor_cons",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerTop",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6531b1655bc7442562bd53d248a798df3d801fd5a54aa8964689683929d0e0da",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerTop:1427",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerTop:1427"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedEuler_tensor_powers_binomial_append",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerTop",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "44b123743de9f9123e72dc8a57681a0cbfe1aceb3b8018fb413a43fbf094c78e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerTop:3168",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerTop:3168"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedSlopePolynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.MixedSlopePolynomial",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "721d83c7fcdb5aa642fd26566f3bd1b891fa7f793b908a9ecc41d1041235bbad",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.MixedSlopePolynomial:160",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.MixedSlopePolynomial:160"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedSlopePolynomial_derivative",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.MixedSlopePolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c26a7db970402f4d14e608e6c1f820d19ed18830455657831396ba10e9797920",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.MixedSlopePolynomial:815",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.MixedSlopePolynomial:815"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedSlopePolynomial_derivative_eval",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.MixedSlopePolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6f4e51fc3d1e9b2edb050ab19ec5b501f9a53c678d090da569900a284e58e423",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.MixedSlopePolynomial:1641",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.MixedSlopePolynomial:1641"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedSlopePolynomial_eval",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.MixedSlopePolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "364816aa033332c688a0b7f7f9e43f8aeb4fc455196ae36843d69dad4f2f9b40",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.MixedSlopePolynomial:297",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.MixedSlopePolynomial:297"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedSlopePolynomial_eval_div",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.MixedSlopePolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "03cf330938e3b2254a36f6c8ea5a2fb1b9fa649dca31a6712894f26680c17c12",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.MixedSlopePolynomial:1909",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.MixedSlopePolynomial:1909"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedTop",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c013946cdd197838b88ba9b046faf50d322062face846c1c1025c514137bd528",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:5090",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:5090"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedTop_cartier_restriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4b4c1bc76ac01c1c5d113f8def6fc7e0926296501452add182a0d228e00463f1",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerRestriction:3436",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerRestriction:3436"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedTop_curve_margin",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerCurveMargin",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1149ceb8b497c44f2a430e964f23d7d18e9404d57bd428b51031fc8a21e34753",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerCurveMargin:3421",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerCurveMargin:3421"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedTop_curve_margin_aux",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerCurveMargin",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fe4be736d8a0229ff9a5521aefe5aedc70cb404f379f2fe6b5b5897751fa03ee",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerCurveMargin:342",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerCurveMargin:342"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedTop_pos_of_ample",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPositivity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0fc7580a0d13083a345b88993fea514d7dba4c4d5aabbe42ff6ea11045187094",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPositivity:3518",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPositivity:3518"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedTop_pos_of_ample_aux",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPositivity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4b78de17f0f66a587b73bd406999295ea76d3fd8a40cce52a143512e428de1ec",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPositivity:845",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPositivity:845"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedTop_power_cartier_restriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c0c23bc362624b92f0166332fd9fe3747174f0975e8ad2036ced4d805e1f481b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerRestriction:4677",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerRestriction:4677"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedTop_replicate",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c841ae635239738514ec320941a0b68b76715f19183ab101ad1e04c20f22d5cb",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:5217",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:5217"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedTop_tensor_binomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e79e3a0b673e0d30f9a2668843cf9d991cd120216f844664a4f1b95398abc58b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:7631",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:7631"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedTop_tensor_powers_binomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "34a9d5de419be56660b59ade5119ce2bd7546ce74c8f0a5b8e9816578443892f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:10264",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:10264"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedTop_tensor_powers_binomial_append",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2a9e6ac480536929b4ae8f4b55a16475977677beee1bafa0cab05e8ceeb0d657",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:11934",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:11934"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedTop_two_powers",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "db1149b06913a95f09a110f0b87be351d448d211ce71907e7bd227bb6739d4c8",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:9201",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:9201"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.newton_sum_of_forwardDifference_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerDifferencePolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c72137155066b8b45f651a3306088a8a4ba1d64c5314363145db37c21e4a4d98",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerDifferencePolynomial:547",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerDifferencePolynomial:547"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.nonempty_integralCurve_of_dimension_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.IntegralCurveExistence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ce67c3a0be3930366d84e6d14cddeb913adc2228d38c262c6a4940abe31859cd",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.IntegralCurveExistence:5156",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.IntegralCurveExistence:5156"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.nonnegative_rat_nat_ratio",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleThresholdPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bffea02e976bd52f02077b10c00fbcf272fd954da733b1ff864f3ebfb830759d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleThresholdPolynomial:4197",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleThresholdPolynomial:4197"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.polynomial_pos_at_boundary_of_rational_margin",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleThresholdPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "528a322904985708300b2c549d476ad01e872fbdecaf665b77ec310391b34d4d",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleThresholdPolynomial:3082",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleThresholdPolynomial:3082"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.polynomial_pos_at_left_of_margin",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleThresholdPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a6063fc1cf907a3912012e157841889de7748a4cb7e2601455cd3c111f69e560",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleThresholdPolynomial:194",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleThresholdPolynomial:194"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_019.jsonl"
