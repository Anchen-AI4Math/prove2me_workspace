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
      sourceName := "OAI.PiExponent.NumericalAmpleness.slopeBundleAddIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f87ecd8ec71d1b9ee333cb18493f98bbc544e2abe87988d1847cd3b7c7cd4557",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra:800"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.slopeBundleCongrIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8cc1735277b48647e3625b24b6353858ccb4b2b2d2011ad23be04eb47f9c7009",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra:1069"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.slopeBundleCrossIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f54980b5c1cffc2256834f823daff6d9141251c03ceee9a4cbd52321543fcc41",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra:1279"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.slopeBundlePowIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cb92ce2aad9c11012b177fb9e717f5b453d40bc50368ecd2b81faf0a6239011a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra:545"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.slopeBundleSubtractIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "24292d1aa13898efa91897fe5dd3798e5c6465c06acd03ee060de4d4c0ad628c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra:3046"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.structureLineBundle",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "699dcb58769c4d01d0007007c2b5a5e1b6f612c4d346561c7e8efc51c708d0cc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization",
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
      sourceName := "OAI.PiExponent.NumericalAmpleness.tensorDifference",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "db20840077238abd01c25cbdfea59410e94002e877e454361bb71ab8b6cccb6d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra:490"
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
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair:1473"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.tensorTwistSwapIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "285d55c57f25881390b72dd4ec258eff8bb39eee5a3c808b9006b5893d240c6e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra",
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
      sourceName := "OAI.PiExponent.NumericalAmpleness.topEuler",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerTop",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f43d09a9ec18a6799672156d93ced07f606f4212928467a0665275412fbe7838",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerTop",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerTop:344"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryAuxiliaryJet.branchCoordinates",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryBranchEvaluation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b334029e19393e2e9608e7b6257dc47fbfa71cd43e9bed623f16b3c287dbb5de",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryBranchEvaluation",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryBranchEvaluation:240"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryAuxiliaryJet.evaluation",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryAuxiliaryJet",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "52ab387ad4b41fb796b2dcb3f30eb8f584b6cba38a2cb44d6d00035718c86c95",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryAuxiliaryJet",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryAuxiliaryJet:521"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryAuxiliaryJet.formalJet",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryAuxiliaryJet",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a0d733b12e7ed84026a0c5eba173c8f3c83a1208ed3ba0ab53309ba2d49eba08",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryAuxiliaryJet",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryAuxiliaryJet:326"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryComponentRigidity.NormalProductComparison",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.OrdinaryComponentRigidity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4f02b969d1dfca851018b4060f67ba56362536c3d63882ebab1240e21ed3db93",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.OrdinaryComponentRigidity",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.OrdinaryComponentRigidity:410"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryComponentRigidity.PersistentNormalComparison",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.OrdinaryComponentRigidity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5ef2002dd80e5cae9df5386637ba3f023df4262ee985832c220b449c2b1faff3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.OrdinaryComponentRigidity",
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
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDVRBranchJet",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDVRBranchJet:1957"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryDVRBranchJet.coordinates",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDVRBranchJet",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8cad82046bbac8156ee96b14a173de4e097b55a4b3bdd197a3ef05846811e39c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDVRBranchJet",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDVRBranchJet:943"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryDVRBranchJet.coordinates_nonzero",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDVRBranchJet",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "abf9916e77f27076591a12cef4bf0378fe59e4664b59a02087e6fb5117071c55",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDVRBranchJet",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDVRBranchJet:1548"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryDerivatives.BoundedWords",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "929fb25d43ed1a7e8f3de947e8f8af1a87892ba9148bcad8e75779df296dc2e8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals:2832"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryDerivatives.Polynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "65604b211d391bc41950560b57c2e4e60f7105f18c8117acb1501ba806bd9205",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals:344"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryDerivatives.equations",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a9b888f56bcdb3a3e4743e3ec0f01adbb80fa780e1c9b5642284ba0b5f570eb0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals:2956"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryDerivatives.ideal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0c49c155af29701bc93151e2a6c7fa5a27b13f6e2a2edd084b184b04619a412a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals:1677"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryDerivatives.partialFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c6c5455286805d386d819c2c5e6ef344f52f86f41f24bc3eb63d6db3e08ed8ea",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals:403"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryDerivatives.word",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4acb49286ee38ec51890763f1ce677cce540680d842fdab400580e2b2f4d1b66",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals:1322"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryMultiplicity.localTaylor",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.OrdinaryMultiplicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "352f9a61fe1d1224cba823cf0b5c4725d1b7ce2f96a552c179e73bc96703323a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.OrdinaryMultiplicity",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.OrdinaryMultiplicity:1155"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryMultiplicity.polynomialTaylor",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.OrdinaryMultiplicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fb5d42027413dc1969c2690c975ad7fa56497d0a7f064f0b5819d827107ddb96",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.OrdinaryMultiplicity",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.OrdinaryMultiplicity:338"
    },
    {
      sourceName := "OAI.PiExponent.OrdinaryMultiplicity.polynomialTaylor_constant",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.OrdinaryMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "13bdac3b6667c516b919f5043bd94f7da683cb15b989b1e52a2edb2e5b420870",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.OrdinaryMultiplicity",
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
      sourceName := "OAI.PiExponent.OrdinaryTaylor.ordinaryTaylor",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.OrdinaryTaylor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9fe3a8b7f098e199eaff673f9c09309a46969e5e9783fef7d61a59e5bbdfd757",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.OrdinaryTaylor",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.OrdinaryTaylor:4106"
    },
    {
      sourceName := "OAI.PiExponent.ParameterResidueField.parameterChartConstants",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterResidueField",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b86ec5607b7fd5190b85191f34ebe8d47261c54e0cdafcc0aed397c9ae178030",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterResidueField",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterResidueField:657"
    },
    {
      sourceName := "OAI.PiExponent.ParameterResidueField.parameterChartConstants_tower",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterResidueField",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2a164031af3b7152d10dad73af3f977a5609c1afe4a7ff24e48445aa0c2ca832",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterResidueField",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterResidueField:935"
    },
    {
      sourceName := "OAI.PiExponent.ParameterResidueField.parameter_residue_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterResidueField",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "68e20109655b3b8835b1a6769b3745ba56bbf0136fd445c1799449cdb84ca53e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterResidueField",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterResidueField:1347"
    },
    {
      sourceName := "OAI.PiExponent.ParameterResidueField.parameter_residue_integral",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterResidueField",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ad35d10006c6099840da22d361497969a6d09a0108a885da9e88f80ffb648032",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterResidueField",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterResidueField:2389"
    },
    {
      sourceName := "OAI.PiExponent.ParameterResidueField.residue_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterResidueField",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4a721469262df2068e12703e1fad9a218d20c7ec254c2088a73ee6562ac9d027",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterResidueField",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterResidueField:235"
    },
    {
      sourceName := "OAI.PiExponent.Parameters",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "inductive",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1959ebb3f2aea65f610a6dccebb1d76370724d77f59615a8613f6fde38207407",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.A",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a4b59a8b4862dd1436e6b185c6ad40d37c8a10bf6b7128048cbdff8c4ba8d1c5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.A_lt_B",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "104640a061689cc71fe999651e3c55424ecf9a4e77ecd24cc21c0769b0f4970c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.B",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ce4bf30b3ed54f9be5151c2a8405547f6049288790361cbc1dcbf2fca8ece291",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.B_lt_C_theta",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8321e192bb45c64f18380c423651fdaf474e0ebcc1e0d827e539199d8c59592f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.B_lt_inv_C",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "93c64801fdd7a5307b83f52be8c091143d8da52d2d5b9011a879767655e555c1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.B_lt_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "692e10f8930e2164c2799f0e0b4727a1fee6feb0770a8ec33e6bf53ca834a61f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.C",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "78f8bfd96546f52acaa6ecc5403daacbd937489beb030bcd3667d170ea4230c9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.C_theta_lt_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9c1e892f80d53d1583368c914bd05959fba4da7100a7c59b921c4ed990099270",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.approximation_gap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fd561b73e671cc3c7dec530c3242cbcd45a158917a9a2427bfb700951d1a8206",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.casesOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "414e266917c5ab0795344618c5171503fbe89f8fd4de3f4c795e862355a05d13",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.eta",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "91809a058c30f17b25f47973836bfcb627bbf45aa2b5d7a58df2b495bc848f0a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.eta_lt_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "083f67995d6b489dd477f85539829ae0f909e017b7b2ae98d79c97d17bc86a1b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.eta_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b7ad4122c2a230b73caa0b6389cc6104fb061ab5dfefa3e9b39bc3605a8f3628",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.gap_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "df664f2d63b6b8c38fc17236e4ce5feafffd4c8434f85135c3d44d2f63d9c3e3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.mk",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "ctor",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "96d047fab06b0c5b26def512360adacb9bb5b285bede888273d0adac5e69b4c8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.mk.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5117ffeec9d4cc0dc67cba1eee378f06f6fd17e0dd45e3de66fac5f2bedb08eb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ca392e756dc60c8923068c5514391b33470b162a7fa98ddc6dfc600189b73e01",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.one_lt_C",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "08c66cfec231332f79f5b9beafcd9b4ea3c7a3cae7659f61081d63a749aa054b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.rec",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "rec",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2bc2f50c6fc2cd9b3b010eb22618c5ccda2dbeb9f070da768579876195eebb37",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.recOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "55b2878abd89a225fa453669d093e9984dc054e329e650f35e579ed91ebc1c53",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.theta",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "31398ad0ca6bea5cd9f9a5281e73a6e514e34bfa9d100ab9b0137324edb592a5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.theta_lt_A",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d4abb8c9fb3d254317e4b080b65a01f32f13042a1beccbbb9bc66c8dbe48cac3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.theta_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "72465333cd1627e9ed4b04f240468bea82c752fa5eef9be02d37292c22a7a2bf",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.PeriodAnalytic.columnFunction",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "32c0368743a1dc58171c4d42c68749ed87a3cfec02c2dfa7a30fa8f19ed96464",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic:6625"
    },
    {
      sourceName := "OAI.PiExponent.PeriodAnalytic.norm_columnFunction_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d52f13ab47ffa71b184c54689723490b2069b488ec5572aa323e3404df15be8b",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic:7055",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic:7055"
    },
    {
      sourceName := "OAI.PiExponent.PeriodAnalytic.periodFunction",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d46358cbac7e8fa3ee5e62a5f74f93602a0830b7b11716be865e9edcb7d192ca",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic:462"
    },
    {
      sourceName := "OAI.PiExponent.PeriodAnalytic.periodSeries",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4442fc28bfc5653dfe71bfd89523b0b5ec01afb86e48a494c1b1145301c2a20f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic:277"
    },
    {
      sourceName := "OAI.PiExponent.PersistentComponents.exists_adjacent_eq_of_height_bound",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "36ab207c923d7ec79be1aa566ec5a24a243e0a162a2c79ce1bec3347364a0800",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents:364",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents:364"
    },
    {
      sourceName := "OAI.PiExponent.PersistentComponents.exists_nested_minimalPrimes",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6f3d89e1953589b1c1bdb3decf57ce78a2a19952cfc2cdebe4094a93b3166149",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents:1413",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents:1413"
    },
    {
      sourceName := "OAI.PiExponent.PersistentComponents.exists_persistent_minimalPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2f18453054cdbbcacec2baee74a07599b79706574b778e22e85e7a5033bbef28",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents:2699",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents:2699"
    },
    {
      sourceName := "OAI.PiExponent.PersistentWeightComparison.UniformRectangles",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PersistentWeightComparison",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "41e466667273e1353da80e36f44d1bc014e200ff3ed3a795eb5ea51fd3d41426",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PersistentWeightComparison",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PersistentWeightComparison:673"
    },
    {
      sourceName := "OAI.PiExponent.PersistentWeightComparison.comparisonConstant",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PersistentWeightComparison",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c8115857447dca7c0c4d105836cda2bde07cba4fa10c3333878b9c09f198b920",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PersistentWeightComparison",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PersistentWeightComparison:539"
    },
    {
      sourceName := "OAI.PiExponent.PiEventualLowerBound",
      expectedModule := "OAI.NumberTheory.PiExponent.Statement",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5e5fedea2064a11a77a1b0f1f5457a715dde48df8a6975b2c491cb9b39eed93e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Statement",
      commandUnit := "OAI.NumberTheory.PiExponent.Statement:642"
    },
    {
      sourceName := "OAI.PiExponent.PlaceCenteredBranch.coordinateOrder_aeval_eq_length",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1e301443dfb291a2d9fcbc3c507c96c7ad14a1af5b96cf66e1b55cd68e8f13b2",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch:1810",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch:1810"
    },
    {
      sourceName := "OAI.PiExponent.PlaceCenteredBranch.lift",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c90d949223f0c7d759b05a33be66f039ec88f2541b2939e738000cc00fca76c7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch:469"
    },
    {
      sourceName := "OAI.PiExponent.PlaceCenteredBranch.lift_aeval",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3a9a161775d5ed1da638d1b7c7a45ed4a76c602a154fd9fd7b0362a887e5c7ef",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch:1462"
    },
    {
      sourceName := "OAI.PiExponent.PlaceCenteredBranch.lift_nonconstant",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8e6b9f52b1a552992fc5dfb401f5dda141be000808b7eda961f42a04dfac0271",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch:787"
    },
    {
      sourceName := "OAI.PiExponent.PlaceCenteredBranch.lift_residue",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ba297c5fe4bebd086cf255b840f898e378616b1fa80a7858fc3e30e2a9fe87fc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch:2866"
    },
    {
      sourceName := "OAI.PiExponent.PlaceCenteredBranch.logContact",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "771aaf58e6aaae678ec4669250f92e9308eabbf280f160fba585db9095f8bbe0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch:4250"
    },
    {
      sourceName := "OAI.PiExponent.PlaceCenteredBranch.logLift_nonconstant",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1e4aa5d2efd367cc6ad9b0daa6bd35684abd3d9ea3fbbacdc8b48b86b3e1d847",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch:3630"
    },
    {
      sourceName := "OAI.PiExponent.PlaceCenteredBranch.logWord_field_order_lower",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0fd0c09e4c27a469efa332a597d40881a46a470f145567f800919422e53e3b42",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch:5686",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch:5686"
    },
    {
      sourceName := "OAI.PiExponent.PlaceCenteredBranch.ordinaryContact",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "636dffb9266c43915931b3355caa01af18fe8392e6403e5adcdbb1b833260382",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch:5114"
    },
    {
      sourceName := "OAI.PiExponent.PlaceLocalRing.residue_integral",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceLocalRing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8556d53e243f09fd9f62ba6da1bea20cdc81428e6593d571b8855b2955d341b0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceLocalRing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceLocalRing:1011"
    },
    {
      sourceName := "OAI.PiExponent.PlaceLocalRing.residue_integral_of_algEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceLocalRing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "91234f3046524c43f65cf9ed6f6d2f912f053bbc237159acca740313defb2bcc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceLocalRing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceLocalRing:507"
    },
    {
      sourceName := "OAI.PiExponent.PlaceParameterModel.parameter",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cc1872affb389aebc96e556b5fc64b3bbb1e3dc6ef7ecbba6dadeba911ae8f88",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel:862"
    },
    {
      sourceName := "OAI.PiExponent.PlaceParameterModel.parameterCenterLocalAlgEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8363433a27ad8c8df9f34020d02e957d782a1341b6e20bafaaf2422bb8141f2f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel:4581"
    },
    {
      sourceName := "OAI.PiExponent.PlaceParameterModel.parameterCenterLocalRingEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "20686442b0c766d4cc103b301460fe08b1c566c5f39516db6e009c7c2fd52a92",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel:2248"
    },
    {
      sourceName := "OAI.PiExponent.PlaceParameterModel.parameterUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ef81fa8bdb5712dbd033d24194ccd82cc67ed8666a54e9ab98198a6a225574b4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel:523"
    },
    {
      sourceName := "OAI.PiExponent.PlaceParameterModel.parameterUnit_order",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d1d539da4730833d6788e5c209976f1308810c0449e12194a05a2ea2b3e70d28",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel:662"
    },
    {
      sourceName := "OAI.PiExponent.PlaceParameterModel.parameter_nonzero",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2baa35c5b96563c6a03ec3db943ff196141850f950a767fd02c6c99824d82867",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel:981"
    },
    {
      sourceName := "OAI.PiExponent.PlaceParameterModel.parameter_positive",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c48c93a4a3a51f30a66bb04ba54a1f2e087879cfe1f5572366ff9d4c870b1ebb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel:1391"
    },
    {
      sourceName := "OAI.PiExponent.PlaceParameterModel.parameter_transcendental",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "032e74653ffe313e03e65bd4e4472c5d408bd80d49c69487807879ab60ea66bd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel:1574"
    },
    {
      sourceName := "OAI.PiExponent.PlaceParameterModel.parameter_value",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d0d63f10340681a8899d60bb7da0bc78a053ae160cf6b8e86bff0ab7554e2b72",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel:1138"
    },
    {
      sourceName := "OAI.PiExponent.PlaceValuationRing.constantsAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "606171efce288f7544a8819928aa1da7d719e8c268c7226824096f27f33cc076",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing:673"
    },
    {
      sourceName := "OAI.PiExponent.PlaceValuationRing.constantsHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "052cdd8ca4545ae2fa4f340c191133d1f8bf8931e9b7dfa75490693bf9e6f303",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing:371"
    },
    {
      sourceName := "OAI.PiExponent.PlaceValuationRing.discreteValuationRing",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d8523c5c826e8e1d68a8d2b8b5ce4c74ad198ac91b7b04488c1c1e229764e286",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing:1383"
    },
    {
      sourceName := "OAI.PiExponent.PlaceValuationRing.ring",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e92acd080d29fce1757671f3a4dd37ddf358c05ba22dbf6a586cf0b34c760bd3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing:262"
    },
    {
      sourceName := "OAI.PiExponent.PlaceValuationRing.scalarTower",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d62b7bbfec228f8a526e5fb2aa8b431c27db7cf81b9b6ae01f87a98b23c26cb3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing:782"
    },
    {
      sourceName := "OAI.PiExponent.PlaceValuationRing.valuation_eq_fractionAddValuation",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c6313401f0ab07dfb4329eae6c840c05be68d1768a3e76f9efabd29ee60c1923",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing:1815"
    },
    {
      sourceName := "OAI.PiExponent.PlaceValuationRing.valuation_nontrivial",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a87b4102147d1b8d0b6b8d5f7066582fc5adf34268866ccf2d9e31b53982cf33",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing:1050"
    },
    {
      sourceName := "OAI.PiExponent.PolynomialJetPackets.polynomial_packet_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PolynomialJetPackets",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "adf4f2ada3423284cc13d7f9698ded7ee2905ac0006f3be5c84e7acf17374f00",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PolynomialJetPackets:230",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PolynomialJetPackets:230"
    },
    {
      sourceName := "OAI.PiExponent.PolynomialNormal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c6face3013130ed41f98d63d69e2ae16ec376b9fe79bf0311457fc2e253f4a4a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential:1534"
    },
    {
      sourceName := "OAI.PiExponent.PolynomialPoleBound.monomial_order_lower",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPoleBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ed8c36bbbd3ec1aa79a9933a7f72172274af0bd0536ec7738adfb9b2adcff70e",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPoleBound:942",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPoleBound:942"
    },
    {
      sourceName := "OAI.PiExponent.PolynomialPoleBound.realValuation",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPoleBound",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "57c2f673f59c9ff0ea983933561f985f97de727282da3f17465cf132202b1ec2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPoleBound",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPoleBound:299"
    },
    {
      sourceName := "OAI.PiExponent.PolynomialPoleBound.realValuation_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPoleBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d5d2900734eb6c9c4ef7e6cdab89450aa64ac4fea8bd441eb862ae7949277824",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPoleBound",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPoleBound:515"
    },
    {
      sourceName := "OAI.PiExponent.PolynomialPoleBound.valuation_prod",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPoleBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cc64eed0959e158c494055ba4bc062116089927f0f61c8c17e41866a33448d8f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPoleBound",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPoleBound:676"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.PowerModule",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c3859244b1dcdeb393478405da7224316a3cebafb72506ac66bc604ea3958b00",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis:1830"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.combine",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ca9222628cfec9ea5ddd42993f6826d5853fd7ffb16d858773d843e0bac3a2c8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents:567"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.combine_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "86eb3d9de0aee4cd0e2f6021d4feb40e29e81e76dc241c602a71c257176ac091",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents:1172"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.combine_quotient_residue",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a89a2cd18a1e71983ed220c0cc18a3c5186fa2e305d32bcb1d6105c0ab9c3744",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents:1350"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.decompositionAddEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e1a36286622de0c39517bc841ac56eb2ba1088b3d110fcba3a4538524264a156",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis:215"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.decompositionAddEquiv_monomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "afc37c29a0ee6a76cda570564a060f33e6af953304b1ca5cabb9bcef44199bb9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis:651"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.decompositionAddEquiv_power_mul",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e0a592ac570bbe0e2ec33b991899f4e30c16d8e57439f485ecc35b54c1eb613b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis:1013"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.exponentEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c2b4f310da919a87ca89735fede3712585a223858af713f71f5e0d7a95c281fb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents:2166"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.instCommRingPowerModule",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c41220f1acc6d5c8986fb72997c837fa2e9d2a21f9e1fc6a1cfed8b356327184",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis:4048"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.instCommSemiringPowerModule",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8a707a1519ffe15370c253bc70d1ac5aef505acc8e2764bf02eecd0c5e050e27",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis:1923"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.powerAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8ac65fb160e6e7917339c1999d6db0ffecf71b97466400df83a93901d98c2f99",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis:2144"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.powerSubstitution",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverSubstitution",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0f764fdc929cdd973233c7cee0a7a1979528f21fb68ae1167bfeadc8046aec23",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverSubstitution",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverSubstitution:953"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.powerSubstitution_X",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverSubstitution",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "478064bd6318f865c14002d3498735b77bd415752aedffb15d579463363b9577",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverSubstitution",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverSubstitution:1107"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.powerSubstitution_eq_mapDomainAlgHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverSubstitution",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4c53f80a5a201ac2a36c31c194e006d1381535487154a7cd081c6255a2515ff1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverSubstitution",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverSubstitution:1308"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.powerSubstitution_monomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverSubstitution",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3ed98e4274cabd3ff964381a7ad292093085e80e3b40972d7b2aacd177ee474b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverSubstitution",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverSubstitution:1816"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.quotient",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b5c3a9cd7523d594c4699a6e5a62b56454234bbfd87f8e71261ac4dcbde28db7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents:291"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.quotient_add_scale",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7e816f8bf081261433c64366ce2b0b012e795a20e088941bdcef5939280bb566",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents:2816"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.quotient_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6cf9289f43ee610f2b61b65de8207b86d2312362267d9336d536b4348e295fd9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents:859"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.quotient_combine",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e7284c0fa4e5b434b787f82bd9b080b706a5d839c77053d77ff41fc16bf89ff5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents:1622"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.residue",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "35f18a9e60b604f4a5073f2af3b4ee629a1be0c626083407bb6b8c4db3249b4d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents:417"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.residue_add_scale",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "60903981891d06518bdd09c1e812df889119208ce553975190b647acb15b4efd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents:3087"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.residue_combine",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ad86c61cb14ba8a4191b2dbecfc65284c79f0851134f4892be664201cdefc32f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents:1915"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_014.jsonl"
