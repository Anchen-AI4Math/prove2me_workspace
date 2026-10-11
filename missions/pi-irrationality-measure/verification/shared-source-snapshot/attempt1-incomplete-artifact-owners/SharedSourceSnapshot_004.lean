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
      sourceName := "OAI.PiExponent.CurveCycle.reducedComponentStalkPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ReducedComponentStalk",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bbcf2c4527ca098a6475737aebaf406e3f168016ce4a2d2864c30e35d160f842",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ReducedComponentStalk",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ReducedComponentStalk:2137"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.reducedComponent_closed",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a4e9218bd1fc2e2a0a78299d3ef59a014daa4996d31588da3c57633d21c79916",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentMultiplicity",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentMultiplicity:2759"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.reducedComponent_integral",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "56fdfd3b115a63e8cae1f471a176b9bb94261a2537e61903a108097f14039048",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentMultiplicity",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentMultiplicity:3112"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.reducedComponent\u03b9",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentMultiplicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "af15ec0f30db636782ad7a0a15e307c8382b0f1dff7c401273efda84a42a4e38",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentMultiplicity",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentMultiplicity:2509"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.reducedComponent\u03b9_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ReducedComponentStalk",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0f929dda803ca76fc444f688a6fe38e251b24353dd3bfd1f975beda98d6483d2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ReducedComponentStalk",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ReducedComponentStalk:669"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.reducedComponent\u03b9_range",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ReducedComponentStalk",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "57e43430757d0bcc7e2bacd4c14b7786a34db62d0c2842230eef5b1706611828",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ReducedComponentStalk",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ReducedComponentStalk:280"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.reducedComponent\u03b9_stalkMap_ker",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ReducedComponentStalk",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1a3f6dce78dd0d3791569253e19c49343dd8c87260e68f0aa91c63f19c7fbeb3",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ReducedComponentStalk:2437",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ReducedComponentStalk:2437"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.regular_section_tensor_euler_eq_cycle",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveCycleEuler",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "388809ea508123cf62fb6ecaf3f1327828cb377fb6a181b13939649f71ec962e",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveCycleEuler:3468",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveCycleEuler:3468"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.regular_section_tensor_euler_eq_lengths",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveRegularEuler",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a4fb6f6d73f7b50593f972d9bb166562e0d28cab4b5c9a71fc2a64f2efc1a3a1",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveRegularEuler:379",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveRegularEuler:379"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.sectionZeroIncidenceEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentIncidence",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c6496b24664180bfef67674dfa0ff42adb774aaff7a4fe2bf61aec7e96c1ac24",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentIncidence",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentIncidence:271"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.stalkLength",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveCycleLengths",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e1e010f440757f1b7adf369d8fd345461a68862fad8b2fefb4f25c0d8022837c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveCycleLengths",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveCycleLengths:403"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.stalkMinimalPrimesEquivComponentsThrough",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "51c7f1321f888917b298333a7741517bbe90d91acb7588acc0bdc207f0e13c31",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks:4625"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.stalkMinimalPrimesEquivComponentsThrough_point",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f3c98c53cb9b928044a6caf6192953508fb694941ff46cd54c657f37302d4e77",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks:5002"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.sum_component_zero_incidence",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentIncidence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ad5b5d06ae696d9a8c8fbba6ec9071a6ad45c44520cbcea29d14bba296df3ca3",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentIncidence:1460",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentIncidence:1460"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.tensor_euler_add",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveTensorEuler",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b5921cea327b88d2661d04f66bb37f012bf228fe13eb2bd4860284f3a9a70649",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveTensorEuler:1111",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveTensorEuler:1111"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.tensor_euler_eq_cycle",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveCycleEuler",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8fc3262f38bec7266dcb7b99a5baf2aaa17f87da5c950350cd0180d1e9492b45",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveCycleEuler:6551",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveCycleEuler:6551"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.zero_lengthNat_eq_component_sum",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveCycleLengths",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "94ed7b269cdd98f7d08764afe8d8e43274ba858f908340e1c6a5bb77ad654ea5",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveCycleLengths:2510",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveCycleLengths:2510"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.zero_stalk_length_eq_minimalPrimeCutSum",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalAssociativity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b6c57288071b9726dcf27b50f19ad1346f21d79498786c1b75775aee7a71d4ba",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalAssociativity:1438",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalAssociativity:1438"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.zero_stalk_length_ne_top",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalAssociativity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cf0457837424840208d371364c145a6564bac288b52e7b409d5e90f3ee7a204a",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalAssociativity:2803",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalAssociativity:2803"
    },
    {
      sourceName := "OAI.PiExponent.CurveDegree.FiniteLineCohomology",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveDegreeAdditivity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0b0a8726ba1f8c052d8fb741622bb6439c3c7deb33eb9e14d053dc235626a325",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveDegreeAdditivity",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveDegreeAdditivity:713"
    },
    {
      sourceName := "OAI.PiExponent.CurveDegree.LineCohomologyTwoZero",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveDegreeAdditivity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d88b1cbc0f5ef53ba7ae1dd6b170f531959da04a2f304366d988c394ba36f18c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveDegreeAdditivity",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveDegreeAdditivity:943"
    },
    {
      sourceName := "OAI.PiExponent.CurveDegree.ample_euler_degree_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleCurveDegreePositive",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8beb2dba46931b60aecf0d8b261397938c790292ef8ef4dbccf85697f540b328",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleCurveDegreePositive:4787",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleCurveDegreePositive:4787"
    },
    {
      sourceName := "OAI.PiExponent.CurveDegree.exists_ample_section_with_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleCurveDegreePositive",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "674fd4169e00e18a25f1f0e6d2dc7e748ba7b6712e858f261974706f69e23688",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleCurveDegreePositive:596",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleCurveDegreePositive:596"
    },
    {
      sourceName := "OAI.PiExponent.CurveDegree.exists_effective_twist",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveEffectiveTwist",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "30ef30811b535aeedfde35156dd9f0e426fe4f500f0fb36846adba842063e515",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveEffectiveTwist",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveEffectiveTwist:3420"
    },
    {
      sourceName := "OAI.PiExponent.CurveDegree.lineBundle_not_isZero",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveEffectiveTwist",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5fc2370100a97ff6b556b8bef524b59fb301fdcab1ff4d50381fe94a7de5ad49",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveEffectiveTwist",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveEffectiveTwist:1540"
    },
    {
      sourceName := "OAI.PiExponent.CurveDegree.nonzero_section_of_generators",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveEffectiveTwist",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f0948130e8ad618418c38d6aad2f6b848083fd5f23e9deb8fef6864702515562",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveEffectiveTwist",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveEffectiveTwist:2922"
    },
    {
      sourceName := "OAI.PiExponent.CurveDegree.section_euler_degree_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleCurveDegreePositive",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9310ec7bd50619d286c224168a66092f43d20374c54db47191e93082d3ad4af8",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleCurveDegreePositive:2229",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleCurveDegreePositive:2229"
    },
    {
      sourceName := "OAI.PiExponent.CurveDegree.section_ne_zero_of_mem_isoOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveEffectiveTwist",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e38ccb5184588b28ebac9c2b081c05d6459535b3e67c1120995218c42b643927",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveEffectiveTwist",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveEffectiveTwist:2284"
    },
    {
      sourceName := "OAI.PiExponent.CurveDegree.section_tensor_euler_add",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveDegreeAdditivity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2ca61be236beb6dcf37fc4e7d6e12b6302f2cca2597dc76812e1e8fd671fa46c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveDegreeAdditivity",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveDegreeAdditivity:1060"
    },
    {
      sourceName := "OAI.PiExponent.CurveDegree.tensor_euler_add",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveDegreeAdditivity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4b8598a6e1e1e4a155aa6e06fdc162d7f7eafe24c89bc1adf9b11fc29c7e0d2f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveDegreeAdditivity",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveDegreeAdditivity:3572"
    },
    {
      sourceName := "OAI.PiExponent.CurveDegree.twistLineIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveEffectiveTwist",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9f31c621d06879803cc4720c6ce6a7e31d7eeebb988b465250d889e89d43c48b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveEffectiveTwist",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveEffectiveTwist:3195"
    },
    {
      sourceName := "OAI.PiExponent.CurveDerivativeVanishing.logarithmic_words_vanish",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveDerivativeVanishing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cb1ba841c6e6273ae141c07f6808675fd9fdd3ff257bcfb31c41ebb35c0ebe9a",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveDerivativeVanishing:561",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveDerivativeVanishing:561"
    },
    {
      sourceName := "OAI.PiExponent.CurveDerivativeVanishing.ordinary_words_vanish",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveDerivativeVanishing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "99d062b08116ad322dab5d9eafbd2fcaf4a5342af1ce82ff9d61ac34f2178f01",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveDerivativeVanishing:3981",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveDerivativeVanishing:3981"
    },
    {
      sourceName := "OAI.PiExponent.CurveFieldRigidity.coordinateKernel",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveFieldRigidity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4b01e6c0fa26ecd83601b37ad35039c835461f3461cd09a66ae783c72017a42e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveFieldRigidity",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveFieldRigidity:372"
    },
    {
      sourceName := "OAI.PiExponent.CurveFieldRigidity.coordinateKernel_isPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveFieldRigidity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6bab46c6786abdc9c5a3b76748dc21b89c8db4c185ddac54fcb52e0f4362bba2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveFieldRigidity",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveFieldRigidity:510"
    },
    {
      sourceName := "OAI.PiExponent.CurveFieldRigidity.logarithmic_coordinate_eq_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveFieldRigidity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "650c8dc447ec46d4161d7be9c440f0c32327df7ee06dfcbe1f716a990dade532",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveFieldRigidity:810",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveFieldRigidity:810"
    },
    {
      sourceName := "OAI.PiExponent.CurveFinitePushforwardCoherent.affine_pushforward_exists_finitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveFinitePushforwardCoherent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "98ceccb4f2dd18713a6730dd2372565e859f3cb98e4682645ffcb2978176619b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveFinitePushforwardCoherent",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveFinitePushforwardCoherent:1701"
    },
    {
      sourceName := "OAI.PiExponent.CurveFinitePushforwardCoherent.affine_pushforward_sections_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveFinitePushforwardCoherent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8a7297b319129696ff27cce57a9814fd007053401674ac4b7a59e0e0980a08b8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveFinitePushforwardCoherent",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveFinitePushforwardCoherent:623"
    },
    {
      sourceName := "OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveFinitePushforwardCoherent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "550f60c81ee7d22d6b77fe127adca4de143211c30e8b59195ae7481f763b847c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveFinitePushforwardCoherent",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveFinitePushforwardCoherent:2193"
    },
    {
      sourceName := "OAI.PiExponent.CurveFinitePushforwardCohomology.baseScalars_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveFinitePushforwardCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5ae307a6a39aaa9cf838643d866c5afb5e03a2c6b0075b5d1bd5ef191904909a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveFinitePushforwardCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveFinitePushforwardCohomology:7716"
    },
    {
      sourceName := "OAI.PiExponent.CurveFinitePushforwardCohomology.cohomologyDimension_pushforward",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveFinitePushforwardCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8738d849812c55fd189f6b805fca237c5be77ea72ffe8144278bc27b68d6ea1e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveFinitePushforwardCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveFinitePushforwardCohomology:7972"
    },
    {
      sourceName := "OAI.PiExponent.CurveFinitePushforwardCohomology.cohomologyLowEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveFinitePushforwardCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "acda84977d769980a9db5707ccdd453ae47c883b1a6aa4f8ac5402c0874192d0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveFinitePushforwardCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveFinitePushforwardCohomology:5075"
    },
    {
      sourceName := "OAI.PiExponent.CurveFinitePushforwardCohomology.cohomologyOneEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveFinitePushforwardCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f682f300afaaa4c6a83c2ff79cb6f35bf88e499eea3547e62b9dfc9448663c34",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveFinitePushforwardCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveFinitePushforwardCohomology:2252"
    },
    {
      sourceName := "OAI.PiExponent.CurveFinitePushforwardCohomology.cohomologyZeroEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveFinitePushforwardCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6e3149c89bdf110d7586116494c18ea0577e201b74e2afa28a56e10ee21d713d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveFinitePushforwardCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveFinitePushforwardCohomology:4349"
    },
    {
      sourceName := "OAI.PiExponent.CurveFinitePushforwardCohomology.euler_one_pushforward",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveFinitePushforwardCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0bbd59a7312888cd546db186a519c650770d7dbc7d3b535a23bbe88d2206e118",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveFinitePushforwardCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveFinitePushforwardCohomology:8777"
    },
    {
      sourceName := "OAI.PiExponent.CurveFinitePushforwardCohomology.finiteDimensional_pushforward",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveFinitePushforwardCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "08557c563db52c9a3bc1ad9823d0f390b8eee4f347f491011f6be2e8149d49d6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveFinitePushforwardCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveFinitePushforwardCohomology:6770"
    },
    {
      sourceName := "OAI.PiExponent.CurveFinitePushforwardCohomology.sectionsEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveFinitePushforwardCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e022e54df2f9c4ed39d3f0820f90073050dbca8a7fd302747cdb7193fbda2a4f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveFinitePushforwardCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveFinitePushforwardCohomology:404"
    },
    {
      sourceName := "OAI.PiExponent.CurveFinitePushforwardCohomology.sectionsEquiv_image",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveFinitePushforwardCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "14f4275a58991ca32fdca82d0cf32487604aa568f14c39c9fcdd29f7b8b92b7f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveFinitePushforwardCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveFinitePushforwardCohomology:1125"
    },
    {
      sourceName := "OAI.PiExponent.CurveFinitePushforwardCohomology.zeroSections",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveFinitePushforwardCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7f72defc33fa2b1e5e03eef7b37ab49373b56aee003721b9efc2877e7927ea65",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveFinitePushforwardCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveFinitePushforwardCohomology:3645"
    },
    {
      sourceName := "OAI.PiExponent.CurveGeometricFunctionField.coordinates",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveGeometricFunctionField",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f795832301dd0ac977252128e4dae2448f635bf75625ee61e8486a0f7643d4cc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveGeometricFunctionField",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveGeometricFunctionField:1381"
    },
    {
      sourceName := "OAI.PiExponent.CurveGlobalCoordinateOrder.coordinateSection_ne_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveGlobalCoordinateOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "56cd2ac51348bbb22a19795dc6a54519c547e216b44a209e7a45d6aebc0a00ef",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveGlobalCoordinateOrder",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveGlobalCoordinateOrder:1201"
    },
    {
      sourceName := "OAI.PiExponent.CurveGlobalCoordinateOrder.coordinate_divisor_order",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveGlobalCoordinateOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9930deb925bc303edf006c07f50c89a3957f515573ff0dd8660a52e7afd0d2bf",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveGlobalCoordinateOrder",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveGlobalCoordinateOrder:2753"
    },
    {
      sourceName := "OAI.PiExponent.CurveGlobalMonomial.exists_parameterCurve_extension",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveGlobalMonomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e8203a600311442bef8f660bcd8e9338e193ec7fd65a2679f0961a57d871eb14",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveGlobalMonomial:929",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveGlobalMonomial:929"
    },
    {
      sourceName := "OAI.PiExponent.CurveGlobalMonomialLocal.centerMorphism_eq_latticeProjectiveMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveGlobalMonomialLocal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "303d2b9871345ae6e314b3434d335ffecdd76780a0f3cd03979bbd1cf47d5641",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveGlobalMonomialLocal",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveGlobalMonomialLocal:5468"
    },
    {
      sourceName := "OAI.PiExponent.CurveGlobalMonomialLocal.genericMonomialMap_comp_projectiveMonomialMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveGlobalMonomialLocal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "028cf5d6b4d9b70a6857e5f2ef4b00ee30dada118353971b20b6fee7835afb0e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveGlobalMonomialLocal",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveGlobalMonomialLocal:4317"
    },
    {
      sourceName := "OAI.PiExponent.CurveGlobalMonomialLocal.latticeProjectiveMap_generic",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveGlobalMonomialLocal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b83175e214dde939c6911d2c15ecfcf9c17039d344c6dcd0e71030158b197f6b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveGlobalMonomialLocal",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveGlobalMonomialLocal:2604"
    },
    {
      sourceName := "OAI.PiExponent.CurveGlobalMonomialLocal.monomialCoordinates",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveGlobalMonomialLocal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f9ba1d29bffa9b16e6fb3baf4dec9a9443871001c58398515b76b871f1300bda",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveGlobalMonomialLocal",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveGlobalMonomialLocal:3485"
    },
    {
      sourceName := "OAI.PiExponent.CurveGlobalMonomialLocal.monomialCoordinates_eq_prod",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveGlobalMonomialLocal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ba8b307997b2eed02ef1f553f6ca2898376ba0ccd39d42db100a2738d40cb83e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveGlobalMonomialLocal",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveGlobalMonomialLocal:3686"
    },
    {
      sourceName := "OAI.PiExponent.CurveGlobalMonomialLocal.monomialCoordinates_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveGlobalMonomialLocal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6f5a75d99f5289d9a774fb8c07c1b072d695bac33fcdbb5be6808c74c98aa2e4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveGlobalMonomialLocal",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveGlobalMonomialLocal:4052"
    },
    {
      sourceName := "OAI.PiExponent.CurveImageAffineCoordinates.affinePart",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveImageAffineChart",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "14fdd52e483ff733454f8f9dc9f78038f1ab7e5e297efabdec77c16eed68dfc9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveImageAffineChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveImageAffineChart:264"
    },
    {
      sourceName := "OAI.PiExponent.CurveImageAffineCoordinates.affinePart_nonempty",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveImageAffineChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "922d18d6264b6f77d52de1fb1da6918bab530839782903ee388f9869359e7559",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveImageAffineChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveImageAffineChart:2351"
    },
    {
      sourceName := "OAI.PiExponent.CurveImageAffineCoordinates.affinePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveImageAffineChart",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "06e4e156025aa3fe939e63174235c8fd054dc6fa2965ee647d85f620bc2ee1a1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveImageAffineChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveImageAffineChart:480"
    },
    {
      sourceName := "OAI.PiExponent.CurveImageAffineCoordinates.affinePresentation_isClosedImmersion",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveImageAffineChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "61b9b806698c5038179d49a9874a8dd6f3ed016e2c3b521d2a363eb987dbc2de",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveImageAffineChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveImageAffineChart:773"
    },
    {
      sourceName := "OAI.PiExponent.CurveImageAffineCoordinates.coordinates",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveImageAffineCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9303b2bbd09d8793202373e69375fc7f0a06416768b495b629289f83a50c523c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveImageAffineCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveImageAffineCoordinates:1985"
    },
    {
      sourceName := "OAI.PiExponent.CurveImageAffineCoordinates.coordinates_generic_map",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveImageAffineCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3750bbc87bdb6917c22068310d0244e5bcbf58878b2e0a36a5d1b767fdf001ac",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveImageAffineCoordinates:3347",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveImageAffineCoordinates:3347"
    },
    {
      sourceName := "OAI.PiExponent.CurveImageAffineCoordinates.fieldAlgEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveImageAffineCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b6e8862e541df50d716943425564d90d2cd4eca5a19216740694455413ab4f96",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveImageAffineCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveImageAffineCoordinates:5550"
    },
    {
      sourceName := "OAI.PiExponent.CurveImageAffineCoordinates.presentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveImageAffineCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1a2ba53c289e3bfba6fbfebb5f3c7aaa619b706fe8634ed538fd576055df5d30",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveImageAffineCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveImageAffineCoordinates:1183"
    },
    {
      sourceName := "OAI.PiExponent.CurveInequality.excess_implies_fibre_coordinate_constant",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveInequality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "89d1bb9ffd31f2585e1eaa3d087f35967fb12af3f7f8c615acac0e89bc8e39df",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveInequality:3152",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveInequality:3152"
    },
    {
      sourceName := "OAI.PiExponent.CurveInequality.excess_implies_zeroth_eq_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveInequality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "131aaba4e733604cab7c1fd72fb5b41788e6f3dc3bbd24d68f69899074ac0de4",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveInequality:653",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveInequality:653"
    },
    {
      sourceName := "OAI.PiExponent.CurveInequality.no_fibre_excess_of_constant_coordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveInequality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "21502de6ec2d0d3cd8cb0023c3f8b179406313c6643923c16f14fcb00282e93f",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveInequality:5871",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveInequality:5871"
    },
    {
      sourceName := "OAI.PiExponent.CurveInequality.nonconstant_coordinates",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveInequalityIntrinsic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "db82f0071b98843d178669a54407bda996a168712bc664ea766c8159ada718a5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveInequalityIntrinsic",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveInequalityIntrinsic:505"
    },
    {
      sourceName := "OAI.PiExponent.CurveLocalOrder.enatToIntegerOrder",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4590f88370eca9a532ffb7905c28977648c965d34e251a7d669a5a9d32c3aa8d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder:998"
    },
    {
      sourceName := "OAI.PiExponent.CurveLocalOrder.enatToIntegerOrder_eq_top_iff",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8c4ac4b0e896c83f58f30adc5c3cfbe23d84289fc852807789a4f39c1fd74c75",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder:1382"
    },
    {
      sourceName := "OAI.PiExponent.CurveLocalOrder.enatToIntegerOrder_monotone",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "69610d73d507f4f8675234ea708c17ef903010b7fe45a37aaa20771f0df1541d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder:1513"
    },
    {
      sourceName := "OAI.PiExponent.CurveLocalOrder.enatToIntegerOrder_natCast",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aaeeb1fef5d33d1e3964eecc0af3232814315eb72853ecb65d38800619c44d39",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder:1271"
    },
    {
      sourceName := "OAI.PiExponent.CurveLocalOrder.enatToIntegerOrder_top",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "87be7b85f2846f9e9349382d8663d4510932611c2aa5dbaa842482a8fdd53b3e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder:1191"
    },
    {
      sourceName := "OAI.PiExponent.CurveLocalOrder.fractionAddValuation",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "90e694b648c6c1c5458d0d411608fa03681caf01b6cc5150fbe574567891769b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder:2805"
    },
    {
      sourceName := "OAI.PiExponent.CurveLocalOrder.fractionAddValuation_algebraMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fe454fac47c5dfa5bbeb83b880ad085fe42820916bf905097a20cb9da7b09db3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder:3137"
    },
    {
      sourceName := "OAI.PiExponent.CurveLocalOrder.fraction_order_eq_principal_colength",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "24308cfca1f6f9bebdc3c61bb54ccf999c465dad5d25422ffb0d84cdaa2ad332",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder:3533"
    },
    {
      sourceName := "OAI.PiExponent.CurveLocalOrder.integerOrder_field_image_eq_length",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ee37a81816b597fa5aac04a95df9e223c1cb3ebf9532889a71b715639beee552",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder:4253"
    },
    {
      sourceName := "OAI.PiExponent.CurveLocalOrder.length_quotient_span_eq_addVal",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d04fb6ca877dfb4eb0a2bdb1f9bc9f9acdee4ce2260f449ab75e5feac5b73ed1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder:376"
    },
    {
      sourceName := "OAI.PiExponent.CurveLocalOrder.localAddValuation",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "66bf7e107fa35090e2810b192c44333a50590b5cbfa1b69573c59be48c5db4e7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder:1692"
    },
    {
      sourceName := "OAI.PiExponent.CurveLocalOrder.localAddValuation_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ca92cc4d49d29fec9c001b53c3505ec20ce0e024a52ed2d5b6d8e061b0adb3d9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder:1958"
    },
    {
      sourceName := "OAI.PiExponent.CurveLocalOrder.localAddValuation_eq_top_iff",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "61c31109a2a6d78db35ed6f526cb08bfab42ef601a6a1ebc44fc7731beaca1d8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder:2174"
    },
    {
      sourceName := "OAI.PiExponent.CurveLocalOrder.nonZeroDivisors_le_primeCompl",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d133e7971fe0e4145f64dc723626b33ca30237a365e71cb1567a4154f5b2786d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder:2463"
    },
    {
      sourceName := "OAI.PiExponent.CurveLocalOrder.principal_colength_ne_top",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4040119b10fb040d4d631f36ab90fa3125cbd9eec07d2b67719ad167f8aa4ca6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder:3958"
    },
    {
      sourceName := "OAI.PiExponent.CurveLocalOrder.residueAugmentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a7638b28cb2147bab21458a97571ed9946fe72587058fc1e1062f7dd6cc7809a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder:8573"
    },
    {
      sourceName := "OAI.PiExponent.CurveLocalOrder.residueAugmentation_algebraMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f315209f834c945140d86b5903ddb19d10c10bac4041b7e42db961f5ddf37c38",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder:8851"
    },
    {
      sourceName := "OAI.PiExponent.CurveLocalOrder.residueCoefficientEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "343fbc1a0a307d632b22896f58b3f99dd5be8b13b8d16753826c0aba30744460",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder:8212"
    },
    {
      sourceName := "OAI.PiExponent.CurveModelLocalOrder.addVal_ringEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveModelLocalOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b6b349850e45d9b6fd81d5b9a6bbbece6b2d1494359b2e4c509a606a0370f22d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveModelLocalOrder",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveModelLocalOrder:4382"
    },
    {
      sourceName := "OAI.PiExponent.CurveModelPlaces.center_images_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c1a97787f21539d932a8284f301d227bd608147faa4a4a6452fc9a6974d0b66b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces:12510"
    },
    {
      sourceName := "OAI.PiExponent.CurveModelPlaces.chartCenter",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dfddf3a9fadf0374175578a7466de49c89e24a65845ca1c509b2a585e89f04b2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces:2175"
    },
    {
      sourceName := "OAI.PiExponent.CurveModelPlaces.chartCenter_chartPlace",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0e6b15b1b6f5721fb628c85bf0fd6c3a35d7a56bb9094dbd6bf5beebbff679b1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces:7925"
    },
    {
      sourceName := "OAI.PiExponent.CurveModelPlaces.chartPlace",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2ad0c44bde72372d017abec20093806f87e6b0c942598eedb7fa06f8d754571e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces:5880"
    },
    {
      sourceName := "OAI.PiExponent.CurveModelPlaces.chartPlace_chartCenter",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "948e16fbb2e73e420606cbbdae560b15bb0e400371eefea9571f53c8037069e0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces:7540"
    },
    {
      sourceName := "OAI.PiExponent.CurveModelPlaces.chartPlace_parameter_nonneg",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "767ecb97a464e5fc475bd7b67b6eb1e875f6accf2f2f7c1f5fb0d12bdc3ed127",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces:6805"
    },
    {
      sourceName := "OAI.PiExponent.CurveModelPlaces.chartValuation",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "beb0f58846f717e4ee3e632ab99162209715aa2da9e36ccdb8b6d46dbf353bc0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces:2649"
    },
    {
      sourceName := "OAI.PiExponent.CurveModelPlaces.chartValuation_nonneg",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "be084e27382172ae245f7aaeb3180642d57c32f72ecc214ad151ea26005ef984",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces:4741"
    },
    {
      sourceName := "OAI.PiExponent.CurveModelPlaces.chartValuation_positive_iff",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "69dde1a0983e8ea85f66e18b8e306ec029d9b144884fb7f89a875b9897f52c5f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces:5301"
    },
    {
      sourceName := "OAI.PiExponent.CurveModelPlaces.exists_placePoint_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bde8bc43eba2197a9f12dc05541f755fc8b90f1d191d5a64caa9c2aac1a458a0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces:20642"
    },
    {
      sourceName := "OAI.PiExponent.CurveModelPlaces.inverse_positive_of_not_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fa2cc7ef28606e98c4917b8e10260d3c7097018f4c07aeb552c7f804991ef730",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces:13857"
    },
    {
      sourceName := "OAI.PiExponent.CurveModelPlaces.laurentCenter",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2d163d6b4bfff07b363000265eda3a2762bd33bc36848a5453e8adf4252c75e1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces:11227"
    },
    {
      sourceName := "OAI.PiExponent.CurveModelPlaces.laurentCenter_infinity",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a98c1666e6056cc73096c835a9c37e61c39d155d3a55252f5332c2b40fdb4211",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces:12043"
    },
    {
      sourceName := "OAI.PiExponent.CurveModelPlaces.laurentCenter_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4d732b727a318cd65bb86abdc40858b8e6dda016aa0fc4f60df31f1deed3b9c3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces:11628"
    },
    {
      sourceName := "OAI.PiExponent.CurveModelPlaces.laurentValuationHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ba16be84226214f18233b9f1b06db2bbda055c58a249f4ca915dd057c5f9eebb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces:10775"
    },
    {
      sourceName := "OAI.PiExponent.CurveModelPlaces.parameterLaurentChart_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "edb86667fabc015eba027a417c46f12664e8df000f28d4d6a0e30ce80eeaf79f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces:10288"
    },
    {
      sourceName := "OAI.PiExponent.CurveModelPlaces.parameterLaurentMap_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ce3ea3c71d46c405032b908234c6e36d0ee4313c0c9e07d11b492308349ab208",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces:9123"
    },
    {
      sourceName := "OAI.PiExponent.CurveModelPlaces.parameterValuationCenter_ne_bot",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "41ca24da2f51f800a53cca0588982f295a8e17563ce5828438d12926e267b437",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces:567"
    },
    {
      sourceName := "OAI.PiExponent.CurveModelPlaces.placePoint",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "772545b98e5ed78ddd1e07a2a197898cebbb284f8cddb4e78c7797189455123a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces:14166"
    },
    {
      sourceName := "OAI.PiExponent.CurveModelPlaces.placePoint_eq_infinity",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "02419dd8a3075b2261afe9af785c96bd4bf62bb2914288b121334bf9a38711b8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces:15088"
    },
    {
      sourceName := "OAI.PiExponent.CurveModelPlaces.placePoint_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "13ccfdbf40e097b6aff19e655248e6f716888a3b05aa5fb81d56a594e27dbf04",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces:14720"
    },
    {
      sourceName := "OAI.PiExponent.CurveModelPlaces.placePoint_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "279ca7bb6a3910f0b26c4ae40f8d0fc960f11d8db097e1890f8067df58884799",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces:19330"
    },
    {
      sourceName := "OAI.PiExponent.CurveModelPlaces.placePoint_mem_zero_iff",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f076452351bd32179b2df1a61cb636c94d346a256b43a05d1802461a793c32a5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces:17657"
    },
    {
      sourceName := "OAI.PiExponent.CurveModelPlaces.placePoint_ne_genericPoint",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "663f8cbb3e79e86c2991add87374532b8aa54840ac35664d8c3c826b4ed440d5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces:15627"
    },
    {
      sourceName := "OAI.PiExponent.CurveModelPlaces.placesEquivNongenericPoints",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e397c49cef0c309052a2dd3b910ee898a81c7a6dc63592559bc709083ea8f771",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces:22783"
    },
    {
      sourceName := "OAI.PiExponent.CurveModelPlaces.regular_center_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e4e5ad4b5b6ff086449fcea9b7e5e5a32cf2a53d1de608b5451e401f150f10be",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces:16869"
    },
    {
      sourceName := "OAI.PiExponent.CurveModelPlaces.regular_iff_inverse_not_positive",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1a07e92cf39efdaffd3dcb36e2c410e31a743fce54d0cddba6bca094da3e50e8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces:13227"
    },
    {
      sourceName := "OAI.PiExponent.CurveModelPlaces.valuation_eq_chartCenter",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a0eff494b00b77889965dfcc0d7334053f537830203c626dd9f9de654e79c2d0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces:3327"
    },
    {
      sourceName := "OAI.PiExponent.CurveMonomialMap.affineChartMap_projection",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveMonomialMap",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "342687c06cfc5516340fb5e458dee9aaa7f3deecca7bc3ed38b16a94981cecc6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveMonomialMap",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveMonomialMap:1296"
    },
    {
      sourceName := "OAI.PiExponent.CurveMonomialMap.fromUnitCoordinate_projection",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveMonomialMap",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2f32e9a1c1d9ee18cb96bbac01f366041144f03da6a3803826ddbade4ffd1108",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveMonomialMap",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveMonomialMap:415"
    },
    {
      sourceName := "OAI.PiExponent.CurveMonomialMap.genericMonomialMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveMonomialMap",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "507b092ce1961b33de0c2ee6e255a1db0602b63495d1e4bb637f618319564ad5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveMonomialMap",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveMonomialMap:1861"
    },
    {
      sourceName := "OAI.PiExponent.CurveMorphismFinite.isClosed_singleton_of_ne_genericPoint",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveMorphismFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b98204fe2a754ac0e5a9d859a7c5b94ed47301c1907f8546ec56fcb05ee8792e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveMorphismFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveMorphismFinite:311"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationDegree.LowCohomologyFinite",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationEuler",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "058823cde322225349ff8a33b0ab7b0c2fa8e503876cad77d7c9d88eec45bb38",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationEuler",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationEuler:425"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationDegree.cokernel_stalk_subsingleton",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "afc652154ff7df23e0284f1539beeb48cb09334e28c72d05463444c4d8c35d58",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDegree:530"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationDegree.cokernel_tensor_euler",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ccf5b38fdc15c311237788548602957823240fb4cd40c00ed93f2206a74c07a3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDegree:6237"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationDegree.dominant_of_iso_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationUnit",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ad88f62a0bccacfa21aa3648cd5497663fd045e1ae8c3fb36be7dd216c9dc824",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationUnit",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationUnit:996"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationDegree.finite_closed_complement",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "898b1896c8b39916fa8485722a3882f79fc114455a81792223567a0fd3b78d0d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDegree:1903"
    },
    {
      sourceName := "OAI.PiExponent.CurveNormalizationDegree.finite_support_euler",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fe5a9e892e5db0b9f98a93b97727a4b72ff3bfba6f74dccc18f21f8dfa63c6be",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDegree:3963"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_004.jsonl"
