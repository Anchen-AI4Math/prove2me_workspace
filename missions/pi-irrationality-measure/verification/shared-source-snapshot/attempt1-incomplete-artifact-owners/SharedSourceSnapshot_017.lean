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
      sourceName := "OAI.PiExponent.RamifiedLocalLength.translatedPowerLocalMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RamifiedPointMap",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7c0ee32d112b424702f1e09df22e1df4cc47e14a0b79c2fd5f3ff510342c46f2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RamifiedPointMap",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RamifiedPointMap:268"
    },
    {
      sourceName := "OAI.PiExponent.RamifiedLocalLength.translatedPowerLocalMap_isLocalHom",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RamifiedPointMap",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cffac59897d499181c1c6a5dbf14d5ac67d6ee0dc058e919ecd42b08d98c8887",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RamifiedPointMap",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RamifiedPointMap:654"
    },
    {
      sourceName := "OAI.PiExponent.RamifiedLocalLength.translatedPowerLocal_quotient_length",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RamifiedPowerLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "728f7cb79d57ccb93d8eb3390856a355f9f6bcaa8ce757d35a9c9f05c6b17213",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RamifiedPowerLength:5494",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RamifiedPowerLength:5494"
    },
    {
      sourceName := "OAI.PiExponent.ReducedComponentAmple.closedBaseChange",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleBaseChange",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b619127978b4ba514ef55f39b59195af1354602f3e58e21a7f90f62f81267eae",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleBaseChange",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleBaseChange:339"
    },
    {
      sourceName := "OAI.PiExponent.ReducedComponentAmple.closedBaseChangeLineIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleBaseChange",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4aa22839e68a8b915d0bc41cac3f5953b74ef59438d6088cf7d41a1438870ddb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleBaseChange",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleBaseChange:1002"
    },
    {
      sourceName := "OAI.PiExponent.ReducedComponentAmple.closedBaseChange_condition",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleBaseChange",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8a72a6e76d54f9e0bbdb0c4d214d7c871168651eba8203d7d0c5ffa149f9e2aa",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleBaseChange",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleBaseChange:708"
    },
    {
      sourceName := "OAI.PiExponent.ReducedComponentAmple.closedBaseChange_condition_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleBaseChange",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "61570b4753fe2fdf5248c8d4ae97adbd9a31324f3788acbd780fb68edbd2e9ff",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleBaseChange",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleBaseChange:708"
    },
    {
      sourceName := "OAI.PiExponent.ReducedComponentAmple.closedBaseChange_isClosedImmersion",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleBaseChange",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dc161a017ea6fe1dc9fc3deca2a0937d80c1ddbf5e522313e68efe95b13069b3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleBaseChange",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleBaseChange:503"
    },
    {
      sourceName := "OAI.PiExponent.ReducedComponentAmple.isAmple_of_finite_closed_cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReducedComponentAmple",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f6ac3483cdd1bd479567a86b9182bceea3acc7ef35488037e2f55e9b9ad3cd78",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReducedComponentAmple:443",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReducedComponentAmple:443"
    },
    {
      sourceName := "OAI.PiExponent.ReducedComponentAmple.isAmple_of_reduced_components",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReducedComponentAmple",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "adf926cbd4c8c1c5678d2d7c2ef6aed9cafdf1bf57de400bad8ed1a8a2c6e6f9",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReducedComponentAmple:3531",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReducedComponentAmple:3531"
    },
    {
      sourceName := "OAI.PiExponent.ReesCechInjectivity.eventually_augmentation_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesCechInjectivity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "52af07c4e09b856e5fc0d04d9315a2c174778f85e46900ed7df7da0218567a18",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesCechInjectivity:1503",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesCechInjectivity:1503"
    },
    {
      sourceName := "OAI.PiExponent.ReesCechRecovery.eventually_ordinary_power_recovery",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesCechRecovery",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5c01f1ee038fc9ba28be0498bd4b67d524cad7a36a21736c6946afebafeadbbe",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesCechRecovery:590",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesCechRecovery:590"
    },
    {
      sourceName := "OAI.PiExponent.ReesCohomologySetup.instIsNoetherianAffineBlowupOfIsNoetherianRing",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesCohomologySetup",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "94b1496bc761d88ac488dc5a8e05abf52d098c7889574d4914493cac2a3a882a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesCohomologySetup",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesCohomologySetup:315"
    },
    {
      sourceName := "OAI.PiExponent.ReesFiniteCover.adjoin_eq_top",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesFiniteCover",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e57cb3e18cc6d0953c7fbfaa3738ace3b850e4fe523812ca2d18345dd5a5779d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesFiniteCover",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesFiniteCover:571"
    },
    {
      sourceName := "OAI.PiExponent.ReesFiniteCover.adjoin_zero_eq_top",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesFiniteCover",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a17faa6822c565dea51bcb0fa9621576358c8cd0945a25e437e84b3b3fd20047",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesFiniteCover",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesFiniteCover:813"
    },
    {
      sourceName := "OAI.PiExponent.ReesFiniteCover.chartOpenImmersion",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesFiniteCover",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9fd730918b9051f482cf6731a18d832ba894424ceacab3373d0d1ed3a09eeedd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesFiniteCover",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesFiniteCover:435"
    },
    {
      sourceName := "OAI.PiExponent.ReesFiniteCover.iSup_generator_basicOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesFiniteCover",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4fe9d58f1514389a381998590a280324eef4b4019adbd362c90122eb4417df64",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesFiniteCover",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesFiniteCover:1429"
    },
    {
      sourceName := "OAI.PiExponent.ReesFiniteCover.iSup_generator_opensRange",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesFiniteCover",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a6c66b9098e4d37ea7d1978f6251f2a4aea4b775d2b7a6a580eb4ff072c46cac",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesFiniteCover",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesFiniteCover:1680"
    },
    {
      sourceName := "OAI.PiExponent.ReesFrozenChart.base",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "941534bd0b0fa908a1c700195dedc73d091701b648299c144a9e2f3c4cacec3d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart:1261"
    },
    {
      sourceName := "OAI.PiExponent.ReesFrozenChart.chart",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "649453adcbb7c603e18dfedf2cd8e0680ba193a4422a708e6b7a48646b76864a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart:1850"
    },
    {
      sourceName := "OAI.PiExponent.ReesFrozenChart.chartFrame_nonempty",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2115bc2d0b703cead05fd69eafdb5608a72eb4e2a6818181c4958a94cb83c03a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedFrames",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedFrames:825"
    },
    {
      sourceName := "OAI.PiExponent.ReesFrozenChart.chartOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "159214e621fe35caa71314f019ee7932f5071c095f1023433d402f111dc7bc1e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart:2637"
    },
    {
      sourceName := "OAI.PiExponent.ReesFrozenChart.chartOpen_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "13692b8a45a1ff461b32d16943376ccf1f8000da38f72d0b90b299200ae10b60",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart:2750"
    },
    {
      sourceName := "OAI.PiExponent.ReesFrozenChart.chart_opensRange",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cb7501f466457a37d9a63bfa8299f3aa1cb5ed8c346559e052629f9f3c417254",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart:2469"
    },
    {
      sourceName := "OAI.PiExponent.ReesFrozenChart.chart_projection",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "200f28afca686c7f41b8a148766a03751e8b6cef1b485c0f54ae24ea0f986c5b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart:2089"
    },
    {
      sourceName := "OAI.PiExponent.ReesFrozenChart.coordinateEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b9a0014bcb140069c61217e4b88199209098f71ab57328fe990d885ceb262e8d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart:978"
    },
    {
      sourceName := "OAI.PiExponent.ReesFrozenChart.coordinateInv_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4eef0b68370adf1a18f010e40e9433f463ca405064d81e785407fd14b5bea786",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart:1376"
    },
    {
      sourceName := "OAI.PiExponent.ReesFrozenChart.coordinateRing",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "86fe91bef61cb9566406caf13d9b937b947a3741c6a6ad275c8d2457bd474c69",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart:736"
    },
    {
      sourceName := "OAI.PiExponent.ReesFrozenChart.coordinateRing_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aad0cae4799a31a17c646fc86ede64bf92e8f510086581c22bff0a8bfdce880a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart:810"
    },
    {
      sourceName := "OAI.PiExponent.ReesFrozenChart.exists_coordinateRing",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ecf7f9324d94cdb91e5a09fea1b4c69b18dacd55eca123e7ebf267b722298f67",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart:597"
    },
    {
      sourceName := "OAI.PiExponent.ReesFrozenChart.frame_nonempty_congr",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "46a680c3cc64e6c778cc56242f3fae6643023f3f434be503b746a5ceb72123f4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedFrames",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedFrames:543"
    },
    {
      sourceName := "OAI.PiExponent.ReesFrozenChart.instIsOpenImmersionChart",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "feaa44e73335d6fc70687d4166d70c4edc994d9087808558a33e5c930894d4f6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart:2004"
    },
    {
      sourceName := "OAI.PiExponent.ReesFrozenChart.restriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d65978b55a60f27db970129cd2f842c99bc16333aea0ba3dc8d8bd87481a55f8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedRestriction:479"
    },
    {
      sourceName := "OAI.PiExponent.ReesFrozenChart.restriction_chart",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "87c8771e3fed88af20925e159516e8b240749ba143953eee6922e7492ee942ce",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedRestriction:1334"
    },
    {
      sourceName := "OAI.PiExponent.ReesFrozenPower.coordinate_mem_power",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedPower",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c4a6af426b83f276599b990fcc5998f8c23d05ea44d7966552ed252585c4f1d2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedPower",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedPower:856"
    },
    {
      sourceName := "OAI.PiExponent.ReesFrozenPower.coordinate_pieceEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedPower",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c891a155299060bf7112bef59dd385cf72abb1f03abf4536b11d9f90a70e39f2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedPower",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedPower:3045"
    },
    {
      sourceName := "OAI.PiExponent.ReesFrozenPower.inverse_map_power_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedPower",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7d872d6109b9f0dbc908f5696db3ccbba5f46e417b72ec73b42c94f27737baca",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedPower",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedPower:1354"
    },
    {
      sourceName := "OAI.PiExponent.ReesFrozenPower.inverse_mem_power",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedPower",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "62b06dc2d91c38ba0e75d13573a75572b7e443d34fdbc9d2d19b9444c81af658",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedPower",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedPower:1597"
    },
    {
      sourceName := "OAI.PiExponent.ReesFrozenPower.map_power_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedPower",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "06fcaf299e2c66ffb7ef7d968883158ec1fb6c37598b2de7af4ee88416852106",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedPower",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedPower:419"
    },
    {
      sourceName := "OAI.PiExponent.ReesFrozenPower.pieceEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedPower",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "11898ea780877a5c3ca2b234428118ad57f938ac41609a2f9f87a4442e1edcad",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedPower",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedPower:2834"
    },
    {
      sourceName := "OAI.PiExponent.ReesFrozenPower.pieceEquiv_restriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedPowerRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a43b0e3eddeb914002ab5b374b1a89963b78b8f7ac9aaf0b5ae777d7d5de44cc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedPowerRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedPowerRestriction:408"
    },
    {
      sourceName := "OAI.PiExponent.ReesFrozenPower.powerEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedPower",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b7e56631cbfdad73516460291ce038392cd47f4342a49fe6b8d1328dfe5c7ab7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedPower",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedPower:2116"
    },
    {
      sourceName := "OAI.PiExponent.ReesGradedModule.gradedScalarAction",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesGradedModule",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "923d76ec37be6e233dc398c5e54a49ef7144695cd84579766e782c45a848d009",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesGradedModule",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesGradedModule:2436"
    },
    {
      sourceName := "OAI.PiExponent.ReesGradedModule.integerGradedRing",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesGradedModule",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a2b36d6c345a92de230697e4a0dad9c803a30c460e99ca0f519153c0d96c2256",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesGradedModule",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesGradedModule:646"
    },
    {
      sourceName := "OAI.PiExponent.ReesGradedModule.integerPiece",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesGradedModule",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "47f184cf6d3f197f5f92c1e261b8bf0a4149d5716b4f9da68e99b7fead32b2e3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesGradedModule",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesGradedModule:547"
    },
    {
      sourceName := "OAI.PiExponent.ReesGradedModule.ordinaryPowerEquivIntegerPiece",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesGradedModule",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8bd2f0362691e1d97312bc73764f0b7c9b46512359d19f7e1970d25c837ce156",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesGradedModule",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesGradedModule:834"
    },
    {
      sourceName := "OAI.PiExponent.ReesGradedModule.polynomial_negative_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesGradedModule",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "838ff4ec6eb30f04c8c55e340611f6dcf91fcbbfb15b50cbee6edbdb39bcbe64",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesGradedModule",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesGradedModule:995"
    },
    {
      sourceName := "OAI.PiExponent.ReesGradedModule.presentation_integer_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesGradedModule",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c3e8249e071850dbe2919f990d3f8c61ac33ec788705e8a09204251b2af5b91a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesGradedModule",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesGradedModule:1375"
    },
    {
      sourceName := "OAI.PiExponent.ReesLocalizedIntersections.LocalizationModule",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesLocalizedIntersections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "056153734745c09bbb1cea9546d28e6591717c3b52df6aeb535e6a1029697cc8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesLocalizedIntersections",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesLocalizedIntersections:955"
    },
    {
      sourceName := "OAI.PiExponent.ReesLocalizedIntersections.Piece",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesLocalizedIntersections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "90f5d45c2b3d52a7898e8d6688ed3be4598f35722c5b768efa4598e0c6a7685b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesLocalizedIntersections",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesLocalizedIntersections:5962"
    },
    {
      sourceName := "OAI.PiExponent.ReesLocalizedIntersections.coefficientProduct",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesLocalizedIntersections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2e9da96b4613c18c3a2cde5501a850625dbf26ca4592e238eb0af330e472e6b3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesLocalizedIntersections",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesLocalizedIntersections:589"
    },
    {
      sourceName := "OAI.PiExponent.ReesLocalizedIntersections.coefficientRestriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesLocalizedIntersections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6500e714312e3afdab7ad2d42d51f0c07afb22f87143ca2dabcafe65e84a2661",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesLocalizedIntersections",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesLocalizedIntersections:2979"
    },
    {
      sourceName := "OAI.PiExponent.ReesLocalizedIntersections.coefficientRestriction_algebraMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesLocalizedIntersections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "169a390d1113b8bd5ad78347aab70959ddf4979e2970ad4d9806ff8f6aa2839f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesLocalizedIntersections",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesLocalizedIntersections:3337"
    },
    {
      sourceName := "OAI.PiExponent.ReesLocalizedIntersections.evaluation_presentation_product",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesLocalizedIntersections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6c2bb86b411289e349df06bc29376c70b862f882d8716c1c03985a5113fc0eb6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesLocalizedIntersections",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesLocalizedIntersections:660"
    },
    {
      sourceName := "OAI.PiExponent.ReesLocalizedIntersections.localizationEvaluation",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesLocalizedIntersections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d398c0dbade9ad78ae8d8bdef832272e3f4c3546bee0bbf4d2863b91160d90bd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesLocalizedIntersections",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesLocalizedIntersections:1155"
    },
    {
      sourceName := "OAI.PiExponent.ReesLocalizedIntersections.localizationEvaluation_fraction",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesLocalizedIntersections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "529585bae7bceed3aab26eaf4c9be076215b64af7aadc10a7d34d624b29aa469",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesLocalizedIntersections",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesLocalizedIntersections:1732"
    },
    {
      sourceName := "OAI.PiExponent.ReesLocalizedIntersections.localizationEvaluation_restriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesLocalizedIntersections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2eff9ee4ccba86d26759de49b27540022275b0444c0e237b69a3fb65a42bd0e9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesLocalizedIntersections",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesLocalizedIntersections:3681"
    },
    {
      sourceName := "OAI.PiExponent.ReesLocalizedIntersections.localizationEvaluation_smul",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesLocalizedIntersections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "72a1bef28a95cf323fc0039b933682185ec6fd51fc212f5f8776fe1b62d0e842",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesLocalizedIntersections",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesLocalizedIntersections:2495"
    },
    {
      sourceName := "OAI.PiExponent.ReesLocalizedIntersections.pieceEvaluation",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesLocalizedIntersections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ccc2d868a3d79177711ad37a4e4753ef2bba6006109a370c76b398f4005b7598",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesLocalizedIntersections",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesLocalizedIntersections:6178"
    },
    {
      sourceName := "OAI.PiExponent.ReesLocalizedIntersections.pieceEvaluation_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesLocalizedIntersections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6e96115df317ec007b50f2bebe1050c439c6d7cd66784d18ce75e77fa4369e18",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesLocalizedIntersections",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesLocalizedIntersections:6956"
    },
    {
      sourceName := "OAI.PiExponent.ReesLocalizedIntersections.pieceEvaluation_restriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesLocalizedIntersections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fb6645879b88f53c0727f74d8dfb888fa518d02f3cd3bcd04e8c908575b0938e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesLocalizedIntersections",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesLocalizedIntersections:6441"
    },
    {
      sourceName := "OAI.PiExponent.ReesPolynomialPresentation.evaluation_presentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPolynomialPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "429475490b4e87e297975ec3eedd91dd812f02029c44d3a90a773f32ee9673b9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPolynomialPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPolynomialPresentation:1932"
    },
    {
      sourceName := "OAI.PiExponent.ReesPolynomialPresentation.homogeneous_piece_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPolynomialPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "93aee9538832aac26270d2569c6a1ee455ec7f0822b2842b4b58e135ead77771",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPolynomialPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPolynomialPresentation:2406"
    },
    {
      sourceName := "OAI.PiExponent.ReesPolynomialPresentation.presentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPolynomialPresentation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "03002acb98d97193fb28c4f9dd440f11740a1a8dd9f7a55187abf7c470376336",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPolynomialPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPolynomialPresentation:351"
    },
    {
      sourceName := "OAI.PiExponent.ReesPolynomialPresentation.presentationAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPolynomialPresentation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b81549c481855c8b196c62e4800fa0cf958126fc3f73ab54cf5b1600717e823a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPolynomialPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPolynomialPresentation:3972"
    },
    {
      sourceName := "OAI.PiExponent.ReesPolynomialPresentation.presentation_X",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPolynomialPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bd45df3fc6c304554692ed820f488275672f1c2bbf3a42cc56dc11eb5a9d3227",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPolynomialPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPolynomialPresentation:468"
    },
    {
      sourceName := "OAI.PiExponent.ReesPolynomialPresentation.presentation_homogeneous_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPolynomialPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c151538fba9d8e1dd53c1d265ce5bb6c51d2751a1e7b1a631c5d75f4ca0bf92b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPolynomialPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPolynomialPresentation:1374"
    },
    {
      sourceName := "OAI.PiExponent.ReesPolynomialPresentation.presentation_monomial_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPolynomialPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "38d9062a1c91079735200614d6e18aefd7e241bb1d509ec7dda4a78b7e877ed4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPolynomialPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPolynomialPresentation:599"
    },
    {
      sourceName := "OAI.PiExponent.ReesPolynomialPresentation.presentation_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPolynomialPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ca0a94888c577b2200b3e9a21afefa734eb66e9e6fad17e47edc1ad7688d15a1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPolynomialPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPolynomialPresentation:3387"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductAugmentation.ordinaryFraction",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductAugmentation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d7b3bbdd03be66cce273b2329f3f1bb742aa4881c4f1c8788e0b40ab2d64051a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductAugmentation",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductAugmentation:626"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductChart.Chart",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "91fc8e89bcb076ca60ba6720e08aab0bc0398da4fb9933db70ea8318067f2a2a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart:1327"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductChart.base_mul_ratio",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "df30749dac79ac0cc07dfbe71c3bc843b63d99ecfddb6a55d4562e9c5ca761a0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart:5781"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductChart.chartBase",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2bfc3ec3a072471a87d861285fe122b9719fdcee98d1b19b770a1808d9914ca2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart:4111"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductChart.chartMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "78e6a663b8b07c26fd7f4be96d627e290faa7af0d3ca4c7fb85cd503f43228f0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart:1425"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductChart.chartMap_base",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c9e1967cb78f87c5c2a170a9ea4f6b4a8a3e0c855bd0d96752a5c72edfbd19af",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart:4301"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductChart.chartMap_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "24d6fa766f41131ac81669e338a10b287a9b2636ff3b2174250f404b11bd9667",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart:2614"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductChart.chartMap_mk",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "89378166411262de596dc4562370dc422111279ed9bf9bc8b7e4b371e2e0bc39",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart:1959"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductChart.chartMap_ratio",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "987367abc5d8bee3c5b2ba1d8fa1541eaa8c972726b3f35dea8bf8bb7927ea7b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart:5429"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductChart.chart_generator_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c8fe22de34d5d62c7030aa83df71844b974499c77b06f729fc17e67debd2028d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart:6966"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductChart.chart_ordinaryPower_principal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4ce335ef6071ebbe91b956f9e5bf6283290cfda4076203d5387f61036235bacd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart:6749"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductChart.coefficientProduct_eq_pivot",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d559026c63e795f1bdb5d30fa4597d56cbe36ef5516e5f64ae7987039397e302",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart:4851"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductChart.evaluation_productGenerator",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ef5c4adbe712998a7f0b31ca5cc7b55de11396975ec5585c6ae6616bc90764b9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart:891"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductChart.map_ideal_principal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aaec856b3f449cc3b4ad365461eab134569247a8aa2e29717e17c15d40b1199d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart:6282"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductChart.productGenerator",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e18c48a05d23583fc0d18e724b2321e9ae0465f71a4269a7bcd0dca6a6bf9f92",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart:573"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductChart.productGenerator_eq_prod",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "088c1d64b0fe6097a787562cbf113fefd5a460ee0fea144ec59d7cd27682e807",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart:1098"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductChart.productGenerator_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b96b63aaa1caeb72af1f6320c9cb1e20d3731d33ad0870501c8831ea6e8e247d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart:683"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductChart.ratio",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d4aa26bbd2c48d3b0790cc4cac48026c95aad3cd6541783052567c11690d4d9e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart:5062"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductPower.chartPowerEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductPower",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "32f771253721654ac39ade79fa3d6e5ff178ad5c1e12a54f35d5e563242fc426",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductPower",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductPower:6670"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductPower.chartPowerMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductPower",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bc3af5d205a7b9130358e4704b52926cf8a7e8cd3e20e847b9cb6cca3b19f3a1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductPower",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductPower:5612"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductPower.chartPowerMap_evaluation",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductPower",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6d87d647e9174de9cc2d4d7cb0a3608b4f58184f87a3023fce86d1a1a9258b45",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductPower",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductPower:6444"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductPower.chartPower_mem_pieceEvaluation",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductPower",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "76364c1d538e0d648fc812bdda3991f6c64e78d2b863701c6696fc34d40146e7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductPower",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductPower:3428"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductPower.pieceEvaluation_mem_chartPower",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductPower",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8deb34c084f8b5290dafe199adbc0549be0279fd9e682df5346e7996f3918d05",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductPower",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductPower:641"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductPowerSections.chartEquation",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "38215fedde73fee3d4bf4e21e33e1db1434a941dd5f7a055611d6d0ce2c41c17",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart:3191"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductPowerSections.chartEquation_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b76ea0ef560cc14edcf03c965fe634b1512607b51f2152e80a00dae0913499c6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart:3863"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductPowerSections.chartFrame_nonempty",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0fc878ad2776110cbff4e956e6848310d8779082b9307a15404de4ea9d7376a0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductFrames",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductFrames:940"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductPowerSections.chartMorphism",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f67028ed09be12668270bf9d71f5566ffa3872b0515b6ae1e997bfac43e626aa",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart:835"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductPowerSections.chartMorphism_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "175d0e90ebd682a01d36f673775ecc940c3f63b823bd720e312ba0a32cd9409f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart:956"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductPowerSections.chartMorphism_open",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "646fd83e8d58f7a6b6ab54bc1a1a5620bc62d6b1f80747c492d42e084eee8513",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart:1179"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductPowerSections.chartMorphism_opensRange",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "434083fcf299f0b5aa91a8861ae97afe1ccf89b269f261d10847cbdba40161cd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart:1952"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductPowerSections.chartMorphism_projection",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a8d11119331cb577aee6c1277d896b9d267b145f01624af8e6d5f0467eea6410",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart:1454"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductPowerSections.chartOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "683ab706613b3e393702eb95ad874ca9074c7701a68fcbbf366a821d903fb03c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart:3035"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductPowerSections.exceptional_chart",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4669a01a29c60067e984e6639b210a8dab7cc447c8fb2e1007f76870cd3bf72e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart:3369"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductPowerSections.exists_chartMorphism",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "71408a008eb26c380af06ba70b095a7604bd313f4f6fdc4e42989f2250979b5b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart:592"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductRestriction.chartMap_mk_homogeneous",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "af9cd49e73459ab575726e8f0cac2dccf0888151192b34fca31385bd1dc35c6d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction:1613"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductRestriction.chartMap_restriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ad0842745d4a54ecb9a3934c4ffbef48d859be1188830c0157de053845ec5cee",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction:3956"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductRestriction.chartPowerMap_restriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0ddcd4c119bd31f8d3f5a9a220819426dccbde861bcc1f3a9fd72740b020c91a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction:5484"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductRestriction.chartPowerRestriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4b73813da93e21c602f6be57bebcf63995656e261a4f01e75d29d1df966a27ca",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction:5104"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductRestriction.chartRestriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a408f28d620743fbf7b8df882c8d390828b4983fb1b0b0ce482555b1e7eff097",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction:1153"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductRestriction.chartRestriction_base",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "548b985b0a81124d71419d8c20b14826b1fa6f1217b8119b2405456eb58ad7be",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction:1364"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductRestriction.chartRestriction_power_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1ba73055da25f9ab016da2cc89060b2805274db6dbb104cfa73d18183eceaff2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction:4532"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductRestriction.coefficientProduct_factor",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ed88add132e083a14db7175962112792889f5b54340f0efb55d5372ae2dc2dae",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction:905"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductRestriction.coefficientRestriction_fraction",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e11fcd24bf50c8bcb449be29cdd51a24e22734cdbfb488cac802c2174f62a4a2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction:2381"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductRestriction.productGenerator_factor",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "97ee7c3472319192ed6ae7647afbfeae66186df411066c94815fb3fed3217246",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction:625"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductSchemeRestriction.chartRestriction_chartMorphism",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ad217e946200dba17676bcd113a2d88c1a9a9dcbfbe092b7c53065e23af08b35",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeRestriction:521"
    },
    {
      sourceName := "OAI.PiExponent.ReesPushdown.eventually_no_power_torsion",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c48f0a8b75b3b6cba838b709aa16542df029230b7a0102d6bc2fae4206019f84",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:15281",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:15281"
    },
    {
      sourceName := "OAI.PiExponent.ReesPushdown.ordinaryPowerEquivPiece",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9d3393840f5eb28a71e6a85afae6d03657c273225c930fe22c179f9bf75f3754",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:12676"
    },
    {
      sourceName := "OAI.PiExponent.ReesSectionInclusion.HasFrozenValues",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesSectionInclusion",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "53f37528bb27fae776883fb7bdfc1d2c4e223b21fa31ac7c31db54391d2219a8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesSectionInclusion",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesSectionInclusion:2165"
    },
    {
      sourceName := "OAI.PiExponent.ReesSectionInclusion.section_inclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesSectionInclusion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a040171ac55a8f2a2f89cef3056047b6de5e74573bf08606a6791f77d0d22de1",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesSectionInclusion:4929",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesSectionInclusion:4929"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechBase.chartFrameTyped",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "67fa2a9da902b1f5de69e0c1fc4a8842c843ebb47b6029a9cf34eafbf76c060a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:5570"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechBase.chartFrameTyped_nonempty",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "606cee92e76d49ea6a4acc507235ba3aeda1691238470390151323d91a49ce81",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:5149"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechBase.chartHomEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "75875eb659ccbce7b24ee19c4f123f8dbd7b73cdd231984107521407f8c17df8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:5782"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechBase.chartHomEquiv_pieceEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "78b6f18de4e50669d962ff4d582b04f6641846773d71a34be11d143fa886969b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:6167"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechBase.chartOpenImmersion",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1ac947098bfcb1556a84c64f03776f596dc7fbcfb81dd6b4e17886ea5b9b233d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:1456"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechBase.cochainEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f1375d4ea530ce81a60c23551c0f6d94594c8da56a7240e5d782864ba9e60174",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:7686"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechBase.exceptionalPower",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bd8dd6d15e21dd5fbeeb8cf8ce15e8efe3c540f2765c3689dddf446685d1535b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:2045"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechBase.freeOpenSectionsEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "58353077c01247882d9a0eb8ddb5a3a5a4d549b12aa6f7ad371cf11ecb9cbcd7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:2522"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechBase.genericChartHomEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "082499df2888b5669f169467778bb44a9706a07e1f6b718ac617833194d700de",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:4290"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechBase.iSup_opens",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "52a966d963bcba9760bb0982228a15af94803db8b2c627d85d5ab3ea23e0fde1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:8606"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_017.jsonl"
