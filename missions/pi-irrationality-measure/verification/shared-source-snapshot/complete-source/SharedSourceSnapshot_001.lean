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
      sourceName := "OAI.PiExponent.AdmissibleJetSurjectivity.eventual_jetRestriction_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AdmissibleJetSurjectivity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6180e3a32dcbee1dcb998d48a7631eb4063045b428db409edaeb73f62fea6c00",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AdmissibleJetSurjectivity:570",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AdmissibleJetSurjectivity:570"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleJetSurjectivity.eventually_jetRestriction_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AdmissibleJetSurjectivity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d2790fd3f54f5fccfb972af13eb804c06b12ec6aa563cf98855aad1d44889ddf",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AdmissibleJetSurjectivity:875",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AdmissibleJetSurjectivity:875"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleMatrixInterpolation.WeightedPolynomials",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixInterpolation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3abd81abf265e1a7e468b3f7b9a1720d5c583c507a2fee35065b28e53074306d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixInterpolation:4692",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixInterpolation:4692"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleMatrixInterpolation.actualFrame_exists",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixFrame",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "911efa439a3ff2e768fcb5cb20856107091fa528237718a386b6a3e505f747c2",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixFrame:1617",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixFrame:1617"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleMatrixInterpolation.actualMatrix_surjective_of_formalPackets",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixInterpolation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6ece6afe4fc5cf7a0c487b2bf82d311fa3cf47a04e6cbac1dea3c46112f58c0b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixInterpolation:3571",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixInterpolation:3571"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleMatrixInterpolation.actualMatrix_surjective_of_packetMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixInterpolation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "372d3d4ec4cae415c5230876e9c402e8f039b16ad951c68105f9e4c9d9e188cd",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixInterpolation:5740",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixInterpolation:5740"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleMatrixInterpolation.actual_truncation_weight_bound",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixInterpolation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8d131130f8ca98e3c737170b3411249e5a1e5549a1f1b1593ca91af4f150d617",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixInterpolation:1356",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixInterpolation:1356"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleMatrixInterpolation.cofinal_actualMatrix_of_eventual_packets",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixInterpolation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0f886413a785067ed850d49e7a00d1059e80ffa84f18a090507b2930338ae807",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixInterpolation:6300",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixInterpolation:6300"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleMatrixInterpolation.degreeWeights_eq_matrix",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixInterpolation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "63b35cafcde7f162cb3d533068dce671e68ebe73788ee0d78642284ddaa56f60",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixInterpolation:496",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixInterpolation:496"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleMatrixInterpolation.eventual_packets_of_eventual_jetRestriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixGeometry",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b402a6e5d2958adf9fc425c893965018844e6d320b8431f5bdf98c7925c9304e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixGeometry:884",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixGeometry:884"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleMatrixInterpolation.frame_exists_of_actual",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixFrame",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "057231ba61eaa8915a1642a30e3df4d985c1a3a7ece777780a810cc6c7f10852",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixFrame:474",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixFrame:474"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleMatrixInterpolation.globalInterpolation",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixGeometry",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "167b3846d2e37a2f89b03c8f812e878b3cd2718272c7b7b4a188ad5896ac6ae1",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixGeometry:1945",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixGeometry:1945"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleMatrixInterpolation.globalInterpolation_of_eventual_jetRestriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixGeometry",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2a36bfc52b1c8b7640c29c51a3739add04a3f0832f8d8b6b24dc1d6dab06aa07",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixGeometry:1513",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixGeometry:1513"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleMatrixInterpolation.globalInterpolation_of_eventual_packets",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixInterpolation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9e22f9ad7912d2d6e075adc9bdee5619d9429c467eda11fba305a4ecae0e9205",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixInterpolation:7049",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixInterpolation:7049"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleMatrixInterpolation.jetWeights_eq_matrix",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixInterpolation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9b76c5809683951a6192ed2cf3ce84695fd202af82dcac61faac14bcd0b67e84",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixInterpolation:920",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixInterpolation:920"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleMatrixInterpolation.matrix_degree_of_supportBound",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixInterpolation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ecd7b9c3e718b320af36d8879384878d3f9529bb25a8b20db675824b9d3b2303",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixInterpolation:2870",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixInterpolation:2870"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleMatrixInterpolation.monomialFrame_exists",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixFrame",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a8e12ecfa8b965dfe049c1eedc7e184555e8dfd6f4e03f15e71de99e0166048e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixFrame:849",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixFrame:849"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleMatrixInterpolation.packetMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixInterpolation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0ce2a9b1d49bcab44ced11278cd29d1ed3d5d34d8d73fbdc65679d20e0e48dc4",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixInterpolation:4901",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixInterpolation:4901"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleMatrixInterpolation.packetMap_surjective_of_family",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixInterpolation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fe967569d8b9a148468069dc4c6063d2cfdc842723e49a3d956cd754b85d75d8",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixInterpolation:5125",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixInterpolation:5125"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "inductive",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0fe91777471b27fdcbaa7b95e79c76540e1450df365beac95969f9a316b777a4",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.F0",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6e07a788a03a732dc4d1e040955770fd5dce26eb544acb52f9d2baf8fd80b4e9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.F0_large",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a63277f0cc4969bcdeddd96ec0aff89d63ec48e4c08b128d189d4f479de88688",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.F0_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "553f377f8fd6260a4647d1fde5b80befc341fd529bd0639649274dea377aee03",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.K",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2c50c7f2a73bb2f01dd7ee4d82c998476d96cdf82131cccbaa649a9563a1a536",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.K_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d833b53cf385eb31443810a0560999e1cbd3b2b4d9cb974dc64ca988f3f85ad1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.K_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "216944eb3c56c3614cd00d008cd63591465c2efce4e273c78b5076f0942d0c1d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.analyticError",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6626569054afa61ec0dc987e8a284cc42620986dc77cb84acb5baed854680a41",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:13093",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:13093"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.approximations",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aaf73660ca7aea3de373bc2aea43f228eb9b222afa662a5985f31ad91181d76f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.arithmeticError",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9e6fd74814be14863914b39dd84fffc1e4ab4051d81cb843514da48b6ad5c745",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:12604",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:12604"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.base",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0870767dac60e9e015d91e1c6914268fc5a75193947844383f584e4e3c3db6ff",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.casesOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fb122f4f0b80a12f44aed313a371e2c56be9d5ba5dc4d3df903cf2b680cfc844",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.cast_rationalWeight",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "97c9500758cc1b110964abd42b4db9ecccf610b3a8c7cfc58cb103c980de8070",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:9601",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:9601"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.collision_exceeds_error_sum",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a3d538fe77ae14b71512b61a5bfa2242de9af54cf27e64f1512c12bb44a1b2b6",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:13825",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:13825"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.collision_exceeds_one_add_error",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "755267a78a41bb50bbff34b06288d25b8823b76438ebc77f462bbaded287c00a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:11977",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:11977"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.collision_margin",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "84bfa8e68dd1fbbf7f77c61a6f9bce064330677ec6dab08880f47f592dd34a85",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.curveCenters",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveInequality",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ad0453e923275bacc98a998bd276f25ffb9fb85c95e6ffe59e5d71c543dc3752",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveInequality:321",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveInequality:321"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.curveCenters_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveInequality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ffdd2514c9c983322a636847f43ce150366cc7ffea87854e1f257fda4501f690",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveInequality:513",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveInequality:513"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.curveDegreeWeights",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveWeights",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "78289e8efcb24b43f844811b1a98c92cd4b6fb2a50878600b35036c292b8c431",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveWeights:330",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveWeights:330"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.curveDegreeWeights_cast",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveWeights",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ba0ee58abdaa390d24206f22e367bb9a65e2585147b94b06b40d03ca5e80ecca",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveWeights:1447",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveWeights:1447"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.curveDegreeWeights_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveWeights",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f1321bd5a489a20ed5ef41de90cc35ab8abab55d576c77aba3b2c45cccf8058c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveWeights:977",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveWeights:977"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.curveJetWeights",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveWeights",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "579f9ccedc1e33f8ac19d2e778d9c628e9cfd144f017c5b0afdfe03b44d6bd6d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveWeights:441",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveWeights:441"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.curveJetWeights_cast",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveWeights",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e8b9c94fbc7f3705ca1331a3ea31345e4e81d8259cbcc67285378dbc0bdb8a40",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveWeights:1766",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveWeights:1766"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.curveJetWeights_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveWeights",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ce49cf136d06455dbe2622a3a7ffb116eea069a776a259b46928159d6b66b033",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveWeights:1215",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveWeights:1215"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.curve_coordinate_ratio",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveWeights",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "23d412c8c48fc2ffdb76a6a9e4526fc71f17977edc86e8c62c01ce4bc25b83b0",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveWeights:4111",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveWeights:4111"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.curve_fibre_product_ratio",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveWeights",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2e8c214dab8ae9cc4b5e43aab6b4965f1e81c223d20041a4fb6838dd3ed7880f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveWeights:2083",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveWeights:2083"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.curve_fibre_volume",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveWeights",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a19cf2d9c08e07df77be27c962a0bbf32bc546aecd009375d3f52b5bf44cadc3",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveWeights:3522",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveWeights:3522"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.curve_product_ratio",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveWeights",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a74a6122b12378b09c06ca91b92acbd3e8d27557f43253054e5fcb89dba77815",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveWeights:2631",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveWeights:2631"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.curve_separated_weight_products",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveWeights",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8ca083ac76105c57719a40b3bb1546d700340148b5cb8ba1e7e5decedf79bb4d",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveWeights:4547",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveWeights:4547"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.curve_volume",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveWeights",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0a2b716256b05e59e5d3c0c01d5d2b2ad82c3e38b8db5923aacfd555bd604aa0",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveWeights:2952",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveWeights:2952"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.dimension_margin",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3d7c12295ae9dd15a57f1098be6fa89b7e2e995b6f2a9f9de6dfedcc5e05272e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.epsilon",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "997dda484fc9c6c4df59258ead4b0ff48858ffe1475a073e41c0cd72252b4f58",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.epsilon_le_half",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "756dbf6888b3abca3143363014fc938bd426f0f2868d9a863a1aed944a8c038d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.epsilon_lt_gap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7a52307cc27628e9b08d4d04119a3177104542c20f1044410cc57345606b7659",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.epsilon_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5f557f266f5920f3d5fc0707f350aeb0a5b3efe05f752ec73db0e8bb017a5ad0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.error_sum_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "19db955c6a774e9810d84e6ca08ebfa513f548575b0fcc1d3bff09422ff6e23f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:13177",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:13177"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.error_sum_lt_gap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "469547249231e68feefb43cd9279a75c2d901ba464d85bcdc26ee07b69d10560",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:13607",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:13607"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.exact_weighted_curve_inequality",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveInequality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d1ef86a1e0cac14665db3ad149b7cfd3e832e3a38f500b5200c62aecf77d9725",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveInequality:1264",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveInequality:1264"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.holomorphicError",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3c7589e8562d6a358c2a9d587332bee9e8ae29cd0c6d9350d0b8d55bba0971d6",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:12936",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:12936"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.initial_margin",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f4484806a112aacdf4dab4967f6b000a7d9903322fc1701926a072aec2a7d0ac",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.m",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d4e9015c664f68ec0c8f884e95478c645cc4ef2efa5bd838abfe68a26fd517b2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.m_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e49fec9450acb197928cf9bc6fca97d2cb0d30e439d5535a37dcbaf14688fe15",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.mk",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "ctor",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b6aa2511d0b6f5dbb66c13f080c9c0590a22109e32b6e0247172b69926d230d0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.mk.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f0a96c772cb0ab288855a6f878530c95d700c41b0512fb76e1fa67a2353ab193",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aa7fdd7013b61ead06aac1f276f8e2efdbdd2de06fe6888ea9736f5c2e4b165c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.p",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "24ae95a144f64ded836576d32841423aed8e60ca95849a20a64a4cf3510d88a5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.q",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8a274dd3132e9589f81d6918a3b40b4f60926b66d529ff5a107c6f86e86cc07e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.rationalWeight",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "de156a5d629cdbd7e50f5c436de7976a71426c3bdd035e645d3d20b0f2c399e6",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:9489",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:9489"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.rationalWeight_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4d0a71c146240aa0a6593fa4f4ea014db8eff3be5ae0bac80bfd0f9b878bc95d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:9818",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:9818"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.rec",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "rec",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "461cc675fd598d7e69d803076ca99f3af3bef39f77604eef020d5756f667f3cb",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.recOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a2cb066747349fec5c889a6cd3cca90bc9336979714dc20a5b940f39fc13cab9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.separated_weight_products",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "27a9bf3b8f04e4f850bf2ea2030583d04f8453327d50d2fe95cb7205bb23d39c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:10646",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:10646"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.sigma",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "62d01aef6f0c6b7ee934e98163dce70b2e73f7d31d485b9c49c9629d032228b2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.sigma_centers",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "49aab0fe8796f41c5417ffe2d03b4acfb3c47412d09c32ea7dd8446a040c1923",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.sigma_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fe2038c34541e78771cb77ebb9e21ea1241e5739b2fa077d48e26c0a59439612",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.sigma_theta",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0226d22e7ed13f7ef3eba3181f4e544bef4747356320d6208f56550107d4d475",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.sigma_volume",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "50b588c2a26c3cf930f6a70903644004bcf3249dc762be28e6b93facf61e72a2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.total_error_lt_gap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d1b7f9ac9de61f54e25ba199b1ad87e2b63e764a4db24e812a5b434cf098c54f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:11450",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:11450"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.translationError",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "70234677172bb5396274cd862433b32d475989035953d9b17e0af072b4ed5e79",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:12784",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:12784"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.v0",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "32e60970381f16d5084a46d2a82245aae8f8d640737814caf25112d4313e4eef",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.v0_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b12ef1a233b168f1cb12db4527acbdf2645a6262ff279decefee033976ee5eba",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.v0_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8bf95ea99a27be454eaa8d8814c0764bb6889a9de310911208f5afe60f297f00",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.volume_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b694ea149bbe3bbd21c7c0714a8a75bea8ab7fb0097b3903b89be3d065b42684",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.volume_lt_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fc991d23bfad19356d4212f994b5c778a3d378a0321ce6707b77e9bfbe4eb29a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.w0",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cbfb437ac6f8bf3a8b1bb4d016b3f1e7d32ee189902b03e47a98de53c350476a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.w0_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e5ed5c83295b807cc0fff10f1627802ebb10e8dafed9b9f98a17a4d8e667f1f9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.w0_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4327cae9ef0fec5683a994f6356f67d795d6d4037e20fc0600a3777b20dc027e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.weight_growth",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b70db00109afdf3108de8a0373186561041683d8a5f744aabb9227dd5fb30c10",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.weight_margin",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "82ff198ada4b33c69b15be674e29b6cc3b960abfb7cafcf500ca829c8f75cd48",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.wstar",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f46018696e8cc4bb9d9fa60c4bfe11903d42a69bc02a72a9f6cae52ec6585737",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.wstar_attained",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ae3b89dd0a91d663f9c7c60d7a9ad66729ca607ed5ec6ab7d7d8a5ce15495f9d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.wstar_lower",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b8962fd7410292f589961d06a99202a07da45f196583ee3ec28702888ddba6ff",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.wstar_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c303662deee1ea3a9d16246be9f19130a51f8b418777f342701cdd4714d76697",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.x",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3d2fb4c0ac87c30c17e50e74f7a3511ca4fc004fa976b575df9c80edccd60540",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.x_log",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b91a285cb298905184148e0e3eec7df492fb5ad914a0c0df2a8b915d6783e61b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.x_one_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "60716a30d4c06faa34f980b218a5b69cefe2538b9fd24218ab7f730572c2f912",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleParameters.x_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1a3642ca8c261b85a664a129811d130c65c7971b4d5820ce584f94db33942d69",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327"
    },
    {
      sourceName := "OAI.PiExponent.AffineJetCoefficientFrame.globalSectionCoefficient_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientFrame",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0468906423e0e2aab7ee8198140392d8b2c2a2001ea37f4b57a70ce32f3cb37b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientFrame:1588",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientFrame:1588"
    },
    {
      sourceName := "OAI.PiExponent.AffineJetCoefficientFrame.polynomialCoefficient_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientFrame",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "99807cfa196e7ce66eb9321438d508b72d238b6d1d629a176522dd0841e46a19",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientFrame:3488",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientFrame:3488"
    },
    {
      sourceName := "OAI.PiExponent.AffineJetCoefficientFrame.polynomialPowerFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientFrame",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "164ee762cce08665dcc0fd07f8037273a80fbf243da919d8054718ebe96b5388",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientFrame:2948",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientFrame:2948"
    },
    {
      sourceName := "OAI.PiExponent.AffineJetCoefficientFrame.restrictionSectionsIso_restrict_value",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientFrame",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "993457ba50f986a145ad71f7a161594f4ff8482f742accb965922fac3b458e3d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientFrame:769",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientFrame:769"
    },
    {
      sourceName := "OAI.PiExponent.AffineJetCoefficientFrame.restrictionSectionsIso_unit",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientFrame",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "680fadb5aa7c5a513f5311ac09601f40b48ee0925fc57a7a8e54a17387662100",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientFrame:1251",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientFrame:1251"
    },
    {
      sourceName := "OAI.PiExponent.AffineJetCoefficientFrame.untwistPowerFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientFrame",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "957dbb2de2b7a235adcf0078363f2bf9d0f2511e8a237641936040793ae652ea",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientFrame:364",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientFrame:364"
    },
    {
      sourceName := "OAI.PiExponent.AffineJetCoefficientInterface.Frame",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientInterface",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1545cbe457d5a24211f4f8e056ab22ca2921fc3e4b1957ab31ee93538bfaa5bc",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientInterface:412",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientInterface:412"
    },
    {
      sourceName := "OAI.PiExponent.AffineJetCoefficientInterface.Sections",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientInterface",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3a99f985bbd3977036964a6b46fd37bceca67634162763903dad1b38d4bec17c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientInterface:515",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientInterface:515"
    },
    {
      sourceName := "OAI.PiExponent.AffineJetCoefficientInterface.coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientInterface",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7ee603ddae85fef0750030d94b034f0c6755b1ac5c8211ff6b2cb4088cd31a46",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientInterface:592",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientInterface:592"
    },
    {
      sourceName := "OAI.PiExponent.AffineJetCoefficientInterface.coefficient_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientInterface",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eb3c34a1e38130d8334027bf588e953f0a702448ab0c82a2cd161ed334010183",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientInterface:714",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientInterface:714"
    },
    {
      sourceName := "OAI.PiExponent.AffineJetFramedPackets.surjective_of_jetRestriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AffineJetFramedPackets",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5af0954578b0c7f774119f567528e91adc4ea206bc3d0c805330e2efc65ddcdc",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AffineJetFramedPackets:460",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AffineJetFramedPackets:460"
    },
    {
      sourceName := "OAI.PiExponent.AffineJetPackets.formalJet_packet_eq_of_sub_mem_pow",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AffineJetPackets",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b8aebcaf011f806beb673b57575dad41078f0bdc29371036cc9eb7e0a25f6c29",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AffineJetPackets:333",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AffineJetPackets:333"
    },
    {
      sourceName := "OAI.PiExponent.AffineJetPackets.formalJet_packets_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AffineJetPackets",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b0a80a303bec2036ef5c9935dda143f6fdbd723e4a8992e1d5e99661f61a9044",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AffineJetPackets:1086",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AffineJetPackets:1086"
    },
    {
      sourceName := "OAI.PiExponent.AffineJetPackets.packets_surjective_of_polynomialIdeal_quotient",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AffineJetPackets",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b631b780029f1f679299b7e0ab3e01460b47545724dba9810dee0e15f9980043",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AffineJetPackets:2130",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AffineJetPackets:2130"
    },
    {
      sourceName := "OAI.PiExponent.AffineJetPolynomial.map_ideal_functionsOnOpenEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AffineJetPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c427785e90982e2912c422a3a95d107214844d2508c231e482f62fe23a7aaf8a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AffineJetPolynomial:572",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AffineJetPolynomial:572"
    },
    {
      sourceName := "OAI.PiExponent.AffineJetPolynomial.polynomialCoefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AffineJetPolynomial",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "71a7e7e4f3911fca6c57f710b511be522e17221cb18d16984e5f2d7c537f3570",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AffineJetPolynomial:1802",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AffineJetPolynomial:1802"
    },
    {
      sourceName := "OAI.PiExponent.AffineJetPolynomial.polynomialQuotient_surjective_of_jetRestriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AffineJetPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "30c5cf0a678c5e8c33f4eef78ea2bb1aa37a1690ad900c3163828a98a4942383",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AffineJetPolynomial:2146",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AffineJetPolynomial:2146"
    },
    {
      sourceName := "OAI.PiExponent.AffineJetQuotient.coefficient_quotient_surjective_of_jetRestriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AffineJetQuotient",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a19e56118a859184be4eb53a9fb7f93cfad4bcc8de268ff7e1a2d3e12a711016",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AffineJetQuotient:4558",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AffineJetQuotient:4558"
    },
    {
      sourceName := "OAI.PiExponent.AffineJetQuotient.globalQuotientValue_jetRestriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AffineJetQuotient",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ce216c8a2bb4196f7ff344868a6752b5b6dda29de3c86f7886537e8f905da403",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AffineJetQuotient:3158",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AffineJetQuotient:3158"
    },
    {
      sourceName := "OAI.PiExponent.AffineJetQuotient.globalSectionCoefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AffineJetQuotient",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3c7ff540de5d5bd3a1030e54edd234aca29cf720f2690e68c2923290b75a2e04",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AffineJetQuotient:2818",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AffineJetQuotient:2818"
    },
    {
      sourceName := "OAI.PiExponent.AffineJetQuotient.localQuotientEquiv_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AffineJetQuotient",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "19b2c95fcc7625c645fcd4b008369947d5e57bffbc0c2667b519214355ba8614",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AffineJetQuotient:2444",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AffineJetQuotient:2444"
    },
    {
      sourceName := "OAI.PiExponent.AffineJetQuotient.restrictionSectionsIso_natural",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AffineJetQuotient",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2fe5e7875d6e0d6211cfcd2ac72d30aa0ff6b870165e89fe9f3c0a61578ca555",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AffineJetQuotient:357",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AffineJetQuotient:357"
    },
    {
      sourceName := "OAI.PiExponent.AffineJetQuotient.restrictionSectionsIso_natural_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AffineJetQuotient",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c80af575352a176e9c5e4c1c692ac020036dab60a5909269c61f034dd8dca1f6",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AffineJetQuotient:357",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AffineJetQuotient:357"
    },
    {
      sourceName := "OAI.PiExponent.AffineJetQuotient.untwistSectionsIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AffineJetQuotient",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "342f1108c59bd13f8caa069bc722c2475bcd74ac436ba04565e655251b0576b6",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AffineJetQuotient:854",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AffineJetQuotient:854"
    },
    {
      sourceName := "OAI.PiExponent.AffineJetQuotient.untwistSectionsIso_natural",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AffineJetQuotient",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f517da121fa3e564b08b673bfdb56c559ce8d9ad3bb131c49e77f4945ecb3c84",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AffineJetQuotient:1239",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AffineJetQuotient:1239"
    },
    {
      sourceName := "OAI.PiExponent.AffineJetQuotient.untwistSectionsIso_natural_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AffineJetQuotient",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "58a40c48af71c3029e9f25f533e53625e240ec9ece4ac82e32963b4106de00be",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AffineJetQuotient:1239",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AffineJetQuotient:1239"
    },
    {
      sourceName := "OAI.PiExponent.AffineJetSupport.globalQuotientValue",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AffineJetSupport",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1a0317a60d5e9ce1f70483a32965d1b1be682669a790c531fdb395b5b62851e7",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AffineJetSupport:3743",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AffineJetSupport:3743"
    },
    {
      sourceName := "OAI.PiExponent.AffineJetSupport.globalQuotientValue_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AffineJetSupport",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5c9a950b4ba06e3bdf7f03f81adb6ca6a7582a8166e517f18bb5662017eaddc0",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AffineJetSupport:4237",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AffineJetSupport:4237"
    },
    {
      sourceName := "OAI.PiExponent.AffineJetSupport.localQuotientEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AffineJetSupport",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6a761371743182de8d771030a954bcfd989f7ea08345c613279eb6207b8907b1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AffineJetSupport:3067",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AffineJetSupport:3067"
    },
    {
      sourceName := "OAI.PiExponent.AffineJetSupport.pushforward_restriction_bijective",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AffineJetSupport",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7dd83c4c094f603d4561bb3d4a4b66213a678f4dd4ab7b517e01c0423455463b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AffineJetSupport:1505",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AffineJetSupport:1505"
    },
    {
      sourceName := "OAI.PiExponent.AffineJetSupport.restrictionSectionsIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AffineJetSupport",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a4fdbcf2ce98046662792dd2a3414ea08ab26a1fe12887666b82ed61616ec448",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AffineJetSupport:2728",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AffineJetSupport:2728"
    },
    {
      sourceName := "OAI.PiExponent.AffineJetSupport.restriction_surjective_of_iso",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AffineJetSupport",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d8aee2314fcf61817407a64dc33ff0d38c377e9ffa87a068db376e316fb7aacb",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AffineJetSupport:806",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AffineJetSupport:806"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_001.jsonl"
