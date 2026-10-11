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
      sourceName := "OAI.PiExponentSeshadri.BlowupLift.mul_coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a4ff18e1415b62d262c9d53f0d91a51349d307461a3880f7d1f2c0067eeb5d56",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:509",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:509"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.CartierSequence.chart_topIso_naturality",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CartierSequence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "74d24de51a39577be75c45f4a4f2dfeaa4fac7061eeafba9884f1f5a6ba36d40",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CartierSequence:401",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CartierSequence:401"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.CartierSequence.exact",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CartierSequence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1d93f972f909305b0da3797efbfe9eae1cf593dfefb57953190c9aa2cf87ea43",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CartierSequence:2278",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CartierSequence:2278"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.CartierSequence.restriction_principal",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CartierSequence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "21a15d8b34f07d220233c663d2e5898157b5fdb3bb77dca444eda634de604688",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CartierSequence:973",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CartierSequence:973"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.LocallyAnnihilated",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalClosedAnnihilatedDescent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8be4d4824bd84c166f229621343490eda7c8809273f77708da3971f425ba5243",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalClosedAnnihilatedDescent:514",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalClosedAnnihilatedDescent:514"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.affineDescent",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedAnnihilatedDescent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "323d92b480ec6a1c40961fee57b032be773e2697494eb86dc830aeafa8e8efc5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedAnnihilatedDescent:1742",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedAnnihilatedDescent:1742"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.affineDescentAlong",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d5ec85d50e6e3242d4e30feb4140ce9e0d89a7b00efa32757d35e32b4c6c54e1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent:3632",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent:3632"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.affineDescentAlongPushforwardIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eb6da879c250cc3661e604c055dbc93d5623db7da9b82f1d3d49e895690e1b77",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent:4052",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent:4052"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.affineDescent_isQuasicoherent",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedAnnihilatedDescent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "552dd7f50a9f9c8b426f1b661a66aa73d28287c80c828d3cd80487dd7248823c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedAnnihilatedDescent:1976",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedAnnihilatedDescent:1976"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.affineSpecTopSections",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "83497b55a9a59bfc6f10b8f9e8c01142ba46dbc4450750bdec342012091002d4",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent:2062",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent:2062"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.affineSpecTopSections_annihilator",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "22edb8897b9adcda0487d24986dc8f305c41de5a68def459cd184ab4a7d294a3",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent:3168",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent:3168"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.closedDescentPushforwardIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalClosedAnnihilatedDescent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8627fa2ea0c45f955bc53c7e3d69cba4412bc47ef27b44ec0d3261b55be97697",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalClosedAnnihilatedDescent:1216",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalClosedAnnihilatedDescent:1216"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.exists_affine_closed_descent",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1a9bacd09b3e9a0cd7899e73ad4d4c273ac2fd94cec39990e3e9dd4e4d93ec7e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent:5211",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent:5211"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.exists_closed_coherent_descent",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalClosedAnnihilatedDescent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7adcd418c8b9ec652934cb6205f04225c23a5f0fe3dee8cf4489f504d356d1bd",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalClosedAnnihilatedDescent:1858",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalClosedAnnihilatedDescent:1858"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.quotientModule",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedAnnihilatedDescent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6e096d7ae7aa2c19124a4d61b7e49433c12c06c487dd8ad37f6b087cd2a3d6f7",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedAnnihilatedDescent:1238",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedAnnihilatedDescent:1238"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.quotientModuleRestrictIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedAnnihilatedDescent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1912a5a12e49456de418270afa8c06c11ca54f968a0f0e50be02273cf376e8e5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedAnnihilatedDescent:1530",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedAnnihilatedDescent:1530"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.quotientModule_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedAnnihilatedDescent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dbac21cfe2002c846841ebecab6397a77654375312387bc3effddbbcf0340bd2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedAnnihilatedDescent:2739",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedAnnihilatedDescent:2739"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.specPushforwardSectionsIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedAnnihilatedDescent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9b2465ee11973646a6e5699aa7dea1b68eb93de9a2854d4fc5a40af93b270eed",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedAnnihilatedDescent:272",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedAnnihilatedDescent:272"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.specPushforwardTildeIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedAnnihilatedDescent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a924cfec3e99fa0ac28b2d20e3b46b61a30b1909d75c752141b6c7eccc67f4df",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedAnnihilatedDescent:707",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedAnnihilatedDescent:707"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.specSurjectiveDescent",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "11410c6e28d3268be8fbd7b837a8e7206e79806c5f7b4e61067afa7a8c2de98c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent:1195",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent:1195"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.specSurjectiveDescentPushforwardIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e4b0ae1ef724f053b225031bc2900bfee89942164d78f9428a33e92b4805504c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent:1470",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent:1470"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.surjectiveModule",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "065ccb43e76b9fc8003e33acfe1b057fa7cad062d64486278ac58dd25fda24c4",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent:345",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent:345"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.surjectiveModuleRestrictIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4779f3562c35bca870af4e058f4ed0b1bc1d95681163dfca1bfcba9ae3681ed0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent:646",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent:646"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.unit_isIso_of_locallyAnnihilated",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalClosedAnnihilatedDescent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "56ed1885dd497631e307aeb36c3fcb774db7f82771adcdec969f6eac359fdbde",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalClosedAnnihilatedDescent:710",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalClosedAnnihilatedDescent:710"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedImmersionModules.additiveFullyFaithful",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionModules",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "95be69aca6b2c22a10e14506b3e4f8141641316399b901437d419f0c57f02173",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionModules:274",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionModules:274"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedImmersionModules.additivePreimage",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionModules",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "556c8256bc9e2f6b21557074ef82a92d5fde6579d8fce2f8cfd923684674dae3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionModules:1476",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionModules:1476"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedImmersionModules.additivePreimage_app",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionModules",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b02b3b955f2e544ee728e2e0aea305c364af819ab44654b2d2d6ec4f772c82ba",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionModules:1717",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionModules:1717"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedImmersionModules.additivePreimage_smul",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionModules",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1ac9c9529c9943b1a38f938a1a70e8c4062357d6ff884ef5de475bb2f6364edb",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionModules:2185",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionModules:2185"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedImmersionModules.counit_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionModules",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "349ef58e7648b93eadf9ec45220d2319acbe089aaca9e6a8b726e5f2adf90513",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionModules:4853",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionModules:4853"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedImmersionModules.modulePreimage",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionModules",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f7abd9ff0906c03862f60584bde9e6dbdbc43150fef564192681e34d06c9741f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionModules:3909",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionModules:3909"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedImmersionModules.preimage_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionModules",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "92556acfac85d9ec918df664a28a69a2485551b9c6bea3a14cd7099a170409b4",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionModules:1242",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionModules:1242"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedImmersionModules.pushforwardFullyFaithful",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionModules",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dcb3e60b931788e876dc194d553b975af44d48b3d44b637ffb3e5651b1151d59",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionModules:4403",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionModules:4403"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedImmersionModules.unit_isIso_of_pushforward",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionModules",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1c8295403e58727ac1943e8ccfc0ac3742a2f4e846923be5f1bcaa8066445307",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionModules:5158",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionModules:5158"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedPullbackUnitRestriction.restrict_unit_isIso_iff",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedPullbackUnitRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f461121b34f5a2fd871a89d236f99788ac86e65b7bb1f82d973671bea9b17ed0",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedPullbackUnitRestriction:400",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedPullbackUnitRestriction:400"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedPullbackUnitRestriction.unit_isIso_of_affine",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedPullbackUnitRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "527aa8a2662012360df2264d55c0f1e4b2ddaaec348d2e2f9a9f7feedfb4dd17",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedPullbackUnitRestriction:1292",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedPullbackUnitRestriction:1292"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedPushforward.map_epi",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardCoherent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "599e2179a50b31a03a00937eb0c3c00552ad798f2b795c3fde26bff94cc0f0b6",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardCoherent:687",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardCoherent:687"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardCoherent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "75df9021a931d1a303b7fdb934c45f345a79efdb13b0e1102330de48f4798d33",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardCoherent:2963",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardCoherent:2963"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardCoherent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eff9d75ec9ad539a538665aca743f58c8d7eb3bb1810535be3cbbc29deaed835",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardCoherent:3316",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardCoherent:3316"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardCoherent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "307867cdf8e48d9812286e1d7b14687b554e04a4ace51008bba587f098d6fa36",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardCoherent:3131",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardCoherent:3131"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardCoherent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2b7a9129f759667316352bf66f673b316910a70f8c20ab6b0eefb2dc68f65382",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardCoherent:3990",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardCoherent:3990"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedPushforward.sections_empty",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardCoherent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f202e8ee1ae77a14187dcb081d64388bc4f2ef2db1a456cb1e022ea7e01e57b9",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardCoherent:425",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardCoherent:425"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Cohomology.alternatingTrunc",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fdab1956c7da9000b4e613d952c7dc6f8117b6e0883cb38c3f2a137270b962a4",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact:253",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact:253"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Cohomology.alternatingTrunc_succ",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fa437116798162c5d8ff796c38e8de79ba57e83e486047d170cbefd7400419cc",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact:366",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact:366"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Cohomology.cohomologyBoundary",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "24dd3ec2354e1e9bbaed9b6dcd1a5ac073dc14c92060fe1f4144a8309d8e5a84",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact:2215",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact:2215"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Cohomology.cohomologyMap\u2081",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f686a213b109a55c34edb197ec2731aa91ef300aedcb1791a9ad7886356227b3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact:1951",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact:1951"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Cohomology.cohomologyMap\u2082",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1446e2b45ff0b277f2742b22e9f966d86c5462b1f23902f6d4f3fffe35dbff3b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact:2083",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact:2083"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Cohomology.cohomology_exact\u2081",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "777c7b8d073a1883927b8397f481fb757335814da5d8c99be6b7e40fcc56954b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact:3146",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact:3146"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Cohomology.cohomology_exact\u2082",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "da7b917beaf25d72b38194ce8374498975c74fc62b5bdc99be8aec08a6021f49",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact:2340",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact:2340"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Cohomology.cohomology_exact\u2083",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "92db2868f40f2de1835ee3ffdf19ff0fc848e05bd9dc350d2911230cd182b44b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact:2735",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact:2735"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Cohomology.extEuler",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d1105784621e6592e75fd4372da250ea3940c2031bacef36325e1d71b0214c49",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact:1783",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact:1783"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Cohomology.extEuler_add",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8aa0c8e72a2439eeb0053be6b4e3584a0b28bc66477887029f0e3694b35505a9",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact:6179",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact:6179"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Cohomology.extEuler_add_of_boundary_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bec0e425366c2e15bd2d3b0c9c62535dcf044c52a2276b749421c4023b9bb01a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact:3577",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact:3577"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Cohomology.finrank_middle_of_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "210f3024e93a548efc10b01094b0a116c8ef967c7957cd1eda1b84c72d3f7d57",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact:1214",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact:1214"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ComponentAmpleDescent.closedModule_restrict_annihilated",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ComponentAmpleDescentLocal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "153256ec4e13378e20f00cc930de97b9f03d9593e354ab262f8fb748601be9a7",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ComponentAmpleDescentLocal:391",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ComponentAmpleDescentLocal:391"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ComponentAmpleDescent.eventual_pullback_twist_sections",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ComponentAmpleDescentCover",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9ca5af5b28f98df38ef9ffdabe02cc5d2bc37d57c83258a35982ef6ed2160621",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ComponentAmpleDescentCover:804",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ComponentAmpleDescentCover:804"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ComponentAmpleDescent.eventual_restriction_surjective_of_complement_ample",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ComponentAmpleDescent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "41b823db6dd7bb87ac6a66e2f5ac95f8cde54a419ba7c9028224953c7ac39f5c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ComponentAmpleDescent:1241",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ComponentAmpleDescent:1241"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ComponentAmpleDescent.eventual_tensor_cohomology_zero_of_closed_pushforward",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ComponentAmpleDescentSupported",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8863d21fb2fc90539c400ebe5365d5f2544f1274304d0a35b79185eed4663eda",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ComponentAmpleDescentSupported:413",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ComponentAmpleDescentSupported:413"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ComponentAmpleDescent.exists_complementary_ideal_descent",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ComponentAmpleDescent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "efb54d4cf783ffb503800605a4d818027e0d13a686ea56d46a9cb508cecc6568",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ComponentAmpleDescent:723",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ComponentAmpleDescent:723"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ComponentAmpleDescent.ideal_le_annihilator_closedModule",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ComponentAmpleDescentIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "26749460c4473edf84d17c9f5b81aaa22c98a1ba95b8418c30b244f111a16f72",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ComponentAmpleDescentIdeal:281",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ComponentAmpleDescentIdeal:281"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ComponentAmpleDescent.ideal_le_annihilator_closedModule_of_reduced_cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ComponentAmpleDescentIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "09ff72e169c8624e1a80d8d7cd4968e1709451f59f573981a65c23c71e6ccd6e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ComponentAmpleDescentIdeal:1629",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ComponentAmpleDescentIdeal:1629"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ComponentAmpleDescent.ideal_mul_eq_bot_of_reduced_cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ComponentAmpleDescentIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1cd0bd25820ab8a1574742b0f53095a4d9f4aa7aa8d94a494b45c4b2cc6352b5",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ComponentAmpleDescentIdeal:1373",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ComponentAmpleDescentIdeal:1373"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ComponentAmpleDescent.isAmple_of_eventual_restriction_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ComponentAmpleDescentCover",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c86fc745cdca12778e67b01a3baf2e6ea660207654ae12af5c12a2b2191302b0",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ComponentAmpleDescentCover:3047",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ComponentAmpleDescentCover:3047"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ComponentAmpleDescent.isAmple_of_reduced_closed_cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ComponentAmpleDescent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "72824b9e2af6162bb8d1563d887c593356f15a5448aae84297f483bb2e356600",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ComponentAmpleDescent:2059",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ComponentAmpleDescent:2059"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ComponentAmpleDescent.pullbackTwistIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ComponentAmpleDescentCover",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "281a12170e2b89b5b6bfb00cfc06de10116b817b19f85b15394c7e2ef8964591",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ComponentAmpleDescentCover:427",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ComponentAmpleDescentCover:427"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ComponentAmpleDescent.section_cover_of_jointly_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ComponentAmpleDescentCover",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cbc2426f9e7eb30986fb1d6164b413b2044d21de37c264362b93457f72bf02c8",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ComponentAmpleDescentCover:1879",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ComponentAmpleDescentCover:1879"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ExtCokernel.quotientEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ad74fc2ab4f3928a5c39d55ac9605affb91ff44cb08fb456fcfb64b3277c74d5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech:421",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech:421"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ExtSectionComparison.mapFrom",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e4f1454513f1ae3b8b35f7b6212ab11de5dfc7b7d92630ccc97ca4449d7e9296",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:43733",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:43733"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ExtSectionComparison.mapFrom_bijective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4a67ca002bcbb9ddc33874ae8d329cc49410c05e407e47fc13247c16ce13e0d3",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:44563",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:44563"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ExtSectionComparison.mapFrom_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b61de54bec1f41a5447e7700692d950b179e89c457208af65963bd8af8d7d75a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:44242",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:44242"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ExtSectionComparison.mapFrom_mk\u2080",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2dcdecea59511ac9d7ed60a24d3239e2e4e0dd3aef78a71fdf80989a891272b1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:44040",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:44040"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.FiniteCoverCohomology.affine_open_ext_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "24986dadf45de9e3b65710111d82f7c761619366701d7a17e7ce97d1ed4d8054",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:54042",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:54042"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.FiniteCoverCohomology.affine_union_ext_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8222be111d95a915529c2dbc3f4419b017196532189d21f070d371e8fd8f786b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:54697",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:54697"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.FiniteCoverCohomology.cover_ext_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a46ca01cd76d2128100145ae03ccfb9dad3ceac96b8cb106a225e5e1490cff87",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:57576",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:57576"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8f66fd4c8e1995edb3f94b7a7d0a3ce5253985f96edcf1f2d39192267eca7705",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:53948",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:53948"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c3191d550ac7bb27f6abae9a7f0501f1ac6136a4a2188c0540aaa5902a64d8db",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:57481",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:57481"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.FiniteSupport.discrete_restriction_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteSupportCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1c59f0cdb66554339c3c180f43cd6c87f0f4b09c17152ef22da6aae3b4a273fd",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteSupportCohomology:299",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteSupportCohomology:299"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.FiniteSupport.finite_closed_support_flasque",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SupportedSheaf",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d8c755c06e0988433a352d6b1e5fc2817b70b50a6b7651415f38f38a1436ff3b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SupportedSheaf:2293",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SupportedSheaf:2293"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.FiniteSupport.finite_closed_support_restriction_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SupportedSheaf",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fb12740e4670db9b35193730c987dd3384baa9aa3917ccea6fdaf96861b4314c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SupportedSheaf:619",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SupportedSheaf:619"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.FiniteSupport.finite_line_euler_eq_sum_stalk_lengths",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteLineEuler",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2da5125176a84b8329aae208de25da184a4dcde29e2edefd12825eef1124b517",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteLineEuler:7121",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteLineEuler:7121"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.FiniteSupport.finite_line_pushforward_euler",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteLineEuler",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b0bef09942c46a8d720835a7dd0e7d8669c29a03947306a4813ec3d3182f0e78",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteLineEuler:5023",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteLineEuler:5023"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.FiniteSupport.finite_line_pushforward_finiteDimensional",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteLineEuler",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "46eaf8a5f1fa9baaf0ec9074f15bfa78053d96a55e8f8c3b676aced3ea015293",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteLineEuler:5613",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteLineEuler:5613"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.FiniteSupport.finite_pushforward_euler",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteSupportCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "485c7f310d95ae0be063af5c75bff830c8aaf72cce24693720d4fa06760aa926",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteSupportCohomology:4358",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteSupportCohomology:4358"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.FiniteSupport.finite_pushforward_ext_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteSupportCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f0832d6aa366217ab26d1aeb75c3a08bd47a4be1840a108bbfe7babd941f7417",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteSupportCohomology:3100",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteSupportCohomology:3100"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.FiniteSupport.finite_pushforward_finiteDimensional",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteSupportCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "352877202b39e90197322bed2f1cc305ba0d95246c6f64fd7ab10a1dfa764a09",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteSupportCohomology:5669",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteSupportCohomology:5669"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.FiniteSupport.lineBundle_trivial",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteLineEuler",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bc019b4415e45b162ea73f51ba9b41dd2f040ef80151a891cd273b33b6c02ace",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteLineEuler:1735",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteLineEuler:1735"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.FiniteSupport.pointFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteLineEuler",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6ce664eb964383fe9ea01b8022f8c08fe9e1ad27d50f5a7b9f083821912e834e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteLineEuler:1255",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteLineEuler:1255"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.FiniteSupport.pointOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteLineEuler",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "27a85b27900c31b2fbb5fab6b40c10f51c346fe84b456bfbaaebfd939886bcb7",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteLineEuler:976",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteLineEuler:976"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.FiniteSupport.pointOpen_basis",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteLineEuler",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4cecdc2e16cf74d08565feb58df49cc9a004b868a48e7b0c4623f0af907c313f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteLineEuler:1043",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteLineEuler:1043"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.FiniteSupport.proper_finite_discrete",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteSupportCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b4dc29c66c62dfb9641fbcb248ceb11bad15691cf92dbec9e1b8416a8d27973b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteSupportCohomology:2144",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteSupportCohomology:2144"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.FiniteSupport.pushforwardUnitSections",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteSupportCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d66e60c37bcfacd24fb2c93b14c43dd6a31f548137310b708661e7ecb10a56c5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteSupportCohomology:3491",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteSupportCohomology:3491"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.FiniteSupport.pushforward_flasque",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteSupportCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "76c5178087191c34b83c6f2649630dfc10e6049e5e278ac3ca309cce4b50e179",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteSupportCohomology:2688",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteSupportCohomology:2688"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.FiniteSupport.sections_subsingleton_of_stalks",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SupportedSheaf",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e9ea42ccc2b6fa944e25690b566fb3c1366490bd803f00505e8b5d476a642cb7",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SupportedSheaf:294",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SupportedSheaf:294"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.FlasqueCohomology.flasque_ext_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "468250b2cfbe489531dd8ca1b3589e68e5fa187ed28e564ee0bf3636a969a9ed",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:34386",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:34386"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.FlasqueCohomology.globalHomEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "72773fec8443bdeca8a747a39074f8ea734385a47c36cd6e5e35d484de59bda9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:32949",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:32949"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.FlasqueCohomology.globalHomEquiv_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cfef02ef05d250bcf85f96c1cb76f273898f08a386dcb819da1e079bef0a3515",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:33108",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:33108"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.FlasqueCohomology.globalHom_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d64f0ee905ad9f8670d2b5f5b2758c11a56daa6bbee1e305639c7563d89d7156",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:33306",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:33306"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aaf1a13b92bd40351960007c282191a27d498be5fbd254317f2051a2c948176c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:34294",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:34294"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.FlasqueCohomology.sectionsTopEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ba2628aee36f89fceeba04eac1059cc4b06836c03e0f46539f4ab2b9300ea04e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:32394",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:32394"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.O",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "20bfbc687d2742e4a7d1836d7e393fa0c7a4635c2233c42523546aaf248a83a6",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients:273",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients:273"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "89b124d4e5850244026402eda16a71c6b0665a7f726266da54f11f73a30547cb",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients:1187",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients:1187"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.coefficient_change",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9191665f7c6f3698d5b62813c0adef1dfd2776b2e60354b4f9bdf67a59e9336d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients:1296",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients:1296"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.coefficient_frame",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cf30a833171ca404a3a4c742114fa7633c9bb2fbeff7cc0db43125b07130f567",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients:1585",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients:1585"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.coefficient_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.IntegralLineSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b3e6b265bb9fee193e6370bcba147ae4606d1e2b98f986596de33c8f4aee72d3",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.IntegralLineSections:7654",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.IntegralLineSections:7654"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.coefficient_isUnit_iff",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "280544d4e7a5f0dfb0bd0c926743626318a4f53c41c32628130a25f217f4a480",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameSections:1866",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameSections:1866"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.coefficient_precompose",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerOpens",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4293ca1debc68d9092920d440d571426e1dbb48924c4ca3d04c527c45a01d227",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerOpens:269",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerOpens:269"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.coefficient_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3abb70c7f7aace03c5bcdcffd2e50d4b765714d69fcefe15bc3be18baad44e23",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients:3543",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients:3543"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.coefficient_restrict_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0508e219f720172c2ac886708b4bb13baf4fb658c3d04667ec2d4d3781da70ba",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients:6492",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients:6492"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.coefficient_restrict_isUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6801f0cd078f6ff3cd1a94eea1521bff128ccdba9f6b1f90df44a277983ff9f2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens:5685",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens:5685"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.coefficient_scalarEnd",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PowerSectionExtension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9e29c163224bda4ed39c15916415074ff5eb1e58098ccd85df6dae6bd8004bfa",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PowerSectionExtension:336",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PowerSectionExtension:336"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.coefficient_transport",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ccc716944b412342d8c6d6e73cef99cf0b776f2b5137ce7ac200a8d5b87e0ae5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients:6269",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients:6269"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.coefficient_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.IntegralLineSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1545c0d6930268fec8a131ccdde2892953fad904375aa52467f40586dd3eb83b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.IntegralLineSections:7839",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.IntegralLineSections:7839"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.endValue",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6bb532bf6f585d5bd7abcb8057d27690ab356285adca997fba104b9c4c6fe35d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients:349",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients:349"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.endValue_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "08853c47c02ebd8c2d30ce4e4e18f709ca10d9c6f2dfbe31f39b4f526ae69318",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients:808",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients:808"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.endValue_id",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c23d93d23a0c7dccf380f9b9075a3c4cb0b574f1977f3f3c85f27add48c4707b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients:744",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients:744"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.endValue_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f8bd6c8ef2c65391c6cbd4f1e85b8f5128938721bd7ac6f42806dc0f8e273024",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameSections:1056",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameSections:1056"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.endValue_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "80613a74df829f5c25d03acef1bb4bc49ba013e7da0fb763f6a8c2ea61b72932",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients:2628",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients:2628"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.endValue_scalarEnd",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "577badb168c79eb1e1cdb447274903c808a52fda9edb1654b2956ba1133ba060",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameSections:916",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameSections:916"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.end_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6e17de4bf33d799cc28d82465a2b2334a5aeffad83f78a3f05dd048c08b15743",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients:426",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients:426"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.end_isIso_iff",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "565126e0100eae768a88690d493ecb9bcb842d75a5a4c4937294d30c1a8f3ae4",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameSections:1304",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameSections:1304"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.end_naturality",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "729d8fdbc9500de9ad87ab38ccd8a3ffc650957adcce727b7f32d0d97b573dbb",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients:2120",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients:2120"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.frameChange",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4a721c904820eb549e8152ea829b85424b9dbe0dd67b9b2a11b43c14db0c9c08",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients:947",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients:947"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.frameChange_restrictOpenFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameSubopens",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "874036354892f29ee26fcfc11510290d50b60f568a716128080a09c23f19ab71",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameSubopens:1319",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameSubopens:1319"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.image_section_extension",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fbcd6f33ef14607491d091af9b44451a1c6434bd049100600c55eae2f721312e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameSections:6214",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameSections:6214"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.isUnit_iff_basicOpen_top",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3c83515ce02e4c90c0ac6dabfc7b8099a3ae58160a73fd8ef0bc1f92c3aa6d30",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens:5412",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens:5412"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.isoOpen_eq_basicOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "588578fcd53a941fa4a40150aae74db4feb42b0574cc012447c101a697fce7c5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens:6164",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens:6164"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.isoOpen_restrictSection",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "977b799bc128ac7a1472527afc5422fdf85c8ade6e2ab3ee2deea2bcbbcee82a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens:7095",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens:7095"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.moduleSectionEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ad1d5bc8ffff50542683c07c724d75009899c1d8f9af11c571ad761b1d4bcbf2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameSections:2871",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameSections:2871"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.moduleSectionEquiv_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "82a892192999edd36bd40dede6ba89d9b15fd972e3ef21f1d9a3ad1728e65362",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameSections:3011",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameSections:3011"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_035.jsonl"
