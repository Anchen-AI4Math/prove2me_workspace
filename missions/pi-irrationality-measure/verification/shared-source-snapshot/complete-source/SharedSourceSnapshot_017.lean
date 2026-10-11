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
      sourceName := "OAI.PiExponent.LiteralAnalytic.beta",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "608a25b1ec2f80f2ed343b0eb1db098bef35ff22803ddac1f2e05e9d7b294e0c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:603",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:603"
    },
    {
      sourceName := "OAI.PiExponent.LiteralAnalytic.card_choiceFamily_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.AnalyticAggregate",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ec05d01d57558566c5e2ca68ab4b00d7cac7403c14e1b17ff64cf1b8b2f93336",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.AnalyticAggregate:1597",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.AnalyticAggregate:1597"
    },
    {
      sourceName := "OAI.PiExponent.LiteralAnalytic.choiceMatrix",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c4a7b640b29655532e726da4123b2de64473dc4b6632e1f9ce521b88b818f7f9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:1862",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:1862"
    },
    {
      sourceName := "OAI.PiExponent.LiteralAnalytic.choiceScalar",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "507a33206cb63d56844c4a38759a210534ae125391cc9bbf7c419fdac9d9316f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:1398",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:1398"
    },
    {
      sourceName := "OAI.PiExponent.LiteralAnalytic.fixedWeights",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4b29a7f620bcd45892c06cb30f7df96611add4d42f724b410a65cb7b0848218d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:337",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:337"
    },
    {
      sourceName := "OAI.PiExponent.LiteralAnalytic.fixedWeights_lower",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b8041cb01d7965f5903daf38588eeb1de05f4f2d6216fecdce2498f066c725cb",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:2482",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:2482"
    },
    {
      sourceName := "OAI.PiExponent.LiteralAnalytic.fixedWeights_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9df22f837d83de4842053d227a8447a2737b20953b9d512b94e8944e059e60af",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:2236",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:2236"
    },
    {
      sourceName := "OAI.PiExponent.LiteralAnalytic.indexWeight",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bb47aeb8669913e86bc7c043796eda1d557392970f58669d029e4ddae37f2a8e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:1060",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:1060"
    },
    {
      sourceName := "OAI.PiExponent.LiteralAnalytic.indexWeight_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "15b1c35f0d4b6c9653bed4c09afbd86c309753356ec9c6ff42421ff5760fcf63",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:3494",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:3494"
    },
    {
      sourceName := "OAI.PiExponent.LiteralAnalytic.indexWeight_nonneg",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "44b45eeb84a63f3d9828018038b55fb4b37b9ff1c674e0a8208b31d010ebf108",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:3220",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:3220"
    },
    {
      sourceName := "OAI.PiExponent.LiteralAnalytic.lowIndexCount_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "94186b7f131f3c92fdf2620b7112e17861d8d4ceb7b62e076b639374c4e9cfb1",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:8089",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:8089"
    },
    {
      sourceName := "OAI.PiExponent.LiteralAnalytic.low_transverse_capacity",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cb5a6a3981ef13ef5c637806e6a2b9fca0a07f6405890f656a43b2270a594dcf",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:7049",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:7049"
    },
    {
      sourceName := "OAI.PiExponent.LiteralAnalytic.norm_actual_summand_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4fd4d50595e18231095b899f4c47d5f8a5699f90654ab2b60ea56faeef4c11d4",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:10546",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:10546"
    },
    {
      sourceName := "OAI.PiExponent.LiteralAnalytic.norm_choiceMatrix_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "80db965ad98a95a80493ca95d6dbe7b2f6b5385ab942bb32f5c4b7dd66fb27a4",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:9158",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:9158"
    },
    {
      sourceName := "OAI.PiExponent.LiteralAnalytic.norm_choiceScalar_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f6dac574a271dc93ba4165fb4d6794b937cfcabc645a8d8c26ecdaaff1c60cd2",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:3709",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:3709"
    },
    {
      sourceName := "OAI.PiExponent.LiteralAnalytic.norm_scalar_product_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "936b8c6f41dd01e19e5a173bd8a2c1ae9fd26b7b0f9d1a9b8b8b0ddc0dbb134f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:8430",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:8430"
    },
    {
      sourceName := "OAI.PiExponent.LiteralAnalytic.rowOrder_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "be0d4c2bfe8020b86583e291cae1012db903b19b9683f26b9e83f12fefb1d924",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:2720",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:2720"
    },
    {
      sourceName := "OAI.PiExponent.LiteralAnalytic.rowWeight",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0f58ced87748ddf24c170db5e3c3720941ffe7a3c96ad374d10f677490aeae56",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:1231",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:1231"
    },
    {
      sourceName := "OAI.PiExponent.LiteralAnalytic.rowWeight_le_indexWeight_of_ne_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "49f8d6ffdc2494dfbd87dd322e6840c9b379bba1672f0c8210ba7ad103ecb94d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:5591",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:5591"
    },
    {
      sourceName := "OAI.PiExponent.LiteralAnalytic.sum_rowWeight_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d5c72f867e576bf95c1d2ee008e58b2d056951bc47d51b9c578322da0394f99f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:6298",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:6298"
    },
    {
      sourceName := "OAI.PiExponent.LiteralAnalytic.tendsto_analyticRemainder",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.AnalyticAggregate",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1da3dd28d1e64ff85d1e6c31c95c57a764635899f5a1a15d9f916f8f3ec3d6af",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.AnalyticAggregate:3610",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.AnalyticAggregate:3610"
    },
    {
      sourceName := "OAI.PiExponent.LocalLengthTransport.localLength",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalLengthTransport",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "673119144f873a983d0b782ee80fe57b3606ab8361a4df2d4e2a39fba2945979",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalLengthTransport:216",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalLengthTransport:216"
    },
    {
      sourceName := "OAI.PiExponent.LocalLengthTransport.localLength_eq_of_localizedIdeal_map",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalLengthTransport",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "071eccccb499e6461188c971082736d0f1d5847e838d9f51a55fa27fb1a79cf4",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalLengthTransport:1618",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalLengthTransport:1618"
    },
    {
      sourceName := "OAI.PiExponent.LocalPullbackSectionOrder.exists_frame_coefficient_germ",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPullbackSectionOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3a51b89c95710a974e87f6add0c7efee00a59df4d5efe494c60edddca40882f1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPullbackSectionOrder:2320",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPullbackSectionOrder:2320"
    },
    {
      sourceName := "OAI.PiExponent.LocalPullbackSectionOrder.factor_coefficient_image",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPullbackSectionOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eb182b978d4d72fae21c1a016ee02634396ee3bfe70cf9c0ce7a797e7655644b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPullbackSectionOrder:1380",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPullbackSectionOrder:1380"
    },
    {
      sourceName := "OAI.PiExponent.LocalPullbackSectionOrder.sectionOrder_eq_germ_order",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPullbackSectionOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "598fae0b766fee87815451e81b76f7401c951cd2022459c5b360236a0e12e9eb",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPullbackSectionOrder:4086",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPullbackSectionOrder:4086"
    },
    {
      sourceName := "OAI.PiExponent.LocalPullbackSectionOrder.topIso_germ_stalkMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPullbackSectionOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4da5c63b320d6449e7b463577ed08d3646c94624c3ad8a876993d5cd9eb1b00e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPullbackSectionOrder:547",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPullbackSectionOrder:547"
    },
    {
      sourceName := "OAI.PiExponent.LocalSectionOrder.localCoefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalSectionOrder",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d61028d1d55c9a8f29751e842d2243b1bbd88d0395faf12efecd1110d183d4f0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalSectionOrder:398",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalSectionOrder:398"
    },
    {
      sourceName := "OAI.PiExponent.LocalSectionOrder.localCoefficient_change",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalSectionOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e87851470d5cbcb06a5ee7a721bd5c496cc65add7afe2dd278198c03e4625678",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalSectionOrder:881",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalSectionOrder:881"
    },
    {
      sourceName := "OAI.PiExponent.LocalSectionOrder.localCoefficient_eq_zero_iff",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalSectionOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d291d0ee255248ab315536113821e909be939647486f1c417657dba9c06b80f0",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalSectionOrder:2375",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalSectionOrder:2375"
    },
    {
      sourceName := "OAI.PiExponent.LocalSectionOrder.localFrameChange",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalSectionOrder",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "02d2c243b4003b198c7b3b0287ed9611cecdc94c1930e347d57cb16d28c22ff3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalSectionOrder:653",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalSectionOrder:653"
    },
    {
      sourceName := "OAI.PiExponent.LocalSectionOrder.sectionOrder",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalSectionOrder",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "da5dd1bf52c85d0f56c0dfad7224fc2c26affea0792d814c8e82bad47774add8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalSectionOrder:1633",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalSectionOrder:1633"
    },
    {
      sourceName := "OAI.PiExponent.LocalSectionOrder.sectionOrder_frame_independent",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalSectionOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "96eb17d80d9258f817d72e3176c77f3d0e626d5a273142de0d8751404d5b77e5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalSectionOrder:1931",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalSectionOrder:1931"
    },
    {
      sourceName := "OAI.PiExponent.LocalizedAlgebraEvaluation.denominatorMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedAlgebraEvaluation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "57e4eb5be67a2012320bff052ce4b81131ff663a838bcc8e47c110b3abf0d502",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedAlgebraEvaluation:337",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedAlgebraEvaluation:337"
    },
    {
      sourceName := "OAI.PiExponent.LocalizedAlgebraEvaluation.evaluation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedAlgebraEvaluation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "583e2c98993d9907361ddc5b90b460172a4c141214cb773963b50d68541e1662",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedAlgebraEvaluation:624",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedAlgebraEvaluation:624"
    },
    {
      sourceName := "OAI.PiExponent.LocalizedAlgebraEvaluation.evaluation_mk",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedAlgebraEvaluation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3835831574c76ac86cd481eba9fc67d2a0f071836308bb2ed009cc75383eff34",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedAlgebraEvaluation:1791",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedAlgebraEvaluation:1791"
    },
    {
      sourceName := "OAI.PiExponent.LocalizedAlgebraEvaluation.evaluation_smul",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedAlgebraEvaluation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e3f4de542974a2d4e2041a504d41e0542355f3ed5c8e3e0b4ae6e03c90cd5ec6",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedAlgebraEvaluation:2068",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedAlgebraEvaluation:2068"
    },
    {
      sourceName := "OAI.PiExponent.LogTailAnalytic.analyticAt_logTail",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f5336a48e0498774df1bed1d1a2833d9647f47ebf17ab5bab4df4620778acd2b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:848",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:848"
    },
    {
      sourceName := "OAI.PiExponent.LogTailAnalytic.analyticAt_prod_logTail",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0eadcc55e799eb662b56885cf64b9ef3a94b93262b7787b7cf834a82e98f1c79",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:2823",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:2823"
    },
    {
      sourceName := "OAI.PiExponent.LogTailAnalytic.eval_trunc_log",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7c369af074e932a80f58e9c1184bb87544cf45a8c6c64b5dff8b8b6dd9da0868",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:372",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:372"
    },
    {
      sourceName := "OAI.PiExponent.LogTailAnalytic.hasFPowerSeriesAt_prod_logTail",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fed27de8a44c0b352b68e5896ae7f2fcdfd55b5cd2d318d55ce8a3ac5cf1bec2",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:8256",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:8256"
    },
    {
      sourceName := "OAI.PiExponent.LogTailAnalytic.hasSum_coeff_mul",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "03b3601ddc266711f4b020b29c1bdcb3039c0af40f2806aa8cf4cabd63ec57d9",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:6271",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:6271"
    },
    {
      sourceName := "OAI.PiExponent.LogTailAnalytic.hasSum_coeff_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "112f56ddb1b972c2202eb26a1b8c5396b76ca1cc2d3222e95f2f312f1958aa2b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:7074",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:7074"
    },
    {
      sourceName := "OAI.PiExponent.LogTailAnalytic.hasSum_coeff_pow",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b1660f134fe8bfdc68454b8ee1a00a5ebdd82cb8c40d2a78106bc589a423783c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:7313",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:7313"
    },
    {
      sourceName := "OAI.PiExponent.LogTailAnalytic.hasSum_formal_log",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aefa8b264882edc6b595418a42ddaee5306ed90ead76a29ade3dd581c473b1a9",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:4162",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:4162"
    },
    {
      sourceName := "OAI.PiExponent.LogTailAnalytic.hasSum_formal_logTail",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "758f216ca3625eef945f655c03811e38700b6288d670daaa1b5ffa27fa301543",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:5368",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:5368"
    },
    {
      sourceName := "OAI.PiExponent.LogTailAnalytic.hasSum_formal_prod_logTail",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1d1a617e6cfd214dc5fec59fac7d006de0fb99c896b36b292405b94d67dce024",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:7671",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:7671"
    },
    {
      sourceName := "OAI.PiExponent.LogTailAnalytic.hasSum_trunc_log",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8aeaa0aacacf57b69b3cfa5ccc9196f7b68ed056cadb3cb2e2d72f979ff3727b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:4505",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:4505"
    },
    {
      sourceName := "OAI.PiExponent.LogTailAnalytic.logTail",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "057f36ca0c65568aaf9357a7f5fc3a412fdad1b00fdb2d7e6ddcca6f3a348e97",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:267",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:267"
    },
    {
      sourceName := "OAI.PiExponent.LogTailAnalytic.norm_coeff_prod_formal_logTail_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "24b547097d5323e7e2bb40895481be90484119a6b05cc3ac8dbc80a1e9813352",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:10069",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:10069"
    },
    {
      sourceName := "OAI.PiExponent.LogTailAnalytic.norm_logTail_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f08de2f45696ee9009c257ec6f10c45b70703d32422ab376bb3f9035921a27af",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:1184",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:1184"
    },
    {
      sourceName := "OAI.PiExponent.LogTailAnalytic.norm_logTail_le_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fbb1a9aa2f930ac70a44ea3f965fc5df3a4df2b3816df9f83779b583f8a66025",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:1567",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:1567"
    },
    {
      sourceName := "OAI.PiExponent.LogTailAnalytic.norm_prod_logTail_le_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "73744f469a410e73908e2d07e1cfb379f4af215d3ed25e6daaf913da27d3c948",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:2412",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:2412"
    },
    {
      sourceName := "OAI.PiExponent.LogTailAnalytic.norm_rowTest_prod_logTail_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "079252196a42aed3d0f4eb5a916537ad7cc3199af601ebf3a8c2687ee7289f7a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:3115",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:3115"
    },
    {
      sourceName := "OAI.PiExponent.LogTailAnalytic.rowTest_prod_logTail_eq_coeff",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6979def9bf341081b4035c777629b7512cf3345eb17ac9954a6d577b55560500",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:8935",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:8935"
    },
    {
      sourceName := "OAI.PiExponent.LogarithmicContactIdeal.branchContact_congr",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7ea510eaaedaf4d1a7ac1c177d9ef802eff5e27c7e3754bd392b69858a6c1810",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal:3187",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal:3187"
    },
    {
      sourceName := "OAI.PiExponent.LogarithmicContactIdeal.expansion_polynomial_aeval",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "02794436f41ba226499a05c1b9d13c706aa04a247b189ed2bc03db8597ea7051",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal:895",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal:895"
    },
    {
      sourceName := "OAI.PiExponent.LogarithmicContactIdeal.expansion_truncatedCoordinates",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "12766e37d8616b2b7dc839ada56a01f18dcfdc3da4372593336fb740a36af037",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal:1285",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal:1285"
    },
    {
      sourceName := "OAI.PiExponent.LogarithmicContactIdeal.logarithmicIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "808809816cc5753c6f106a29cf50f523e133d8f8baf9c0888422d87ecc47833d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal:687",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal:687"
    },
    {
      sourceName := "OAI.PiExponent.LogarithmicContactIdeal.logarithmicIdeal_colength_eq_contact",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "feaed3f9cc04c3a149d05f2532f9da78b261432491561629d2e461f1c774376f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal:4899",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal:4899"
    },
    {
      sourceName := "OAI.PiExponent.LogarithmicContactIdeal.truncatedCoordinates",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "69203cc50c3e5ff6c1ee9b6e3ba81cc6b0990b19acad1c63b13a4f1278debe8d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal:420",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal:420"
    },
    {
      sourceName := "OAI.PiExponent.LogarithmicContactIdeal.truncatedCoordinates_nonzero",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d1835b72f7c9d8c6e495b5a849c83a3b3a846c88546736878ce3fdafa8a566ba",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal:2216",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal:2216"
    },
    {
      sourceName := "OAI.PiExponent.LogarithmicContactIdeal.truncated_contact_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a62118b3f08fba64e238d35aeb4caf6c2f37ca1193e7de1dbc8e55a6267c2e7d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal:3455",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal:3455"
    },
    {
      sourceName := "OAI.PiExponent.MatrixArithmetic.actual_row_card_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "79201b4128cb359eee42bcb0b06d0ef5a742d7ed3c871cc9f24f4989f05cb496",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:10039",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:10039"
    },
    {
      sourceName := "OAI.PiExponent.MatrixArithmetic.ceil_log_weight_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7498e07b4d00c3d109b2ba1690bb98d533c11f3348aea098ff2046bec95e2432",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:10466",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:10466"
    },
    {
      sourceName := "OAI.PiExponent.MatrixArithmetic.columnCost",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5bd035755c88d60de1f563583d48f57a3dbabd49556e57b4facbd0646305b4fa",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:9152",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:9152"
    },
    {
      sourceName := "OAI.PiExponent.MatrixArithmetic.columnScale",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "50b8fdf28699700567042dfc4fbaef4c57be21b41b53362332819893861af63a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:6054",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:6054"
    },
    {
      sourceName := "OAI.PiExponent.MatrixArithmetic.columnScale_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cf26bc4f5f88675cab0b1bb9c450e0bbb14ab2d5429bb6120ac0a8b0ed4a6fee",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:6762",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:6762"
    },
    {
      sourceName := "OAI.PiExponent.MatrixArithmetic.column_coordinate_le_floor",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c1b4d973caa926b7f974d0d3e130215836081c55a70d9f6e6c32eb3967a38e90",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:10702",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:10702"
    },
    {
      sourceName := "OAI.PiExponent.MatrixArithmetic.column_log_cost_le_H",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "81bf255dfc9ad80eac61adfcb2d023977ec5a4357b908e044b8605ba4976f3c4",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:11380",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:11380"
    },
    {
      sourceName := "OAI.PiExponent.MatrixArithmetic.denominator",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "191ad789555602d4d17f47d1c6b892d3573ec2658b7869a52ef3cdf690dbf21a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:6289",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:6289"
    },
    {
      sourceName := "OAI.PiExponent.MatrixArithmetic.denominator_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cfd09dbb9dff6bc2424f7ed7521dd4a6d83d259d38a24fb59a392113aac099d7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:7128",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:7128"
    },
    {
      sourceName := "OAI.PiExponent.MatrixArithmetic.logWeights",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8ef49fa76d76971c4b1d1506cda093434a6c8c316d6d77e2fd7020145cebce76",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:5936",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:5936"
    },
    {
      sourceName := "OAI.PiExponent.MatrixArithmetic.log_columnScale",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a088a43ccf7b36269b05bd700a5949ee5d1d35ffb0235757081a5ec5d1fa477c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:7371",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:7371"
    },
    {
      sourceName := "OAI.PiExponent.MatrixArithmetic.log_denominator_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b420fdff7e8bcc7f3a7eeba52d003ac51a82cc8cdd7b134acebc0f386a9f0ca4",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:7923",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:7923"
    },
    {
      sourceName := "OAI.PiExponent.MatrixArithmetic.log_rowScale",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4768a8e7747cc70a43ba60ca081c2319f00c970aa0fd618d4f4c6856b011cdbb",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:7693",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:7693"
    },
    {
      sourceName := "OAI.PiExponent.MatrixArithmetic.meanRowWeight",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "efb39a5322d227e492931b8b83f48ec2652dd83a2775d047acd0cf9558cd377d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:8704",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:8704"
    },
    {
      sourceName := "OAI.PiExponent.MatrixArithmetic.meanRowWeight_le_theta",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "17434665ee7c690078b1baa04c64e6333c7db5f0ed7aa646752a37ee28b20d78",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:20099",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:20099"
    },
    {
      sourceName := "OAI.PiExponent.MatrixArithmetic.meanRowWeight_nonneg",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5d3fd4a69eaba4a4942c882720d1ac5a0fde85564256ea0f225b860f1c196bfc",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:19735",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:19735"
    },
    {
      sourceName := "OAI.PiExponent.MatrixArithmetic.rationalCenters",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "187f1dbb28fc63e6cbff30f58278fcfd19d43fd578647a5d80b85c36d72e2da5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:6457",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:6457"
    },
    {
      sourceName := "OAI.PiExponent.MatrixArithmetic.rowCost",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "af88da33a3b8c5c31a4f7e2b0923931d89591b41229607bde47c6faadf3c73dc",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:8932",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:8932"
    },
    {
      sourceName := "OAI.PiExponent.MatrixArithmetic.rowScale",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "03a5a484c64b2510306f02abb0456e829fe6d180cb539ee04346442f4e395b35",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:6174",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:6174"
    },
    {
      sourceName := "OAI.PiExponent.MatrixArithmetic.rowScale_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b9e3d1b32b443911f086d7cbaddce654203512038fc3593f6e804f953d4458cd",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:6967",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:6967"
    },
    {
      sourceName := "OAI.PiExponent.MatrixArithmetic.rowWeightedSum",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cf170101c12b2c81f6a16429540aac06dce1f0799c0e88fed6bea724dda2ee06",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:8477",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:8477"
    },
    {
      sourceName := "OAI.PiExponent.MatrixArithmetic.row_weighted_cost_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "47bcfc1395f905d1bc16a41975237e93674d3c5e7f0766d23e082eb3e7e99eec",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:12970",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:12970"
    },
    {
      sourceName := "OAI.PiExponent.MatrixArithmetic.selectedMinor",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3cfa08b2c2b8384642ef8093e8a03fae6d66b29634e3e67341b5fe7d80e99625",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:9514",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:9514"
    },
    {
      sourceName := "OAI.PiExponent.MatrixArithmetic.selectedMinor_arithmetic_lower_bound",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1f76986e1e375b9a157c82b4c1ac4ef7c6d4d13ac64e80c0ebf2c12aa6f5f8b0",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:17647",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:17647"
    },
    {
      sourceName := "OAI.PiExponent.MatrixArithmetic.selectedMinor_clearing_bound",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "437ee24b77dfbdb86388a8c0d3c690d65e2ac8fb346c12669d73c15d510c224b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:16341",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:16341"
    },
    {
      sourceName := "OAI.PiExponent.MatrixArithmetic.selectedMinor_entries_gaussian",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "695c55497715714da28c172f0720064d171aca004733e3bfdebd508aa6769dfc",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:14846",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:14846"
    },
    {
      sourceName := "OAI.PiExponent.MatrixArithmetic.selected_column_log_cost_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "20b06edfdf57a3713e600c7918030bc76b51a21645727c80b30f0941fed128a8",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:12243",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:12243"
    },
    {
      sourceName := "OAI.PiExponent.MatrixArithmetic.truncationOrders",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e5ddcff4addb67930e5989ac8fb20bebee5ecd43f111be1b5e2837717f82121f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:6617",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:6617"
    },
    {
      sourceName := "OAI.PiExponent.MatrixCounting.lowIndexCount",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f312d71befd7a7f4af25b7bee7c322982c9d29571b79938719c728e38fb5f5b1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting:447",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting:447"
    },
    {
      sourceName := "OAI.PiExponent.MatrixCounting.rationalLogWeights",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "38d3ed072c371bb871c1c1986d06d5b6b48af53449243541d8080eff05ba3991",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting:619",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting:619"
    },
    {
      sourceName := "OAI.PiExponent.MatrixCounting.rationalLogWeights_cast",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5387204acae68b0a4951b5ebefe6fc8b8631c0a74805ea437729a0c2ed9da54e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting:745",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting:745"
    },
    {
      sourceName := "OAI.PiExponent.MatrixCounting.rationalLogWeights_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "385cf5ec611547d2eddcaa13f22a219735ab256e7236dacb68d4c61a47d27626",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting:966",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting:966"
    },
    {
      sourceName := "OAI.PiExponent.MatrixCounting.rowCount",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7954110a276ead7f2a49e5073418ba4ecfc17e7f9a33de9bd482fa89f88e602e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting:239",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting:239"
    },
    {
      sourceName := "OAI.PiExponent.MatrixCounting.tendsto_collisionRatio",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e32d2052ed79617b4775397d831a6842a046494611f139ba9924c5bcff6f2236",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting:5780",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting:5780"
    },
    {
      sourceName := "OAI.PiExponent.MatrixCounting.tendsto_lowIndexCount_normalized",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c76f1b372934580db8ba3d153862653798d3970d0bb0264d56ffb13fe5d2692f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting:2857",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting:2857"
    },
    {
      sourceName := "OAI.PiExponent.MatrixCounting.tendsto_rowCount_normalized",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b576bf07ee19920a3f2068920da62e9a6795bbb59bbbaa7bd3169410f3f3319a",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting:1212",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting:1212"
    },
    {
      sourceName := "OAI.PiExponent.MatrixCounting.tendsto_row_lowIndex_ratio",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f4dd93aaa7e0f93d6d09aa310b18c03cf82c22656ad7b651f5105c7e7d7db1ef",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting:4010",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting:4010"
    },
    {
      sourceName := "OAI.PiExponent.MatrixTranslation.card_transverseIndices",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "917e8bf91372cdd51fcba08731aa0bc3aa04920275ddc64f78b25fddc174a8a2",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:3086",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:3086"
    },
    {
      sourceName := "OAI.PiExponent.MatrixTranslation.coordinate_translation",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f4d04205d241ded7a808b8260de4743aa3e5b12cf17f1d1890d200fa4648a9a6",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:5984",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:5984"
    },
    {
      sourceName := "OAI.PiExponent.MatrixTranslation.det_dependent_row_sum",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "209bf01ca92570e5fac9b6d4a5dc409ec3a7399449472844e1ff03216c716d63",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:9819",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:9819"
    },
    {
      sourceName := "OAI.PiExponent.MatrixTranslation.det_matrix_translation",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a367e96e29e6f34fed3c2816c4667f8c73a7769c14341e0b0b4685b8e7749ead",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:10656",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:10656"
    },
    {
      sourceName := "OAI.PiExponent.MatrixTranslation.formalMonomialImage",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5dea6349ff9c233c42675df66c6cebce9ab70403328b1b1c95bc13fadb69ca3f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:5652",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:5652"
    },
    {
      sourceName := "OAI.PiExponent.MatrixTranslation.formalMonomialImage_coeff",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d551991b9921a704775b719d71dbbbb9807133df942b7265f151fa775ad45ffd",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:7462",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:7462"
    },
    {
      sourceName := "OAI.PiExponent.MatrixTranslation.matrix_entry_translation",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "865c4917bcce1cdfef35e6d74d6628686589c39c0ee637502c28e5f17271c8da",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:7913",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:7913"
    },
    {
      sourceName := "OAI.PiExponent.MatrixTranslation.matrix_entry_translation_choices",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fbcc3d3caf43f8b4ece24370e2e2f857acf47270552851f9aade28ce32b1e943",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:8799",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:8799"
    },
    {
      sourceName := "OAI.PiExponent.MatrixTranslation.mem_transverseIndices",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0fe8d676231db118ce48d4f7d951b18dfaa19eb6e52715d43489f97fe13d5f48",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:2773",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:2773"
    },
    {
      sourceName := "OAI.PiExponent.MatrixTranslation.periodCoordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "25cf7e497f7a9c8bd12da4dad7c421acf2fdc2ff3617a728a93ef1e7a8ce9325",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:264",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:264"
    },
    {
      sourceName := "OAI.PiExponent.MatrixTranslation.periodMonomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "00f510252ddb80f83f5274bf860cdd2cab858352b1ba8b60d63131111a111d39",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:400",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:400"
    },
    {
      sourceName := "OAI.PiExponent.MatrixTranslation.periodMonomial_as_shift",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8afb6ceeb20b220b2631f1028b525559028360414bc3324ee7b2902732e99104",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:631",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:631"
    },
    {
      sourceName := "OAI.PiExponent.MatrixTranslation.periodMonomial_coeff",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a74fdd3bb69cd19dbb610701cc1a5892bfdf356476bd5103d1b2c482967f264a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:961",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:961"
    },
    {
      sourceName := "OAI.PiExponent.MatrixTranslation.periodMonomial_shift",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c45e80e282c695baafb492e36405c68ee010fd4e1ab7ac1ff809a37993df022d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:6555",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:6555"
    },
    {
      sourceName := "OAI.PiExponent.MatrixTranslation.periodMonomial_support_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a7ddba2a23ed9a6d0e1310c38bbd22240d294f52639e873e1b28c66a6fd4aa75",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:1528",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:1528"
    },
    {
      sourceName := "OAI.PiExponent.MatrixTranslation.periodMonomial_support_subset",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "18c4a14a003b7bdff5d47db6599c8d7ad2903d5b8e63141b484cec3fe80d2522",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:3282",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:3282"
    },
    {
      sourceName := "OAI.PiExponent.MatrixTranslation.periodMonomial_support_weight",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1e152a90e28474d4666f23f329996fe388a1604d32e1895a88414cce6acab111",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:2099",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:2099"
    },
    {
      sourceName := "OAI.PiExponent.MatrixTranslation.row_term_count",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3191bd7582f7e728e4dba5a01fd3febf6abc9e87af6ce9b55b93e6209861172e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:5048",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:5048"
    },
    {
      sourceName := "OAI.PiExponent.MatrixTranslation.transverseIndices",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c6cfe56913921e51b061d1b65d25f7fb23a4d9fd4e04b5a47b355592b769ef8f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:2572",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:2572"
    },
    {
      sourceName := "OAI.PiExponent.MatrixTranslation.transverseIndices_card_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dcc2ee67ba8b9dc7d270bec768466e290ef45f5ea622d05b69e2c5b4c6762c7b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:4319",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:4319"
    },
    {
      sourceName := "OAI.PiExponent.MatrixTranslation.transverseIndices_coordinate_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b41a3fbc8d59590d4654a18bb010bcbd2235eb3a6546fbd4035a786c6b3b1eef",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:3686",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:3686"
    },
    {
      sourceName := "OAI.PiExponent.MatrixTranslationBounds.actual_error_exp",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "678e0d1b3f42fcb96cd77b910b351e47880bda3927ed5735cdfa9af9c87f6a83",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds:7322",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds:7322"
    },
    {
      sourceName := "OAI.PiExponent.MatrixTranslationBounds.error_power_product_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8be1d45a13cfb3d4e31a4d25abc90f4c002318700dd7d7654e3a664b583f34d7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds:433",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds:433"
    },
    {
      sourceName := "OAI.PiExponent.MatrixTranslationBounds.norm_rowScalar_exp_basic",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bdfc67f71e83a24c2fa174c320e769166d9f85297e5111d7bbe3383bb73e324f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds:883",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds:883"
    },
    {
      sourceName := "OAI.PiExponent.MatrixTranslationBounds.norm_rowScalar_exp_weight_difference",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "85201b79d5f90f2ec59886dfc9eded124d8dd76a1ec99a494c9ea3c388207e1b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds:6243",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds:6243"
    },
    {
      sourceName := "OAI.PiExponent.MatrixTranslationBounds.norm_rowScalar_exp_weighted",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b5da5181ec583ac24cfc4ab3b86109bd8323a3045379663387c05a6e46915ed5",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds:3283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds:3283"
    },
    {
      sourceName := "OAI.PiExponent.MatrixTranslationBounds.residual_exponent_identity",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "df2c17a8b09a89e1559cc40fce1f3f18603f73bba7d0deda814b9dab1666e9b1",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds:2694",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds:2694"
    },
    {
      sourceName := "OAI.PiExponent.MatrixTranslationBounds.sum_exponents_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3d792aad0456088274041f803a09347b4a00ebaff05390cedbd859586e4776ed",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds:2113",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds:2113"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_017.jsonl"
