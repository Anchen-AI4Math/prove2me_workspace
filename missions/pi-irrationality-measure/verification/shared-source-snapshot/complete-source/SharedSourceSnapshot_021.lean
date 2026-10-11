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
      sourceName := "OAI.PiExponent.Parameters.mk.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5117ffeec9d4cc0dc67cba1eee378f06f6fd17e0dd45e3de66fac5f2bedb08eb",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ca392e756dc60c8923068c5514391b33470b162a7fa98ddc6dfc600189b73e01",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.one_lt_B_div_A",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bce9660bae08ec5501e1d536de69a1056d4090996748ff83d275fad82334a3bf",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:6012",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:6012"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.one_lt_C",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "08c66cfec231332f79f5b9beafcd9b4ea3c7a3cae7659f61081d63a749aa054b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.one_lt_C_theta_div_B",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e632a89989571627fc375bf5abe9183e97d6326ddb5749323af6e7e5aa089ada",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:5875",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:5875"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.rec",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "rec",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2bc2f50c6fc2cd9b3b010eb22618c5ccda2dbeb9f070da768579876195eebb37",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.recOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "55b2878abd89a225fa453669d093e9984dc054e329e650f35e579ed91ebc1c53",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.theta",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "31398ad0ca6bea5cd9f9a5281e73a6e514e34bfa9d100ab9b0137324edb592a5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.theta_lt_A",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d4abb8c9fb3d254317e4b080b65a01f32f13042a1beccbbb9bc66c8dbe48cac3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.theta_lt_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "520d63465407a6537bf087fd28bed73caced16daa228316b49ead79f7d81509f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:5656",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:5656"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.theta_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "72465333cd1627e9ed4b04f240468bea82c752fa5eef9be02d37292c22a7a2bf",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.PeriodAnalytic.analyticAt_periodFunction",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c7756bad8592ab6ee9b0ce132e6d447b1f974d6f741fdf6923c7f377abd10c8b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic:1845",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic:1845"
    },
    {
      sourceName := "OAI.PiExponent.PeriodAnalytic.columnFunction",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "32c0368743a1dc58171c4d42c68749ed87a3cfec02c2dfa7a30fa8f19ed96464",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic:6625",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic:6625"
    },
    {
      sourceName := "OAI.PiExponent.PeriodAnalytic.differentiable_columnFunction",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bd2de8ce44594e9894ac09846c4ce9e4fc66ab41a7527cf824fba30b9cce4cf4",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic:6855",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic:6855"
    },
    {
      sourceName := "OAI.PiExponent.PeriodAnalytic.exp_period_center",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4e5c6d86a1fe9fa0782d3a1a1b877d309dd64a7154a5e4274b0476dcfbbb7168",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic:4757",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic:4757"
    },
    {
      sourceName := "OAI.PiExponent.PeriodAnalytic.hasFPowerSeriesAt_periodFunction",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "70d8b08d7a56df9ffcb2b4acba26324d0d3604054eea53311aa22d14ceb211c3",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic:2198",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic:2198"
    },
    {
      sourceName := "OAI.PiExponent.PeriodAnalytic.hasSum_coeff_C",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9b61250180bba780d8e50f9514553c5d64eba572c2a50ceae6710835aef52602",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic:602",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic:602"
    },
    {
      sourceName := "OAI.PiExponent.PeriodAnalytic.hasSum_coeff_X",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "23efc30556ebe5e7d4bddcf2fb3549938659642b14f55d639ed00aa14acde098",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic:826",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic:826"
    },
    {
      sourceName := "OAI.PiExponent.PeriodAnalytic.hasSum_coeff_add",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a15d8fc5a0818ce51deb81acba9b4aca799f0160fdf0de3d2d9da1f32ffaa5bc",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic:1064",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic:1064"
    },
    {
      sourceName := "OAI.PiExponent.PeriodAnalytic.hasSum_periodSeries",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4f15874cf757d9175de6de4ae92632643bed126943a48f085a83aed4e747a2b7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic:1378",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic:1378"
    },
    {
      sourceName := "OAI.PiExponent.PeriodAnalytic.norm_binomial_product_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d9410930b835d0cf72900065285bbc022a79b68f12f78d3c1bce152bc0003eb6",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic:6174",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic:6174"
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
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic:462",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic:462"
    },
    {
      sourceName := "OAI.PiExponent.PeriodAnalytic.periodFunction_eq_exponentialMonomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "df3df298381008b16d30d420a2525e27b9a80b6226bb640f3ce6bc77a1eaab68",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic:4241",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic:4241"
    },
    {
      sourceName := "OAI.PiExponent.PeriodAnalytic.periodMonomial_coeff_eq_rowTest",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4fafef7fbbc9ede932d720478c0fd34678ee4efbf009e762c14830b9eb105f66",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic:5553",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic:5553"
    },
    {
      sourceName := "OAI.PiExponent.PeriodAnalytic.periodSeries",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4442fc28bfc5653dfe71bfd89523b0b5ec01afb86e48a494c1b1145301c2a20f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic:277",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic:277"
    },
    {
      sourceName := "OAI.PiExponent.PeriodAnalytic.rowTest_congr_sphere",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c431425259069836d1e3a43b4257dd263cb1147b13dd7ef64d65b71abd839dba",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic:3818",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic:3818"
    },
    {
      sourceName := "OAI.PiExponent.PeriodAnalytic.rowTest_exponentialMonomial_eq_coeff",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "236a65cd4118ccdb27c8e506abc17431e57fa4e94e9b7148ba2ae78a03b07b5e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic:4936",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic:4936"
    },
    {
      sourceName := "OAI.PiExponent.PeriodAnalytic.rowTest_periodFunction_eq_coeff",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6a3e1c83c74b1a74d6147963bc4067df40d2dcdda0a953f58c82bd5cc8c381c9",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic:2792",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic:2792"
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
      sourceName := "OAI.PiExponent.PersistentComponents.exists_persistent_component_positive_height",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f18c8118e202c97dae787dc954a5616d387e136f69580f1ade4580b7f0bd5479",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents:6156",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents:6156"
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
      sourceName := "OAI.PiExponent.PersistentComponents.exists_persistent_minimalPrime_pair",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a268f0a321a1527023b077ac695d901d1f42f8999906b707d3eb92c7af15e7e7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents:4132",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents:4132"
    },
    {
      sourceName := "OAI.PiExponent.PersistentComponents.minimalPrime_height_pos_of_nonzero_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "57d6dd1129655e8674c47e24e1f1283230333a4c5af07da30a7576b3fc32a940",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents:5761",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents:5761"
    },
    {
      sourceName := "OAI.PiExponent.PersistentComponents.minimalPrime_persists",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cceec43a6e2138e599c6a4ee9e92b1f46b07e437765a1887507f7b955794115d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents:3880",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents:3880"
    },
    {
      sourceName := "OAI.PiExponent.PersistentComponents.prime_height_step",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0c8857de4ddb46cebd8838b4296ac0feb39e6df4216f5128346531b6011aa4cb",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents:152",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents:152"
    },
    {
      sourceName := "OAI.PiExponent.PersistentWeightComparison.UniformRectangles",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PersistentWeightComparison",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "41e466667273e1353da80e36f44d1bc014e200ff3ed3a795eb5ea51fd3d41426",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PersistentWeightComparison:673",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PersistentWeightComparison:673"
    },
    {
      sourceName := "OAI.PiExponent.PersistentWeightComparison.comparisonConstant",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PersistentWeightComparison",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c8115857447dca7c0c4d105836cda2bde07cba4fa10c3333878b9c09f198b920",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PersistentWeightComparison:539",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PersistentWeightComparison:539"
    },
    {
      sourceName := "OAI.PiExponent.PersistentWeightComparison.eventually_uniformRectangles",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PersistentWeightComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "05443490b6f12ce35e2753387163c5bf53d689da20ef4cde55ba5f54509379f6",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PersistentWeightComparison:896",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PersistentWeightComparison:896"
    },
    {
      sourceName := "OAI.PiExponent.PersistentWeightComparison.logarithmic_normal_comparison",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PersistentWeightComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f13f8eec5c088062b043cd051c88a68929fe73c35159c94f85073a666c1db55b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PersistentWeightComparison:1179",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PersistentWeightComparison:1179"
    },
    {
      sourceName := "OAI.PiExponent.PersistentWeightComparison.logarithmic_persistent_comparison",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PersistentWeightComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a6bb680535dd12ec6fe8e72146cf208155882d8c743aac831bdd0054cc54dfa3",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PersistentWeightComparison:3954",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PersistentWeightComparison:3954"
    },
    {
      sourceName := "OAI.PiExponent.PersistentWeightComparison.ordinary_normal_comparison",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PersistentWeightComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e41e6e05ed04f09d8c1573354b52e8188ffe8cb3cf7f9fc203f1499b85f9f7b1",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PersistentWeightComparison:4791",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PersistentWeightComparison:4791"
    },
    {
      sourceName := "OAI.PiExponent.PersistentWeightComparison.ordinary_persistent_comparison",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PersistentWeightComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "68b7faf617555e29ad7adfe6c56b5350ea2af1593c6650393686d00861abf781",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PersistentWeightComparison:7528",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PersistentWeightComparison:7528"
    },
    {
      sourceName := "OAI.PiExponent.PiEventualLowerBound",
      expectedModule := "OAI.NumberTheory.PiExponent.Statement",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5e5fedea2064a11a77a1b0f1f5457a715dde48df8a6975b2c491cb9b39eed93e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Statement:642",
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
      sourceName := "OAI.PiExponent.PlaceCenteredBranch.fibre_nonconstant",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f220079ea8ea7cf144f45daf36a20c4471ec8711c15a907a66d3ffa8c9457701",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch:8412",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch:8412"
    },
    {
      sourceName := "OAI.PiExponent.PlaceCenteredBranch.lift",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c90d949223f0c7d759b05a33be66f039ec88f2541b2939e738000cc00fca76c7",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch:469",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch:469"
    },
    {
      sourceName := "OAI.PiExponent.PlaceCenteredBranch.lift_aeval",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3a9a161775d5ed1da638d1b7c7a45ed4a76c602a154fd9fd7b0362a887e5c7ef",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch:1462",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch:1462"
    },
    {
      sourceName := "OAI.PiExponent.PlaceCenteredBranch.lift_nonconstant",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8e6b9f52b1a552992fc5dfb401f5dda141be000808b7eda961f42a04dfac0271",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch:787",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch:787"
    },
    {
      sourceName := "OAI.PiExponent.PlaceCenteredBranch.lift_residue",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ba297c5fe4bebd086cf255b840f898e378616b1fa80a7858fc3e30e2a9fe87fc",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch:2866",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch:2866"
    },
    {
      sourceName := "OAI.PiExponent.PlaceCenteredBranch.logContact",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "771aaf58e6aaae678ec4669250f92e9308eabbf280f160fba585db9095f8bbe0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch:4250",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch:4250"
    },
    {
      sourceName := "OAI.PiExponent.PlaceCenteredBranch.logContact_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a37267a475c0b79994486ee84f098abd0244b7fcf234f32fc3c8177d2bd62832",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch:8806",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch:8806"
    },
    {
      sourceName := "OAI.PiExponent.PlaceCenteredBranch.logContact_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "93c6c5779a9820a0a1034ece690b3b3ac909bedc01922d253c1a2ecbe88f0a77",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch:4650",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch:4650"
    },
    {
      sourceName := "OAI.PiExponent.PlaceCenteredBranch.logLift_nonconstant",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1e4aa5d2efd367cc6ad9b0daa6bd35684abd3d9ea3fbbacdc8b48b86b3e1d847",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch:3630",
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
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch:5114",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch:5114"
    },
    {
      sourceName := "OAI.PiExponent.PlaceCenteredBranch.ordinaryWord_field_order_lower",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aef7a44d9a75689f5279dfd3d2e5cf43c1d3b581727df0d3e9ea3275fc3a5c8a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch:7329",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch:7329"
    },
    {
      sourceName := "OAI.PiExponent.PlaceLocalRing.residue_integral",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceLocalRing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8556d53e243f09fd9f62ba6da1bea20cdc81428e6593d571b8855b2955d341b0",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceLocalRing:1011",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceLocalRing:1011"
    },
    {
      sourceName := "OAI.PiExponent.PlaceLocalRing.residue_integral_of_algEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceLocalRing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "91234f3046524c43f65cf9ed6f6d2f912f053bbc237159acca740313defb2bcc",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceLocalRing:507",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceLocalRing:507"
    },
    {
      sourceName := "OAI.PiExponent.PlaceParameterModel.parameter",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cc1872affb389aebc96e556b5fc64b3bbb1e3dc6ef7ecbba6dadeba911ae8f88",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel:862",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel:862"
    },
    {
      sourceName := "OAI.PiExponent.PlaceParameterModel.parameterCenterLocalAlgEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8363433a27ad8c8df9f34020d02e957d782a1341b6e20bafaaf2422bb8141f2f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel:4581",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel:4581"
    },
    {
      sourceName := "OAI.PiExponent.PlaceParameterModel.parameterCenterLocalRingEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "20686442b0c766d4cc103b301460fe08b1c566c5f39516db6e009c7c2fd52a92",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel:2248",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel:2248"
    },
    {
      sourceName := "OAI.PiExponent.PlaceParameterModel.parameterUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ef81fa8bdb5712dbd033d24194ccd82cc67ed8666a54e9ab98198a6a225574b4",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel:523",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel:523"
    },
    {
      sourceName := "OAI.PiExponent.PlaceParameterModel.parameterUnit_order",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d1d539da4730833d6788e5c209976f1308810c0449e12194a05a2ea2b3e70d28",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel:662",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel:662"
    },
    {
      sourceName := "OAI.PiExponent.PlaceParameterModel.parameter_nonzero",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2baa35c5b96563c6a03ec3db943ff196141850f950a767fd02c6c99824d82867",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel:981",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel:981"
    },
    {
      sourceName := "OAI.PiExponent.PlaceParameterModel.parameter_positive",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c48c93a4a3a51f30a66bb04ba54a1f2e087879cfe1f5572366ff9d4c870b1ebb",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel:1391",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel:1391"
    },
    {
      sourceName := "OAI.PiExponent.PlaceParameterModel.parameter_transcendental",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "032e74653ffe313e03e65bd4e4472c5d408bd80d49c69487807879ab60ea66bd",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel:1574",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel:1574"
    },
    {
      sourceName := "OAI.PiExponent.PlaceParameterModel.parameter_value",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d0d63f10340681a8899d60bb7da0bc78a053ae160cf6b8e86bff0ab7554e2b72",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel:1138",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel:1138"
    },
    {
      sourceName := "OAI.PiExponent.PlaceValuationRing.constantsAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "606171efce288f7544a8819928aa1da7d719e8c268c7226824096f27f33cc076",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing:673",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing:673"
    },
    {
      sourceName := "OAI.PiExponent.PlaceValuationRing.constantsHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "052cdd8ca4545ae2fa4f340c191133d1f8bf8931e9b7dfa75490693bf9e6f303",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing:371",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing:371"
    },
    {
      sourceName := "OAI.PiExponent.PlaceValuationRing.discreteValuationRing",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d8523c5c826e8e1d68a8d2b8b5ce4c74ad198ac91b7b04488c1c1e229764e286",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing:1383",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing:1383"
    },
    {
      sourceName := "OAI.PiExponent.PlaceValuationRing.ring",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e92acd080d29fce1757671f3a4dd37ddf358c05ba22dbf6a586cf0b34c760bd3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing:262",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing:262"
    },
    {
      sourceName := "OAI.PiExponent.PlaceValuationRing.scalarTower",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d62b7bbfec228f8a526e5fb2aa8b431c27db7cf81b9b6ae01f87a98b23c26cb3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing:782",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing:782"
    },
    {
      sourceName := "OAI.PiExponent.PlaceValuationRing.valuation_eq_fractionAddValuation",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c6313401f0ab07dfb4329eae6c840c05be68d1768a3e76f9efabd29ee60c1923",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing:1815",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing:1815"
    },
    {
      sourceName := "OAI.PiExponent.PlaceValuationRing.valuation_nontrivial",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a87b4102147d1b8d0b6b8d5f7066582fc5adf34268866ccf2d9e31b53982cf33",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing:1050",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing:1050"
    },
    {
      sourceName := "OAI.PiExponent.PointLengthEquiv.evaluation_map",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PointLengthEquiv",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "773a789f41bf208ecea7703d78e9b32276e817d1652b74d3e693cca4c20121a4",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PointLengthEquiv:283",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PointLengthEquiv:283"
    },
    {
      sourceName := "OAI.PiExponent.PointLengthEquiv.pointIdeal_comap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PointLengthEquiv",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "998084daaff7c38d6d0d6afff518c1e64d2447daad99abb1f4edc0a2d1e44dc6",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PointLengthEquiv:650",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PointLengthEquiv:650"
    },
    {
      sourceName := "OAI.PiExponent.PointLengthEquiv.pointIdeal_map",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PointLengthEquiv",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3a8372a46befc2d3fb7051f7aa59ba4be5d95e13fda5e6698cfc550b8c53db32",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PointLengthEquiv:1006",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PointLengthEquiv:1006"
    },
    {
      sourceName := "OAI.PiExponent.PointLengthEquiv.pointLocal_quotient_length",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PointLengthEquiv",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6abf61f0780509c3f9072ae145048e7d0a2189264b3ff93e332f6f3e520a43dc",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PointLengthEquiv:1327",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PointLengthEquiv:1327"
    },
    {
      sourceName := "OAI.PiExponent.PointLengthEquiv.point_mem_minimalPrimes_map",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PointLengthEquiv",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "862806b82f59ab352077e1d0b3e9defe33d8782e8ee43f237817d634dd6ad978",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PointLengthEquiv:2071",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PointLengthEquiv:2071"
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
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential:1534",
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
      sourceName := "OAI.PiExponent.PolynomialPoleBound.polynomial_order_lower",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPoleBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e4fd68dfb2fe6c88431d9d21276923aec7e812f3febad6ef3ce9fe71b465bd8d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPoleBound:2255",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPoleBound:2255"
    },
    {
      sourceName := "OAI.PiExponent.PolynomialPoleBound.realValuation",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPoleBound",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "57c2f673f59c9ff0ea983933561f985f97de727282da3f17465cf132202b1ec2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPoleBound:299",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPoleBound:299"
    },
    {
      sourceName := "OAI.PiExponent.PolynomialPoleBound.realValuation_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPoleBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d5d2900734eb6c9c4ef7e6cdab89450aa64ac4fea8bd441eb862ae7949277824",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPoleBound:515",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPoleBound:515"
    },
    {
      sourceName := "OAI.PiExponent.PolynomialPoleBound.valuation_prod",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPoleBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cc64eed0959e158c494055ba4bc062116089927f0f61c8c17e41866a33448d8f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPoleBound:676",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPoleBound:676"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.PowerModule",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c3859244b1dcdeb393478405da7224316a3cebafb72506ac66bc604ea3958b00",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis:1830",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis:1830"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.combine",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ca9222628cfec9ea5ddd42993f6826d5853fd7ffb16d858773d843e0bac3a2c8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents:567",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents:567"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.combine_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "86eb3d9de0aee4cd0e2f6021d4feb40e29e81e76dc241c602a71c257176ac091",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents:1172",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents:1172"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.combine_quotient_residue",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a89a2cd18a1e71983ed220c0cc18a3c5186fa2e305d32bcb1d6105c0ab9c3744",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents:1350",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents:1350"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.decompositionAddEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e1a36286622de0c39517bc841ac56eb2ba1088b3d110fcba3a4538524264a156",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis:215",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis:215"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.decompositionAddEquiv_monomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "afc37c29a0ee6a76cda570564a060f33e6af953304b1ca5cabb9bcef44199bb9",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis:651",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis:651"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.decompositionAddEquiv_power_mul",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e0a592ac570bbe0e2ec33b991899f4e30c16d8e57439f485ecc35b54c1eb613b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis:1013",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis:1013"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.exponentEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c2b4f310da919a87ca89735fede3712585a223858af713f71f5e0d7a95c281fb",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents:2166",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents:2166"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.instCommRingPowerModule",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c41220f1acc6d5c8986fb72997c837fa2e9d2a21f9e1fc6a1cfed8b356327184",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis:4048",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis:4048"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.instCommSemiringPowerModule",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8a707a1519ffe15370c253bc70d1ac5aef505acc8e2764bf02eecd0c5e050e27",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis:1923",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis:1923"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.powerAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8ac65fb160e6e7917339c1999d6db0ffecf71b97466400df83a93901d98c2f99",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis:2144",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis:2144"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.powerSubstitution",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverSubstitution",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0f764fdc929cdd973233c7cee0a7a1979528f21fb68ae1167bfeadc8046aec23",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverSubstitution:953",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverSubstitution:953"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.powerSubstitution_X",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverSubstitution",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "478064bd6318f865c14002d3498735b77bd415752aedffb15d579463363b9577",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverSubstitution:1107",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverSubstitution:1107"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.powerSubstitution_eq_mapDomainAlgHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverSubstitution",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4c53f80a5a201ac2a36c31c194e006d1381535487154a7cd081c6255a2515ff1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverSubstitution:1308",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverSubstitution:1308"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.powerSubstitution_monomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverSubstitution",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3ed98e4274cabd3ff964381a7ad292093085e80e3b40972d7b2aacd177ee474b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverSubstitution:1816",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverSubstitution:1816"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.quotient",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b5c3a9cd7523d594c4699a6e5a62b56454234bbfd87f8e71261ac4dcbde28db7",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents:291",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents:291"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.quotient_add_scale",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7e816f8bf081261433c64366ce2b0b012e795a20e088941bdcef5939280bb566",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents:2816",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents:2816"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.quotient_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6cf9289f43ee610f2b61b65de8207b86d2312362267d9336d536b4348e295fd9",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents:859",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents:859"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.quotient_combine",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e7284c0fa4e5b434b787f82bd9b080b706a5d839c77053d77ff41fc16bf89ff5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents:1622",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents:1622"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.residue",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "35f18a9e60b604f4a5073f2af3b4ee629a1be0c626083407bb6b8c4db3249b4d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents:417",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents:417"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.residue_add_scale",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "60903981891d06518bdd09c1e812df889119208ce553975190b647acb15b4efd",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents:3087",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents:3087"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.residue_combine",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ad86c61cb14ba8a4191b2dbecfc65284c79f0851134f4892be664201cdefc32f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents:1915",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents:1915"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.scale",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c6753d05f70c264d4d45e58326e0fc5ff0ecfca886bdcd974c8331d05bb6ab47",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents:168",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents:168"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.scaleHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverSubstitution",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "daabb1314c7c0d7ff41ece263fa47403f62a78158409b2bbe6f229f070daf80a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverSubstitution:204",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverSubstitution:204"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.scale_add",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "60c525deffaa1834f742df5434bc4e9c13a796bf223bd15c6cb14ebb87c2fddc",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents:3840",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents:3840"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.scale_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5b370dd3f1eac1c9ad08cf02e614777493775e7abe2611916fbb6ce03805cddf",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents:732",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents:732"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.scale_single",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverSubstitution",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3463e3b65c6f8fe074cbe165d87b6a8d9463c2ab1d2c144cdab3cd943501d6eb",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverSubstitution:468",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverSubstitution:468"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.scale_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ba90fd73d362dd7276d368d772fc2f5d538f4abdcb0594e8de37fb5ad06958f7",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents:3754",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents:3754"
    },
    {
      sourceName := "OAI.PiExponent.PowerCover.toPolynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c8304a3c455d77cc1c6370b29ee2ba354bac0244739136f3763ce3a57f69bc3c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis:2042",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis:2042"
    },
    {
      sourceName := "OAI.PiExponent.PresentedIdealIso.idealPower_presents",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalPowerPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8cd5264ef1535dc7211c96ec5f425686cb3b75f463f7e60b798290cd1a872fad",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalPowerPresentation:1757",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalPowerPresentation:1757"
    },
    {
      sourceName := "OAI.PiExponent.PresentedIdealIso.imageIdealSheaf_eq_comap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PresentedIdealIso",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b425d91a42faf1ca69181c7c1c4c64e7e8010090d6769607decbf0aeb1782701",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PresentedIdealIso:573",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PresentedIdealIso:573"
    },
    {
      sourceName := "OAI.PiExponent.PresentedIdealIso.imageIdealSheaf_idealPowerInclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalPowerPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8461991eb0c150d9c0cc47626e6614043cbcd981826a4ecb5b8125d7681b1af4",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalPowerPresentation:559",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalPowerPresentation:559"
    },
    {
      sourceName := "OAI.PiExponent.PresentedIdealIso.inclusion_structureMap_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PresentedIdealIso",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ccbad2825877b9b6540776a9500252c1e2fb774b67a670fe71828f0739367249",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PresentedIdealIso:2132",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PresentedIdealIso:2132"
    },
    {
      sourceName := "OAI.PiExponent.PresentedIdealIso.powerIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalPowerPresentation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "38ac5f4cad8bdc1a93d0651650b930f281ace5daf79d039dfca9dcf835709813",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalPowerPresentation:2891",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalPowerPresentation:2891"
    },
    {
      sourceName := "OAI.PiExponent.PresentedIdealIso.presented_range_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PresentedIdealIso",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "12ea89930925ef8cd1230b62c0e6d0b08af31554fe870661fb19fb2ac2b672fa",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PresentedIdealIso:1554",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PresentedIdealIso:1554"
    },
    {
      sourceName := "OAI.PiExponent.PresentedIdealIso.toIdealModule",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PresentedIdealIso",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8265411501c02a3abe7a1c8cf73b417632451dac1e9caa1c4d8f865cd77fd4d1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PresentedIdealIso:2612",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PresentedIdealIso:2612"
    },
    {
      sourceName := "OAI.PiExponent.PresentedIdealIso.toIdealModule_inclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PresentedIdealIso",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "55b64fcc4c7d7afb37c49e2002a40a6ea2d042a7dbe45657cd84714efc91ce97",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PresentedIdealIso:2924",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PresentedIdealIso:2924"
    },
    {
      sourceName := "OAI.PiExponent.PresentedIdealIso.toIdealModule_inclusion_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PresentedIdealIso",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "24e896ba1e5a846d847936772863e479832dced7c726f9b99d305c3deae71020",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PresentedIdealIso:2924",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PresentedIdealIso:2924"
    },
    {
      sourceName := "OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PresentedIdealIso",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aa41f6215a51d9491673696026e7de23364ed8ca3f3300717425fa1759a99034",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PresentedIdealIso:3227",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PresentedIdealIso:3227"
    },
    {
      sourceName := "OAI.PiExponent.PrimeLocalCotangent",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1343d05473fa185ee216b1e81f0d56214a0d6a813c338fbe86a169ce71651b29",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent:1608",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent:1608"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_021.jsonl"
