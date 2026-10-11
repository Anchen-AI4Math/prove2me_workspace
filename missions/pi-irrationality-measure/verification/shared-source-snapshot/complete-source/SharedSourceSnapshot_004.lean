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
      sourceName := "OAI.PiExponent.Collision.norm_det_le_of_entrywise_hasSum",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.CollisionLimit",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1d109a2db7705352ef07d26c91148ef062fd13ba0d57163283763862d1576514",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.CollisionLimit:818",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.CollisionLimit:818"
    },
    {
      sourceName := "OAI.PiExponent.Collision.norm_det_le_of_entrywise_limit",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.CollisionLimit",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b964a65bd918bfcdab08dc398ab0c7dafe70cbaeaa5e47d554bf6c2d4f85d7f6",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.CollisionLimit:227",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.CollisionLimit:227"
    },
    {
      sourceName := "OAI.PiExponent.Collision.norm_det_le_of_tested_series_hasSum",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.CollisionLimit",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "53f0764e5bc758054d7367333bbd97c5d6576e2de90c9e7a98b75fe49051452d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.CollisionLimit:1303",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.CollisionLimit:1303"
    },
    {
      sourceName := "OAI.PiExponent.Collision.sum_choose_multiplicity_le_sum_degree",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.CollisionCombinatorics",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ebe9cb9082a1207744641a2369bc863800039034ffeea7361a50681e3f0ad64f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.CollisionCombinatorics:1666",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.CollisionCombinatorics:1666"
    },
    {
      sourceName := "OAI.PiExponent.Collision.sum_choose_multiplicity_le_sum_degree_univ",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.CollisionCombinatorics",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "97e177a8ab7da9cb5c46e7b4e34acd138b74ef609ac4fa56acf2cbb8e2512cdd",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.CollisionCombinatorics:2608",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.CollisionCombinatorics:2608"
    },
    {
      sourceName := "OAI.PiExponent.Collision.sum_multiplicity",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.CollisionCombinatorics",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e7849c4f4bd8ca067c7bcc46d4fc86963f3cbe292555cfbc791b9c028c88c0e7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.CollisionCombinatorics:1278",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.CollisionCombinatorics:1278"
    },
    {
      sourceName := "OAI.PiExponent.Collision.sum_multiplicity_eq_card_filter",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.CollisionCombinatorics",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "00fa76db553bd781adca9342694c9c169a2b1dbd20c7ce8d48c24df69b831a2d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.CollisionCombinatorics:5106",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.CollisionCombinatorics:5106"
    },
    {
      sourceName := "OAI.PiExponent.Collision.sum_multiplicity_univ",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.CollisionCombinatorics",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b7b95f2423e0ca9c8e904a60311f876b2221dc944b9950dc98ab51fed79063b0",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.CollisionCombinatorics:3033",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.CollisionCombinatorics:3033"
    },
    {
      sourceName := "OAI.PiExponent.Collision.sum_pow_degree_assignments_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.CollisionGeometricSum",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7c946c910f2f451d4aca00e12c88b6ace9f05aa04a6d246e1c6b2b546e142936",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.CollisionGeometricSum:480",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.CollisionGeometricSum:480"
    },
    {
      sourceName := "OAI.PiExponent.Collision.sum_pow_degree_assignments_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.CollisionGeometricSum",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0b1c174c1a2ba1065241ae633359bf373122e0b5f74e0d2e75d09a3b9121176e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.CollisionGeometricSum:847",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.CollisionGeometricSum:847"
    },
    {
      sourceName := "OAI.PiExponent.Collision.sum_pow_fin_le_inv_one_sub",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.CollisionGeometricSum",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e37030a9a36b2104936e8befa9e4582298f4e8890f7e175a1c21c0308645e155",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.CollisionGeometricSum:149",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.CollisionGeometricSum:149"
    },
    {
      sourceName := "OAI.PiExponent.Collision.sum_sq_le_card_mul_sum_sq",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.CollisionOccupancy",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f19823b4b87c74a29aea1bc5ff9580fd99291327e98cdac83af2b7351b497bb7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.CollisionOccupancy:157",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.CollisionOccupancy:157"
    },
    {
      sourceName := "OAI.PiExponent.Collision.sum_sq_le_card_mul_total_sq",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.CollisionOccupancy",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dff7a68ae5a21c34cb70100973fec013e832e568ad85022fbfb785f1aa2959ca",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.CollisionOccupancy:378",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.CollisionOccupancy:378"
    },
    {
      sourceName := "OAI.PiExponent.Collision.sum_sq_le_card_mul_univ_sq",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.CollisionOccupancy",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bd693bd4a5a7590152af5975c2c68e6872768937d05146f05c93777c59cb4656",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.CollisionOccupancy:1816",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.CollisionOccupancy:1816"
    },
    {
      sourceName := "OAI.PiExponent.Collision.sum_weight_ge_of_low_count_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.CollisionCombinatorics",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a807d9f19aeab422b7d9b15208ea3ebc15f311ac941216e59bfab3d72674a10e",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.CollisionCombinatorics:6196",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.CollisionCombinatorics:6196"
    },
    {
      sourceName := "OAI.PiExponent.Collision.twice_collision_count_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.CollisionExponential",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d3417cf915d29d15bbbc8b0f3eaa664b282aafa4e15008144e3369d264bd1e3c",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.CollisionExponential:1031",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.CollisionExponential:1031"
    },
    {
      sourceName := "OAI.PiExponent.CommutingTaylor.coeff_residueTaylorFin",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b8cf737ba4cde55d841491d290cb05b6d1e04a58e22f8f0e31e10a05208d3b33",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:7334",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:7334"
    },
    {
      sourceName := "OAI.PiExponent.CommutingTaylor.coeff_single_residueTaylorFin",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7e0cd9cd1502cab515717026f144599fd5d5ef13ba8d8ee9c51cb59f55780a00",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:7959",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:7959"
    },
    {
      sourceName := "OAI.PiExponent.CommutingTaylor.coeff_single_taylorHomFin",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "780f9ff07b7d93d68284e935b84fc1bd30442d7dc23bf99173702345af40f64a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:6692",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:6692"
    },
    {
      sourceName := "OAI.PiExponent.CommutingTaylor.coeff_taylorHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1bc5c9531bfbe1a93e5593b304186a9917bf72c76577f0758c71f1af46c1a698",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:3634",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:3634"
    },
    {
      sourceName := "OAI.PiExponent.CommutingTaylor.coeff_taylorHomFin",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e06f2b94169155c7d55d99c4a4109778954458b2dc07d9b5f48d951a739be476",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:4565",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:4565"
    },
    {
      sourceName := "OAI.PiExponent.CommutingTaylor.coeff_taylorSeries",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b60fcb2412b6d8d8c35727eaa25b3d97fca937f78e5a8eb2c7eb11d012ac9a80",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:2452",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:2452"
    },
    {
      sourceName := "OAI.PiExponent.CommutingTaylor.coeff_zero_residueTaylorFin",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e356114fb6cf15595b394c175a8df75e8b772f86d6ad774b289f01168d71faba",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:7715",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:7715"
    },
    {
      sourceName := "OAI.PiExponent.CommutingTaylor.coeff_zero_taylorHomFin",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "603cdb3adc0a7f7eb9d17955d55da1c466ad8022e7dbf86bd3a2da1a6a293e3d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:6507",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:6507"
    },
    {
      sourceName := "OAI.PiExponent.CommutingTaylor.constantCoeff_residueTaylorFin",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b829bd380ba88ff59568b070d95876ae29d5295f62a833a406ca0c8a48a2b4b7",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:8242",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:8242"
    },
    {
      sourceName := "OAI.PiExponent.CommutingTaylor.iter",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "86a0474915dafe9177965d3fad6cef1859ce8338e435dabb7562c8225883984c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:203",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:203"
    },
    {
      sourceName := "OAI.PiExponent.CommutingTaylor.iter_mul",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4eb12d2ef61d00d8e33518f9616d0da88ad8daf459c7a7d998b17200e650ebd5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:942",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:942"
    },
    {
      sourceName := "OAI.PiExponent.CommutingTaylor.iter_succ",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5399914e670a8c53616aed49ee076814c7b75f179d07a2f7926f02911821e124",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:373",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:373"
    },
    {
      sourceName := "OAI.PiExponent.CommutingTaylor.mixedIter",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9cd2e63f26c9bed8d2719c990af023cd1344378884ef57b397d29a6bbde004a6",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:4056",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:4056"
    },
    {
      sourceName := "OAI.PiExponent.CommutingTaylor.mixedIter_single",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2ffcbadd7c34bfebb23deb000a5421f6d72579dbd05e2bcc221aae446896ab18",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:6058",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:6058"
    },
    {
      sourceName := "OAI.PiExponent.CommutingTaylor.mixedIter_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "611d11e1d032cdb0f40aac87d001a3f82d0a351fbaab39e591d0e4cf0a1eabf6",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:5768",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:5768"
    },
    {
      sourceName := "OAI.PiExponent.CommutingTaylor.residueTaylorFin",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "28774f2bcba721aee3f431941a58880d96a6a5b4931a6da4ebae2123bb7fc4df",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:7126",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:7126"
    },
    {
      sourceName := "OAI.PiExponent.CommutingTaylor.taylorHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0837850797181723a656951708a7be5a9c94631470c7e309e07d74390a2dad3e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:3138",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:3138"
    },
    {
      sourceName := "OAI.PiExponent.CommutingTaylor.taylorHomFin",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b4a41fb9433f5b938abc505ce532c5328e7154eeff050b9cde1a51ab4e1084c4",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:4278",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:4278"
    },
    {
      sourceName := "OAI.PiExponent.CommutingTaylor.taylorSeries",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b6982a73f33321ba1a742bb266685d58051ad087b0abbea6f845cffed0c48d0a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:2312",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:2312"
    },
    {
      sourceName := "OAI.PiExponent.CommutingTaylor.taylorSeries_mul",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6291d146d0d86b15f80d79715ecb144e54967a47fceabd93c7784dafeb3bb975",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:2662",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:2662"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetIdeal.closedModule_isFinitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetIdealCoherent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "acd6a26a6df8c6cd6daa74e8f5cf8650cf423959fc94a47488906e2cb1a51dc8",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetIdealCoherent:403",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetIdealCoherent:403"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetIdeal.extend",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "af49d6505e30d2f8d68d4e69c79f450a41821edbd5ba40a6b52f06803e401e6c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetIdeal:374",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetIdeal:374"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetIdeal.image_support_isClosed",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e8cfc3cc7df904f17f67448d7256711244649562101adacc8f573ae707d9c4cb",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetIdeal:1319",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetIdeal:1319"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetIdeal.restrict_eq_top_of_disjoint",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0a713148b4a17e5ab08db141d8bcf93bee0ae1e902e81ed920e44f0cb95fa558",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetIdeal:2509",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetIdeal:2509"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetIdeal.restrict_extend",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "408582dedf0b447aa6d90f5bbe78605488fc729868981c3f04f137b0e2bc89a0",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetIdeal:455",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetIdeal:455"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetIdeal.section_isClosedImmersion",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e6e4d22c1acb07091da4877b4b0eb01a9299d0209aa27d3ccefef9b81f71832d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetIdeal:1069",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetIdeal:1069"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetIdeal.support_extend",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bb9ff09f857f432b26f373149cbd46eaccea66e6348a28dd53025f7bc6521ca9",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetIdeal:2011",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetIdeal:2011"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetPolynomial.aeval_coordinates",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dfa550ce5c2e4be638cd85396c64dbe0dd4ce50d02d387894686de8d3cb5bb67",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:8765",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:8765"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetPolynomial.center",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7cfed9d6477f0f01f90fb1c7e3f68c25c612d50c918bbcf50babfb9a5b98c8df",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:394",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:394"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetPolynomial.centerPoint",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d32b879251e433548dcc7d3a28e9053b3c1f5441718bde68330e83ed2ce3785b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:3379",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:3379"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetPolynomial.coordinates",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fe36040af5ba2097bbb44f2850005a74db8b420e6182ce010b3318c7fb082e49",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:461",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:461"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetPolynomial.eval_center_inverse",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7d4a342b7baef8908421cdbe1050140d6f5cf07dc7564ab2760de86a090e5d0c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:806",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:806"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetPolynomial.formalJet_mem_weighted_of_mem_pow",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ae9986e84527ccf880c739c37b89d2222f521c9e3bf9b0342853c5eb1f94d669",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:7301",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:7301"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetPolynomial.logPolynomials",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a73e6c015b35567e32b71f6943332785d659ca67c84aeb4f95c617d95d69e5e1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:4958",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:4958"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetPolynomial.logPolynomials_eval_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2633dacd61a36d0e558c865858724571bbaa239da6c9f4a3490ebe5cb1e22cdc",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:5088",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:5088"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetPolynomial.map_powerIdeal_aeval",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "83fb18019015e23ad8540f1c5f8182ccb6f1d9da9de64f0c87f343f7f067db15",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:9459",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:9459"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetPolynomial.map_powerIdeal_pow_truncatedFormalJet",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eb3cbbb74e400e6c7397d578dad1611dd4c18ff2814e00c4e73a06cf04b2d5ea",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:6330",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:6330"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetPolynomial.map_powerIdeal_truncatedFormalJet",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8fbde67ff288fa7fd25df7d4ecf6f5a7815d5c7fb5d6f5d27f64df500862cb7f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:5745",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:5745"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetPolynomial.powerIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "53d75f4bb1fd9cca48490ec83495438c3757741a51a6f3d56dab5e595645e824",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:611",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:611"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetPolynomial.radical_powerIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "12881a76af2dc64504cbc4bb851719436f696c2549464360ea496be26cd3090b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:2483",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:2483"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetPolynomial.span_coordinates",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4148041017953b9a2040d5d7e31fafb93cd0bef8d92cb4a4082294433b1eefcd",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:1379",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:1379"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetPolynomial.truncatedFormalJet_coordinates",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1c9a33ecc7129dbd1c6b1a6d220a94072207221072635e4d69e10a5a05605e8f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:5329",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:5329"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetPolynomial.truncatedFormalJet_mem_weighted_of_mem_pow",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f4ab882f2e4960a3484457956bd4d6b220962e305af580a836cf0ec94eb50382",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:6695",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:6695"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetPolynomial.zeroLocus_finset_prod_powerIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "444f50a5e0e8badd11251b4c13f4476089bd61edca1bdadc4872e1fecb1e9d90",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:3892",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:3892"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetPolynomial.zeroLocus_powerIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1d97de20785dcba1380eaaab86abe26b7b162ccb5e92fcb5431b049391542ad1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:3525",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:3525"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetPolynomial.zeroLocus_prod_powerIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "13c86cf0f823a5315bdb07c0cf34ec3dcd7a40687efceb9a2fb167b498dfae54",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:4521",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:4521"
    },
    {
      sourceName := "OAI.PiExponent.CompactLogJetIdeal.affineIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a95ea5b78d261709f278acb3cf80f0055a91a7863e2d5a80fa9bcc6c73662668",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:2268",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:2268"
    },
    {
      sourceName := "OAI.PiExponent.CompactLogJetIdeal.affineSpace",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6a989e856438321d1508e4f7f076cfb1fa5dee6a73079e9777a4eced92df3029",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:453",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:453"
    },
    {
      sourceName := "OAI.PiExponent.CompactLogJetIdeal.base",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d2c92a9bac51cee435c5a537a554e81b4e72e2e897cef63b90fcfc80832362cf",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:536",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:536"
    },
    {
      sourceName := "OAI.PiExponent.CompactLogJetIdeal.compactIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "93d4277a9a02697ea68cf9a4e448af1ad9f792c43cb97addc1e9a6de5c6e9728",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:3157",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:3157"
    },
    {
      sourceName := "OAI.PiExponent.CompactLogJetIdeal.coordinateRing",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6a30a7f3d3d62c8d4a9bde18f0d8e0a1120a18361cf5549ba85200f8284f5925",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:388",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:388"
    },
    {
      sourceName := "OAI.PiExponent.CompactLogJetIdeal.point",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "07665ac7c7b9c6fea38bad1bc002dde54ff71def8b97b6b80e84faa3be6d81bd",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:715",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:715"
    },
    {
      sourceName := "OAI.PiExponent.CompactLogJetIdeal.point_section",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aef13bbc5086c619d3f70dd0d1f36250d0fed46d8308f9113de1444d10755639",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:850",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:850"
    },
    {
      sourceName := "OAI.PiExponent.CompactLogJetIdeal.polynomialIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ac584cc8cecb2f833caa4725654d78d6e9d4eb2fa0d204ef2c5f7320b5d16c74",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:2068",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:2068"
    },
    {
      sourceName := "OAI.PiExponent.CompactLogJetIdeal.polynomialIdeal_pow_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "221f09dfc55ff907d03a96a61e10fa6153dce76e681f5f5d6dcc96296bd52e10",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:4790",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:4790"
    },
    {
      sourceName := "OAI.PiExponent.CompactLogJetIdeal.range_point",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "67c0a3cb62da53870f9a91e59a1a356e0b24669637ff8f24056b5e9b1b34ffb4",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:1230",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:1230"
    },
    {
      sourceName := "OAI.PiExponent.CompactLogJetIdeal.restrict_compactIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2077b7de38d754485845489accaed5b48dae3da61726463b4c9ec43464291575",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:3390",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:3390"
    },
    {
      sourceName := "OAI.PiExponent.CompactLogJetIdeal.structureMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4fd57724e7ba40d13b3e420380af33f1fefbdf7168da112f720431fdc194acd7",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:589",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:589"
    },
    {
      sourceName := "OAI.PiExponent.CompactLogJetIdeal.support_affineIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cf3cf53d926cc268069b5e403d84949712354c057aaba0c7c9ab33a6ec2a6796",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:2492",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:2492"
    },
    {
      sourceName := "OAI.PiExponent.CompactLogJetIdeal.support_compactIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c420c9ed44768d4a0ec2f74e2493d0ad1145719aa1503442833b10aa7828961c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:3703",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:3703"
    },
    {
      sourceName := "OAI.PiExponent.CompactLogJetIdeal.support_specIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7ae92155243e5e71cc3d3c9cf193b02a81a708ae76e143481049c788288edb47",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:1591",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:1591"
    },
    {
      sourceName := "OAI.PiExponent.CompositePullbackCoefficient.exists_frame",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CompositePullbackCoefficient",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "75e9fdc168577faa863ba685cd36cd3db3ecf59d1d1438f712add420bfb988d0",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CompositePullbackCoefficient:271",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CompositePullbackCoefficient:271"
    },
    {
      sourceName := "OAI.PiExponent.CompositePullbackFrame.exists_frame",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CompositePullbackFrame",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9fafc7e65cc2fc14244d05df68cb11e7f5d6b57bcf812254e7f4d396aefefec5",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CompositePullbackFrame:1057",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CompositePullbackFrame:1057"
    },
    {
      sourceName := "OAI.PiExponent.CompositePullbackFrame.exists_power_frame",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CompositePullbackFrame",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6b9e3f127d33ac5a960f8a61ef552001f651115e22ca878cacabca2bbcd5d7e0",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CompositePullbackFrame:3210",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CompositePullbackFrame:3210"
    },
    {
      sourceName := "OAI.PiExponent.ConstantPullbackDegree.constantPullbackIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ConstantPullbackDegree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bfa16b3a44d5c8dc632ed3d3e7d91182f513d94b62092f0262197ef69ff5141b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ConstantPullbackDegree:1208",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ConstantPullbackDegree:1208"
    },
    {
      sourceName := "OAI.PiExponent.ConstantPullbackDegree.curveDegree_eq_zero_of_contracted",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ConstantPullbackDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9a77cb2c5a3a8659a43c4eb702c76b2886f53f953b0f5aa4b77f94fd6fac325e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ConstantPullbackDegree:2306",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ConstantPullbackDegree:2306"
    },
    {
      sourceName := "OAI.PiExponent.ConstantPullbackDegree.euler_difference_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ConstantPullbackDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "11e09a17500e5e1e38e579cb1549c9d73c19dedbb7ae4787c5349d1a2cb644ef",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ConstantPullbackDegree:1577",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ConstantPullbackDegree:1577"
    },
    {
      sourceName := "OAI.PiExponent.ConstantPullbackDegree.pullbackFrame_of_range_subset",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ConstantPullbackDegree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "45630a9b44806598147009db8bd93e930f567819401764a8e539f7542e2abfab",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ConstantPullbackDegree:440",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ConstantPullbackDegree:440"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateContactBound.X_mem_rationalWeightedIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateContactBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2d2d6baba1ff8289b6dc9495dadd28f17d199b0936b279db26d07189b98882bf",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateContactBound:1254",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateContactBound:1254"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateContactBound.coordinate_contact_sum_le",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateContactBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4a015b240d00c96b697506f946006c309f4492fc10a1d2fb3b62445a286e3222",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateContactBound:1979",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateContactBound:1979"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateContactBound.ordinary_formalJet_X_sub_C",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateContactBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "070d040621f660d27cb4a998bc56a2f9d6ffeb6339c41a3ae43625d38cf69167",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateContactBound:848",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateContactBound:848"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateContactBound.ordinary_formalJet_coordinate_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateContactBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b7cf4a846ff1b9bc50a8ecd309a4111539656ae69a0a5bc57c03509d746961d1",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateContactBound:1620",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateContactBound:1620"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateContactBound.supportBound_X_sub_C",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateContactBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1dc202ed4545ac4b1a6b19d70f3ce09ae54f78a4ba9399cf854db73de5f7a298",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateContactBound:416",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateContactBound:416"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateFiniteSlice.complementary_transcendenceBasis",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c0dd2062d119bc95d64e868f30e5ff2e1eecce37839c8fc0388a7b3c232c0e90",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice:3397",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice:3397"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateFiniteSlice.coordinateEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b217190cbc75ad31d58f293a8458846fde24dc7f0b5b151f701c508d1208bfe5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice:376",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice:376"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateFiniteSlice.coordinateRenaming",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "da9e4b51e0ad6739102b2088175e0bf48a7fb4dc57b38327db311850e25beecc",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice:839",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice:839"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateFiniteSlice.coordinateRenaming_X_inl",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4cbc00727c411ef8d0e9bc6a579db1e2a22455fa83d3e41ea0899d96490910d4",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice:1021",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice:1021"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateFiniteSlice.coordinateRenaming_X_inr",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e1e4c5040231af93f3bf64d374fad9274e17f548c4b3ecdf06f0bf662f99d60c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice:1385",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice:1385"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateFiniteSlice.enumeratedSliceMap_X_inl",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1defca5146a92379bb5ca91560e8ab5beecace467add7f5a3e8fc3608a7f76f7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice:4911",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice:4911"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateFiniteSlice.enumeratedSliceMap_X_inr",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "90976358e9a376bc96673b8be4f15c059bdd38358792210e79ff1ec129338365",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice:5374",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice:5374"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateFiniteSlice.residueCoordinates",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "583ea0b9e140321076963b5a794ba1621d80986455164850b7f9a53919479604",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice:4583",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice:4583"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateFiniteSlice.residueEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f9e8db2d919b0576c92b100cf25b59a99ab03255e3a73edef83aee6e6f8ae1d3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice:2096",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice:2096"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateFiniteSlice.residueEquiv_coordinate_inl",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a39b98a964b3c4faf3db00d159048b8f1edb74ab37fbadddd0787f4d4f6e1953",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice:2290",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice:2290"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateFiniteSlice.residueEquiv_coordinate_inr",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e2a9947733af99bcab25f7b8b9f333a353b97f225cc35dae99b2486cef175024",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice:2863",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice:2863"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateFiniteSlice.residueEquiv_symm_coordinate_inl",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d37364dfd41f448cc0b5162bf18652343a683ff8816c0c5cb5cd206d62e6d1d7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice:5810",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice:5810"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateFiniteSlice.residueEquiv_symm_coordinate_inr",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1040307cb58ee5d590fe1410299c15a111154bc73c6ac0861d693f036a775df8",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice:6249",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice:6249"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateFiniteSlice.slicePoint",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "65d86fb1a188143b714a5fe2676d63e9dc96ac39459da68a324b66c32769aba3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice:4750",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice:4750"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateFiniteSlice.splitPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "640916fe1b4263a30da67e46ed6e26b2295642305cdf2aab53bbfa9e80d41780",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice:1735",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice:1735"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateFiniteSlice.splitPrime_isPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e9b504dd83e6ad4b40f53560cc5e1b3d25c69d0d7e83e6659d2d65dce111c765",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice:1920",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice:1920"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateFiniteSlice.splitPrime_mem_minimalPrimes",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ef1951fd61756f7216264d6779eaa469e22a456a1620b0b6d2e8d2632f33e5e7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice:3947",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice:3947"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateSliceComparison.length_eq_enumeratedSlice",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoordinateSliceComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2dbfa4a63996fe720d379bb772cdc3c83d7d5591f2960a9d4e37616173bd3721",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoordinateSliceComparison:3638",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoordinateSliceComparison:3638"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateSliceComparison.length_eq_enumeratedSlice_of_normalBasis",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoordinateSliceComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fac6119e29018c43c3cae3136091f52c4bcc5deae192f4c27ba2569b6bd517f0",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoordinateSliceComparison:5939",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoordinateSliceComparison:5939"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateSliceComparison.length_eq_sliceFamily_of_normalBasis",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoordinateSliceComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5d9702f90da823eebc8b0a3ff55fe329ca5d8d32127b71b1900b33be6f666df8",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoordinateSliceComparison:7747",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoordinateSliceComparison:7747"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateSliceComparison.map_residueSlice_eq_enumeratedSliceMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoordinateSliceComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2e605e4c580f152f6480ae375fa9096646350d11d6224601f2b30b790a5a244a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoordinateSliceComparison:1076",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoordinateSliceComparison:1076"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateSliceComparison.map_slice_ideal",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoordinateSliceComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0b4811f7c4db0d297e74690b67f6c623057e7f2a0464279bbcea18d71769e839",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoordinateSliceComparison:3105",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoordinateSliceComparison:3105"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateSliceComparison.map_span_sliceFamily",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoordinateSliceComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "86b60dec895446764e85021c3627ffab4d55c487c871d523b7b6333dfbe0a52a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoordinateSliceComparison:7268",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoordinateSliceComparison:7268"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateSliceComparison.map_splitPoint_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoordinateSliceComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6a47354f4744e6c35f4e14b1b7168c35e5c77750fbba387f5741ba390ef2b4f7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoordinateSliceComparison:2759",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoordinateSliceComparison:2759"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateSliceComparison.primeLength",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoordinateSliceComparison",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7b421796e3acff08975985370ace68c6d2550160809ec7227cac948b61d53947",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoordinateSliceComparison:512",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoordinateSliceComparison:512"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateSliceComparison.sliceFamily_mem_minimalPrimes_of_normalBasis",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoordinateSliceComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "619065309c1034edf5d7a1456249076ec55661b7a899c1f49489321828a59b89",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoordinateSliceComparison:8536",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoordinateSliceComparison:8536"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateSliceComparison.slicePoint_mem_minimalPrimes",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoordinateSliceComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "954efec6105193f201165206c40d048f85b0e62cf1a34540a6b661c631a228f8",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoordinateSliceComparison:4880",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoordinateSliceComparison:4880"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateSliceComparison.slicePoint_mem_minimalPrimes_of_normalBasis",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoordinateSliceComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9f77dd8a5876657b7196e0d7211af24c7dd2d1edfffbd9e2b4c57ff7790e562c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoordinateSliceComparison:6589",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoordinateSliceComparison:6589"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateSliceComparison.splitBasis",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoordinateSliceComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0a0a4f9ce1cda782083241333c56440e8b58623bb281b441f3363c78f2e98a1d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoordinateSliceComparison:733",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoordinateSliceComparison:733"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateSliceLength.closedPolynomialIdeal_comap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b6ff4182ae4fdea9e6a21cb1ac0aae4153a641bd716fbfe60556bc3f462e8b39",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:3276",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:3276"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateSliceLength.closedPolynomialIdeal_eq_contractedPoint",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5885010306ffa0676cd31e5d77fc36dcfe95c9e2cf1eaf84088179868ce7ff50",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:9714",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:9714"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateSliceLength.closedPolynomialIdeal_eq_ker",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b6febf025b5961e85046f9637b2b9f13f11a6eec473a386413e729ff74078988",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:2038",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:2038"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateSliceLength.closedPolynomialIdeal_mem_minimalPrimes",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ab87f8805691d496342569c8187b305905f58db7c423fb868ab1db0496cf739d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:3832",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:3832"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateSliceLength.length_eq_rationalized",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f1e8b2263d7da450c139eadb5f3e131db9d6a330c8c6bdf45504d53a4cee2dd0",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:6060",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:6060"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateSliceLength.length_eq_residueSlice",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c240ef34f00d0e02299d38ed56206fa4ee6c651d768669695407f854ae45f890",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:10126",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:10126"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateSliceLength.localizedLength",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3022d9536879846f38197724dd6460e1041f1808909f1adc634b8b4951f10252",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:562",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:562"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateSliceLength.localizedLength_congr",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b17cef9b02aef7753c2f18d974e6c866234ab8e482f8133068b02bd5705dd0ed",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:787",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:787"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateSliceLength.map_prime_eq_closedPolynomialIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e689eca3028f4ad9d065804e3297918a468c8146083fb53cb4f5c3ede7cedc9a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:2640",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:2640"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateSliceLength.map_rationalize_eq_residueSlice",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "18fcdcccbd69de0f2ce8e4de73fc569988338235f1429e73b70542136b26c31c",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:8169",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:8169"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_004.jsonl"
