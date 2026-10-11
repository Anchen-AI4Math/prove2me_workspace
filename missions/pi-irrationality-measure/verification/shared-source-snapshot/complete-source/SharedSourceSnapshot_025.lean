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
      sourceName := "OAI.PiExponent.ReesProductPowerSections.chartMorphism_opensRange",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "434083fcf299f0b5aa91a8861ae97afe1ccf89b269f261d10847cbdba40161cd",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart:1952",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart:1952"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductPowerSections.chartMorphism_projection",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a8d11119331cb577aee6c1277d896b9d267b145f01624af8e6d5f0467eea6410",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart:1454",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart:1454"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductPowerSections.chartOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "683ab706613b3e393702eb95ad874ca9074c7701a68fcbbf366a821d903fb03c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart:3035",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart:3035"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductPowerSections.exceptional_chart",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4669a01a29c60067e984e6639b210a8dab7cc447c8fb2e1007f76870cd3bf72e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart:3369",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart:3369"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductPowerSections.exists_chartMorphism",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "71408a008eb26c380af06ba70b095a7604bd313f4f6fdc4e42989f2250979b5b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart:592",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart:592"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductRestriction.chartMap_mk_homogeneous",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "af9cd49e73459ab575726e8f0cac2dccf0888151192b34fca31385bd1dc35c6d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction:1613",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction:1613"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductRestriction.chartMap_restriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ad0842745d4a54ecb9a3934c4ffbef48d859be1188830c0157de053845ec5cee",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction:3956",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction:3956"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductRestriction.chartPowerMap_restriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0ddcd4c119bd31f8d3f5a9a220819426dccbde861bcc1f3a9fd72740b020c91a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction:5484",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction:5484"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductRestriction.chartPowerRestriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4b73813da93e21c602f6be57bebcf63995656e261a4f01e75d29d1df966a27ca",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction:5104",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction:5104"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductRestriction.chartRestriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a408f28d620743fbf7b8df882c8d390828b4983fb1b0b0ce482555b1e7eff097",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction:1153",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction:1153"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductRestriction.chartRestriction_base",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "548b985b0a81124d71419d8c20b14826b1fa6f1217b8119b2405456eb58ad7be",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction:1364",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction:1364"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductRestriction.chartRestriction_power_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1ba73055da25f9ab016da2cc89060b2805274db6dbb104cfa73d18183eceaff2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction:4532",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction:4532"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductRestriction.coefficientProduct_factor",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ed88add132e083a14db7175962112792889f5b54340f0efb55d5372ae2dc2dae",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction:905",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction:905"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductRestriction.coefficientRestriction_fraction",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e11fcd24bf50c8bcb449be29cdd51a24e22734cdbfb488cac802c2174f62a4a2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction:2381",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction:2381"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductRestriction.productGenerator_factor",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "97ee7c3472319192ed6ae7647afbfeae66186df411066c94815fb3fed3217246",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction:625",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction:625"
    },
    {
      sourceName := "OAI.PiExponent.ReesProductSchemeRestriction.chartRestriction_chartMorphism",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ad217e946200dba17676bcd113a2d88c1a9a9dcbfbe092b7c53065e23af08b35",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeRestriction:521",
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
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:12676",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:12676"
    },
    {
      sourceName := "OAI.PiExponent.ReesPushdown.ordinaryPowerEquivPiece_apply_coeff",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dc38b0a3bb1d4097b92676850e7d5fdf1fc38d6587be814108cab7ea9915226b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:13741",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:13741"
    },
    {
      sourceName := "OAI.PiExponent.ReesSectionInclusion.HasFrozenValues",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesSectionInclusion",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "53f37528bb27fae776883fb7bdfc1d2c4e223b21fa31ac7c31db54391d2219a8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesSectionInclusion:2165",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesSectionInclusion:2165"
    },
    {
      sourceName := "OAI.PiExponent.ReesSectionInclusion.section_chart_inclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesSectionInclusion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "66d34482a63081c432e0899139b1c26242ff18fa5bbe9a0d48278a00a02735bb",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesSectionInclusion:2600",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesSectionInclusion:2600"
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
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:5570",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:5570"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechBase.chartFrameTyped_nonempty",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "606cee92e76d49ea6a4acc507235ba3aeda1691238470390151323d91a49ce81",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:5149",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:5149"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechBase.chartHomEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "75875eb659ccbce7b24ee19c4f123f8dbd7b73cdd231984107521407f8c17df8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:5782",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:5782"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechBase.chartHomEquiv_pieceEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "78b6f18de4e50669d962ff4d582b04f6641846773d71a34be11d143fa886969b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:6167",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:6167"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechBase.chartOpenImmersion",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1ac947098bfcb1556a84c64f03776f596dc7fbcfb81dd6b4e17886ea5b9b233d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:1456",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:1456"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechBase.cochainEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f1375d4ea530ce81a60c23551c0f6d94594c8da56a7240e5d782864ba9e60174",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:7686",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:7686"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechBase.exceptionalPower",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bd8dd6d15e21dd5fbeeb8cf8ce15e8efe3c540f2765c3689dddf446685d1535b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:2045",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:2045"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechBase.freeOpenSectionsEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "58353077c01247882d9a0eb8ddb5a3a5a4d549b12aa6f7ad371cf11ecb9cbcd7",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:2522",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:2522"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechBase.genericChartHomEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "082499df2888b5669f169467778bb44a9706a07e1f6b718ac617833194d700de",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:4290",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:4290"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechBase.iSup_opens",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "52a966d963bcba9760bb0982228a15af94803db8b2c627d85d5ab3ea23e0fde1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:8606",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:8606"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechBase.opens",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "efbb2cdfca246f5d0b9cd0b05a09ebdba4c3cb583c380c5be227e9143d5aa86a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:2125",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:2125"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechBase.tupleHomEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "17cf15b6528101873dea1c1d50cad9338ae5400e260be923480505e81b32952a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:6886",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:6886"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechBase.tupleOpen_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "82d2e2515b119817f5c5e6e92a7673ef61e3de51885b90ca2a781ada205da86d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:3723",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:3723"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechBase.tuple_isAffine",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b609fbb07942a8d71dc9c9150b9a02ab1330e0b77c5548c8274180c39b05041d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:8376",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:8376"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechBase.tuple_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "67bc0aca488bcafb23344f346795a7173916a1c26affe4c7ece0fec1740fb13f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:2210",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:2210"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechBase.tuple_nonempty",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bd9d2dc146c45c14b25569598f98569d801820e34f711dc9a529bb01b8867e02",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:2384",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:2384"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechNaturality.chartHomEquiv_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechNaturality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2a00d0373a51cad950c0eda694cd7b5fa18afeb99a437c475e264fe0212d0779",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechNaturality:2384",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechNaturality:2384"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechNaturality.cochainEquiv_differential",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechNaturality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "32f8bab70edcaf216fc448c695628c2d7ac5f7bfac6d6ee980fa4e9c8ed8a8b9",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechNaturality:5426",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechNaturality:5426"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechNaturality.tupleHomEquiv_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechNaturality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4a36a90bbfd13b1c61213aa222ea3b0228e9da52d0732b6f08201d76dc339f6f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechNaturality:3747",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechNaturality:3747"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechRecovery.cyclesEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f4eea99d95a1f399fdc940f988f41fbe960e700d1464d42621a08cd10e68cb1e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:3027",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:3027"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechRecovery.eventually_recovery_and_cohomology",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "927884fb7bee8763ac87003605a8f118f1fc8d54184116d3cf2eb96c50b1d536",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:9554",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:9554"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechRecovery.eventually_recovery_and_primitives",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "75edb77af119f9f044694dcd446f55232e926dca5e2e522c3e668433d69c4e0b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:7459",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:7459"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechRecovery.globalCyclesEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d6f3e7d74258a4da190f5364cd4879613f8165bb8feb85f57af7ce61b015d4c0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:4089",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:4089"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechRecovery.gradedCycles",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "780a8a42c2798847ca67eb513b95e5eb0b79d2a873297bdf047e6aa70687886e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:1920",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:1920"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechRecovery.gradedCyclesAddZero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f3c274838929d4881576ae1de31cc036601caccd7d02fd6f5f749c25959651c7",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:2721",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:2721"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechRecovery.gradedCyclesAddZeroClass",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a2ad91367aa1e39c656ceed938ea9cfaf0b93a2c07cd83fdd4ea6d9c1192daf0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:2864",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:2864"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechRecovery.gradedCyclesGroup",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f533b169c4e9b55282807b633f9e6a1784b1a741a3e69119536fef8290445fff",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:2348",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:2348"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechRecovery.groupAddZero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "23d65aa26fd71eaed01751581bac9c34058c1cd37c925322f4f99211dc217daf",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:2463",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:2463"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechRecovery.groupAddZeroClass",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bc91ce8645c4232bfa9be9d4c6dec293bee91cc2e8640e541a401b80bd78ee19",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:2587",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:2587"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechRecovery.ordinaryAugmentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1a63459642d13a1d10328946c40429a1397675875321701a44d2aa2e18f53a34",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:3648",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:3648"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechRecovery.ordinaryGlobalSection",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "78ae4d3c2ce32d9011c0a3e705bd652ce5146dae0527b6d32af511977335db85",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:4913",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:4913"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechRecovery.ordinaryGlobalSection_inclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesSheafCanonicalValue",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7d271f6671240aea3c4cf099d0a8da53a6295220b68362757239ace2ba1634f4",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesSheafCanonicalValue:1881",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesSheafCanonicalValue:1881"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechRecovery.ordinarySectionHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "46030eb04e9a2f2c4197e268981b23f621a1853cf49dc37453fa9f1b43bc600d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:4641",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:4641"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechRecovery.ordinarySectionHom_chartValue",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8f2120f82d01b166dcfc8af27f7e4c5321e4e21d6305b6d293174d5245e00c14",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:6066",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:6066"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechRecovery.ordinarySectionHom_frozenChartValue",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "32f9ca7c1d7f3910e2ccb16b3e81b336c417ae956333a5c81dbe7f85f5ac442c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:6696",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:6696"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechRecovery.ordinarySectionHom_restriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "57a898a99ba8af25ebec9870be5b81d32dc825beb0d37c2a63611c7c9bc61a81",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:5178",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:5178"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.RowChoices",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "98def1acefd799e100d4889e9d9f1fa635991d2726dd3f4bfa52ea6ce4936bfb",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:10668",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:10668"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.card_bounded_indices_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "73cb81d02694b277d117e41b91f47b713d1ce01e963afd93becd2f82a6463dfe",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:10317",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:10317"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.card_rowChoices_box_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ceeddebe0bc27d837f9848203ca8f96054932c7a1a6362ac13a069b7d177520b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:11417",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:11417"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.card_rowChoices_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f57fcbc091ae0c87aecf142032a3dda354cb84ad7715019bd3049b334175206e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:10812",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:10812"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.choose_product_le_four_pow",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ddaf5e9d3c7fa75682903fcb03aa2b2a92d0919c82d27578eec3fb2808388c31",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:9566",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:9566"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.coeff_shift",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d3ff0610fa55d3dcaffe64030fdd39ab2a0405eaf067c1ab20bd674d996d5948",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:1139",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:1139"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.coeff_shiftCoefficient_error_tail",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e6cb25d2be317ceecf92db7640f977a66fb08a62bb5e1e8b0e041bfe0b072d48",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:8107",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:8107"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.coeff_shift_over",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "feac1d721041898881d571c9875991c709f73e0249b9d1984fca5ee2aa7ac0ea",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:1574",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:1574"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.coeff_tail_of_lt",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "56bee06e4869dbcf27ce5d9a747223b2e2839fb0f40974431835782eb9c3cc65",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:12973",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:12973"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.coefficient_error_tail",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4f5cf94edc9ae0d11e1f60f1ab2dbd491514b257b93a7b5bd3f473c9b1d7f028",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:6569",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:6569"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.exact_row_identity",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "224cca6bcc94a300becb7261ef70e1620b6a7b610baab05057175732312616ad",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:8789",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:8789"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.multiIndex",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b3aac1c3795f11100810fae4a6d0bfd4e6c7efc3cbbe706511f311ab771405c9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:2296",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:2296"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.multiIndex_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c820b4360b0e8d00e40d8222918477c6530194930ff925a074714056d161c597",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:2396",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:2396"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.multi_choose_product_le_four_pow",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "66f094b7cc7fe3b046abe5cf4157d2f32878d9ffe75c8930d6bab0aa55fd4ad5",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:9975",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:9975"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.norm_rowScalar_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "41f0aa90b32f99b86d47d86f1b4edee20b54ef0a957adf5fdf4ef2294fdcd2ab",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:11982",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:11982"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.order_tail",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3fe1a2d88b44fad3201eef23b8e962318c1823e11647b8143360790cf055f429",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:13146",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:13146"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.order_tail_prod",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "11e169f36192b64b48154ed6149b56bcdf758a93c25d8351ebaa4af56833eb12",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:13326",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:13326"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.product_add_expansion",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3da2e53327888aa5499fb43aaa9095254cc2d6e03537f66067eea5a92abfb9fc",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:5183",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:5183"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.rowScalar",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "25e6fd5a6123637169e5cbf6ce748019c0a0e5bae583742016ef7ce609548f84",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:7272",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:7272"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.rowScalar_ne_zero_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2e205293fa764385224def069af4f92be9bf3282ec4088956f12e7d9ad6a4e18",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:7597",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:7597"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.row_coefficient_identity",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a7ab7e282e5ef672bc3b29f7c81553cfc33ed829fbc584e832499b8c128de709",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:5958",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:5958"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.shift",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f7078d28ae849daef40dc4a03ab4592117179dd459496aa8eeb2dbd42b4cd106",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:222",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:222"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.shiftCoefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c3966b6cd9032c86c56f70ab19acc6bf3d3c0c8a08f1a44f609b7caccc3bb5f2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:1019",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:1019"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.shiftCoefficient_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3cd7188363c947a1ed33d6f8e58710b3e7481b4de0fd7e7e9cb6e64df316c17b",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:3766",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:3766"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.shift_C",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "83c92fa3b9aded9cda835b89f001c3cd98eada41343bb782fd11310e4c59668e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:352",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:352"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.shift_X",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4620d65b0b042222649cc8125ecf38504b5e2a8940c732b16d51b60036927b86",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:446",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:446"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.shift_monomial_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ba2d43d79652ded0c7412096358354b21e5f5f5506923adb7859913aebd19793",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:3500",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:3500"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.shifted_X_pow",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "96caa63129aa32a4292905db84200c2e679999cad15955051dfe14c684955b4a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:2534",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:2534"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.shifted_product_expansion",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "67570c22c7b300f23abea8f4bbe57becc5c3f7b67f02f63d86589ab4e62225d6",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:2894",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:2894"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.tail",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "864a826c6d1078095926e1c88bdca809500d27fb0702b18adfd18fc633157061",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:12851",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:12851"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.tail_budget_nat",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c444266bc677e5921afd0628622536057025a81ec7d8f863f3882dde4f74e561",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:14040",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:14040"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.tail_weight_budget",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ea64ea8276585ae8a4d58da51e0a26bbd5b8a78d150f4f32588bcd28406a3107",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:14353",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:14353"
    },
    {
      sourceName := "OAI.PiExponent.SectionImageIdeal.affine_map_imageIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "383099ae8d3cb6d84c04c14dd7ad17a5b6054db58884c782d8d60758760ffd73",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal:831",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal:831"
    },
    {
      sourceName := "OAI.PiExponent.SectionImageIdeal.imageIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ce47c3772147018bc7d8fe3211cee6fab85b3cefa00cd30f77d75196d408747e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal:362",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal:362"
    },
    {
      sourceName := "OAI.PiExponent.SectionImageIdeal.imageIdealSheaf",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e66461d353e21057008478068e6ec163c0b7d0614e144f70ddc25e96a9b9c82b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal:4891",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal:4891"
    },
    {
      sourceName := "OAI.PiExponent.SectionImageIdeal.imageIdealSheaf_on_frame",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6be849641ae52d679efbc86c9be19c55b5f801d79efbe3e43d247d41660180fb",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal:6431",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal:6431"
    },
    {
      sourceName := "OAI.PiExponent.SectionImageIdeal.imageIdeal_map_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "195712e53abd127d8a70e567ed5dfe6a3f872f88f3c0df9fc679c136d6d2fae8",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal:6106",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal:6106"
    },
    {
      sourceName := "OAI.PiExponent.SectionImageIdeal.imageIdeal_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a296eaae4b8d38f01710e54f9392d5ffdaffb1f9c54b6128108a21a03bf438eb",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal:2040",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal:2040"
    },
    {
      sourceName := "OAI.PiExponent.SectionImageIdeal.imageIdeal_top_of_frame",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f5540f2d165bef6d3ee226e92ea249d86f078c793ac1c68d864b6d4d4fd84ee8",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal:5262",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal:5262"
    },
    {
      sourceName := "OAI.PiExponent.SectionImageIdeal.map_imageIdeal_affine_image",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dc824d3ec0c972128e24f282d198965d93f0081784f900cc73b6eecf128a4747",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal:3157",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal:3157"
    },
    {
      sourceName := "OAI.PiExponent.SectionImageIdeal.map_imageIdeal_basicOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e9e4b57ba9a9db19e2a4bd7898bee4cff10c737fb2f58e30caa6640c440f5b5d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal:4134",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal:4134"
    },
    {
      sourceName := "OAI.PiExponent.SectionImageIdeal.map_imageIdeal_le",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7ed12fa8cdf788b7dcfb647dcf680a8872ddd13106a60a61931b50a8074f559a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal:476",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal:476"
    },
    {
      sourceName := "OAI.PiExponent.SectionImageSupport.imageIdealSheaf_support",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionImageSupport",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "89fc8576697e5eea8358a502f1efa3b6c78a4a10a5082e599566095b23a4a60b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionImageSupport:1861",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionImageSupport:1861"
    },
    {
      sourceName := "OAI.PiExponent.SectionImageSupport.isoOpen_preimage_on_frame",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionImageSupport",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cd8eb6130faa90411b5efa57ddac95bcf0221b7571c10a47ddc573ecd2a89f28",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionImageSupport:568",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionImageSupport:568"
    },
    {
      sourceName := "OAI.PiExponent.SectionImageSupport.preimage_basicOpen_topIso_hom",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionImageSupport",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dc3e47e5329993d1f586029b654bef012b5243106df1bb653e45096e315fd958",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionImageSupport:1588",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionImageSupport:1588"
    },
    {
      sourceName := "OAI.PiExponent.SectionOrderDivisor.CurvePoint",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ed2ddc2240a4dbcdba02e31327eece24780f9da4a0b08fbdb8a62653dafa1fff",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor:350",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor:350"
    },
    {
      sourceName := "OAI.PiExponent.SectionOrderDivisor.divisor",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e47f1a9b419a06a9e38ded61141fa70c55d8b3e98c44a3054776e9b640a1d5ae",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor:3102",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor:3102"
    },
    {
      sourceName := "OAI.PiExponent.SectionOrderDivisor.divisor_degree_eq_euler_difference",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "50a403bc1c216d4d639b0389e8abef2558f59236ade71d91bc5f0f051a86151d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor:3860",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor:3860"
    },
    {
      sourceName := "OAI.PiExponent.SectionOrderDivisor.mem_zero_support_iff_not_isUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d2644e696db874b962400851e880e49555003b06d9b4585b161942b3490614c3",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor:438",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor:438"
    },
    {
      sourceName := "OAI.PiExponent.SectionOrderDivisor.orderAt",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5f51c566c4c82a4811e9d3a452a3cc60d5a5ab5edcc59ab94177ecd29e7e10ad",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor:947",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor:947"
    },
    {
      sourceName := "OAI.PiExponent.SectionOrderDivisor.orderAt_eq_zero_of_not_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "61a25bd687aff8a6d66765a258f52547d2d3af7b1dc8275529cab4060c112245",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor:1252",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor:1252"
    },
    {
      sourceName := "OAI.PiExponent.SectionOrderDivisor.orderAt_finite_support",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6ea9ec3a7c8228c598ae0502eac1698cf25759d18d2675eb62efa4d39a2cac8e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor:2178",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor:2178"
    },
    {
      sourceName := "OAI.PiExponent.SectionOrderDivisor.zeroPointEmbedding",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e32864c8f018ed6b4bb65f216fd3032c9ddad7c7dbf86b341a6ae8f81add76a2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor:1778",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor:1778"
    },
    {
      sourceName := "OAI.PiExponent.SectionZeroIdeal.dualSection_isoOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionZeroSupport",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e8257f12aad24ba723de9816c050a672c116f80863912f6ddece77ce9d5a530f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionZeroSupport:424",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionZeroSupport:424"
    },
    {
      sourceName := "OAI.PiExponent.SectionZeroIdeal.zeroIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionZeroIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f0c9501a66bac9b887d8a340a2f35a5e6d18d332ab7d1822e84f9121eb2e94b9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionZeroIdeal:634",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionZeroIdeal:634"
    },
    {
      sourceName := "OAI.PiExponent.SectionZeroIdeal.zeroIdeal_ne_bot",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionZeroIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "180e15dd0238fcdfcc619976fb6d9a7261b41796f500356dffd696b4e00c7405",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionZeroIdeal:1753",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionZeroIdeal:1753"
    },
    {
      sourceName := "OAI.PiExponent.SectionZeroIdeal.zeroIdeal_on_frame",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionZeroIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cc9a5ecac9930c53a6313436dce123e5455468afa02854e394886104fe128ef5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionZeroIdeal:1020",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionZeroIdeal:1020"
    },
    {
      sourceName := "OAI.PiExponent.SectionZeroIdeal.zeroIdeal_support",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionZeroSupport",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5643c4f39d1c4021f219faa0265640e9821ac24fc004a7306c14dbd174ad18b0",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionZeroSupport:1035",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionZeroSupport:1035"
    },
    {
      sourceName := "OAI.PiExponent.SectionZeroStalk.intrinsic_length_eq_of_ringEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "47e0d21d403f7ba77a6f750b4c5670845f8d81755b6e931464768c365be149c9",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk:3564",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk:3564"
    },
    {
      sourceName := "OAI.PiExponent.SectionZeroStalk.sectionGerm",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2efde06912223d65aff4688a9b1a2116b3236a89a8b90ce636d37b1e9d3905bf",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk:2613",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk:2613"
    },
    {
      sourceName := "OAI.PiExponent.SectionZeroStalk.sectionGerm_ne_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f751f74913a245a9231400e8af5f7f703b5d464f786a7e58934224a4e60528a8",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk:3856",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk:3856"
    },
    {
      sourceName := "OAI.PiExponent.SectionZeroStalk.stalkMap_ker_eq_map_affine_ker",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6f9798fd6b1432db2e6547beca78b45fe61ec8ba6971a42a17a8c3a0bddac6c3",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk:330",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk:330"
    },
    {
      sourceName := "OAI.PiExponent.SectionZeroStalk.zeroStalkQuotientEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "62d58532b9aff8d48f315684556368c4e3a1098e2f06a0998bc9e985991f9271",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk:2900",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk:2900"
    },
    {
      sourceName := "OAI.PiExponent.SectionZeroStalk.zero_stalk_kernel",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b8f7fd5caac7806319336db73e11a9d22aa93d986d8b88491faa900e13344f02",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk:1927",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk:1927"
    },
    {
      sourceName := "OAI.PiExponent.SectionZeroStalk.zero_stalk_length_eq_order",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4bd58f1c5372b6b1670cdb864a8de892b66f4e37afd08aae222354056064d9b5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk:4672",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk:4672"
    },
    {
      sourceName := "OAI.PiExponent.SeparablePointLength.coefficientBaseChangeEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dbbaa02a6be944e93706a3f909306a46c1600a3be3bb731cff01fdfe7367e446",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:381",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:381"
    },
    {
      sourceName := "OAI.PiExponent.SeparablePointLength.coefficientExtension_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5aaf97d6aa75d915eaa985a8f438bccfee23b4543ff8f83871c18d1c51574838",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:789",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:789"
    },
    {
      sourceName := "OAI.PiExponent.SeparablePointLength.coefficientExtension_flat",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "93efadd79195a7da038f358aff6a44668ee7ffdcb79ccd30f70185ee013d8c6b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:583",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:583"
    },
    {
      sourceName := "OAI.PiExponent.SeparablePointLength.coefficientExtension_unramified",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9760378d8dc38886d05f439bcb3ec3682c747a05f7c2abc7ad0ed7d1e12cfd95",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:1007",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:1007"
    },
    {
      sourceName := "OAI.PiExponent.SeparablePointLength.contractedPoint",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "990d5ef9af63a512915c624990e33f52c9e3cbdc830296d323ebd2d69ffa9d10",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:2070",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:2070"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_025.jsonl"
