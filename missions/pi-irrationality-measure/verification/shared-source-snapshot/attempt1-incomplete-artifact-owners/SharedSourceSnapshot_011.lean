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
      sourceName := "OAI.PiExponent.GlobalSectionClearing.affineToSpecModule_quasicoherent",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "04dcff47d8c2c1deec2b4c2b5dda452bcf37354334ff5d639b211f4e9d51cd8e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:2376"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.affine_basicOpen_denominators",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9ad22136100e58e17e6e472d00f3027559f8a6632809a0997396b91f316118ce",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:5782"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.affine_basicOpen_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5a352104607c6559ae22c6e7689ed55a85e2a6f0a6abbe3ecb7207ca89fa3aab",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:8736"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.affine_immersion_zero_on",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ab149596e536a3a2c61e3841b3e536b575b1e990f3affbfc94348740b5057bfa",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:9900"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.affine_openRestriction_localize",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4c488ded6012c4a9096fa5f79dda8a1c3793ad945bb2b99387e1c6a8107cdb2c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:4660"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.affine_open_section_extends",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bce1af34a5fe46a24d09202e2047b09b3b33e50691373ae1ec0ff6b439082662",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:15292"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.affine_sections_localize",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "acaa1bb01e9502bbe8abf78f52ed9d6202f9d077f7e24557232a55e9276519cd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:2564"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.clear_finite_overlap_discrepancies",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "466ec716381eb3e62864088921d257a7b56a5bf8d2a29d9cb50db8e0cd0ef02d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:18104"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.compact_open_section_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d972a4b58a42160c1cd9a84cd98c6b1b344f96f979abb7e4b3323f59ff2e64c5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:11554"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.finite_affine_local_extensions",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c7de36c5e4475a415a7445ada6fe73adbed79faaec7154c73543eb6c36108716",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:21350"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.finite_cover_power_gluing",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "35bbd64d9414cd3716cacc0a09827bc1847b6fd2c3e13fd672c33c8318282170",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:20344"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.global_section_extends",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4a936b57bf0d7a84f8ade46c86d443023bb81db308351074d1022e0795939845",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:22175"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.global_section_extends_native",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "71fc8c00babe3dd8d9105383c0f1db3b6c0d8d2fb89f3178b0d87d8e01457650",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:23218"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.instAddCommGroupCarrierOpenSections",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "81f1275cdf0c8bd8c6a306e31850319e2b6ef3a1da31d851bf521d171c7ae398",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:726"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopCarrierOpenSections",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c61fab96a45d2f6b4dd9e54730d697529aa717b03dde1b4c4b798dd5c5bbf055",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:845"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.openRestriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a8d758ac7135a0d2375e4e7554ac07b3fa74023b53c969b1c7ae2172783a94df",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:975"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.openRestriction_comp_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "897c023daf57146f25dda8aeabcc7fe10fb682fec2564dba260ea10f10c5cb36",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:9294"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.openRestriction_zero_congr",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9fb12e2f36287dad2b244a0feea50baa3ac93567d64d24312da842687bd2385d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:9665"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.openSectionsCongr",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5be1b6b0cb27420a2763d50c39ee765ad9ae56cb6869340dd6d03c3ac2f4697b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:4217"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.openSectionsCongr_naturality",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "11d42d726f27aa4c38fa8c67f6d093912130b04f406616a94d7901c2aa1a3710",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:13397"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.openSectionsCongr_restriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1a89e3a16f99242d09496a7f49c011390dc9e937d76324eea55a125c5ab1a061",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:4392"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.overlapDifference",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "de9c79f15eb63ac3d232974f88f158d8deb98f66c5bc5c2e8f31978637db09b3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:16330"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.overlapDifference_restrict_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b70cd665c942e71a6ccffe49c80cbf0cd6cfdf26e18ef3e7cd00bc81dc9a950b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:16538"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.overlapDifference_smul_zero_iff",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "41932d303244911d1e0e0524ef847bc02b607b9d55ef2bcba15ab2cb81a106e7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:17676"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.principal_open_image",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f5e221659c59bc0b697a3710dc5fcc056a175bf259d1e9993ae29fd0bb6d6211",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:13704"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.quasicoherent_pushforward_iso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4ebfcc6ad7adf4ca476945c66430878723c8e9a74ece50c2c6cdb8f6640815b0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:1555"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.restrictScalar",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "014733666f87d6f3257cdadc469ab5c282441190e7160a93b7af74ee647bd6c9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:245"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.restrictScalar_appIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cb7869bd6e13b9fbce13f8cdf6340ae5095dcc1a758f8f12123aa28fd64f447e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:6945"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.restrictScalar_naturality",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b19da7b5505c10b5327cf6ecf303d2d378b6b6c07d88bab8f7b204601bb28500",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:373"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.restrictedOpenSections",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8a6476ff83529c91a661ac0bfb1823d5a141e47043c62ec4eefbd6ef0039a275",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:7538"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.restrictedOpenSections_naturality",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3451d567cdb4e01cb55dec35961df2a6c40e511ee4a70a4ddce4b758b1325d3e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:8415"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.restriction_of_glued_power",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d38ef1a1616c84a9d80d8930cd586743590f6fe1704cac9b7347adf86b054c81",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:19216"
    },
    {
      sourceName := "OAI.PiExponent.GlueGlobalGenerators.exists_finite_global_generators",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlueGlobalGenerators",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e6f38beac444514282e6376bbe01f1bd774a357cb9f4d33fee1e2c05de9812d9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlueGlobalGenerators",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlueGlobalGenerators:2896"
    },
    {
      sourceName := "OAI.PiExponent.GlueGlobalGenerators.globalEvaluation_epi",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlueGlobalGenerators",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0deb9a532293e3f6ca47316f87e88ddd17c38c3a6beb16c1b7a7bd47eae0d445",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlueGlobalGenerators",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlueGlobalGenerators:796"
    },
    {
      sourceName := "OAI.PiExponent.GlueGlobalGenerators.globalGenerators",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlueGlobalGenerators",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "494c2607a454774e1064381e47a2bcc90aabc6259900422f2972d5904e23ba8b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlueGlobalGenerators",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlueGlobalGenerators:2484"
    },
    {
      sourceName := "OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlueGlobalGenerators",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "455e4937f595ae848e32e96fca9a5f4ac0e5b22ac60da2ac67701352e7cb185c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlueGlobalGenerators",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlueGlobalGenerators:2650"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.Cochain",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "500a52ff8931926ef5d76b2eaaf2afd06d535b1bd4ff01367ab64d43c50d042e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:8810"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.IntersectionPiece",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d1f1f2d97a300f7e0cf9b424d41f58b95a254a3b92f3b3006582f299c7eca31a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:6968"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.augmentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8a8c94f3630885dc5baf4a4c006bf1415eaff15cc7dad59b68bd10ac1101e666",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:11771"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.cochainMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "14edcbfe449c740119253fa15d0fb2cdb3ce39babd1708b916ed5eaba53fdada",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:13851"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.cochainMap_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "880b2f41640a4080883faa8ca0bff97db9042f08008d5ce52e997fb6c3896f88",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:16656",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:16656"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.coverProduct",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7512a99489388bd57cb3c4e4ec0fc986a9c70d2b75f3c03acd419214ac252199",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:5822"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.coverProduct_dvd",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "45f828b15411b925eb28e383acb6c34c66f8045dca9bc8ffef4c1e9aeaba9d50",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:6758"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.coverProduct_factor",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "68e13de4004716c83754cd2362b6d62cb0231287b6c5e155b3c08ad34afcd839",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:6309"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.coverProduct_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "af1294659cd591e3fdb4400352a4eac67677cb4acd3088a013b8f44b07f31c6d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:5881"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.degreeRestriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5f80ecf5924ccd71056121a021630a75696fca27b5df139b078abd6a77060a7b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:4602"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.differential",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a0b3d465f2eb219e7cf174b9414a264b785c24c2e555a2ad7d099696b9fc3fee",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:8929"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.differentialHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d5a6ffac184d61a118ad981bc3a1899784a732251c1b844368af4335eb94f7b7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:11434"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.differential_augmentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6f94b63a36b863f0127ed17543e7eab26b710c0b3bdb707848c8d43d50c31b3d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:12574"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.differential_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7e3fc408c8ef5d81be57663fa307682af1ec92419cdd62441435b820983d9b97",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:9199"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.divisor_isUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "abda57cc9ada972f613132272dc5246a5b7081f798952f6b9a99a3c363a246c8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:350"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.divisor_powers_isUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "54c442dff0935ebb33ddff6a859e2e4bd8c396247b1f5561237a9cf849aaf6dc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:811"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.evaluate",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "210f2b3b5b084d06a9fa59f43de420490052aa39772b8ca3449669cd26412877",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:9977"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.globalPieceMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "56ca042a6e12ab2f007aa3de1a2a4363092bf2b70cb2cc0a974b688c864a9d52",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:15018"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.power_smul_fraction",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "43de8eb2f831801add673fa68d44329fd998632db33a505b4fdc3622885ad27c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:1816"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.restriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "466a3b612e932e37d2fc3974fd1c77313d872a6158719e28032d5bf66197477a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:1097"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.restriction_fraction",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e56d4a20e56526d10668b54034406ef42f9218160452ff208e5d34f867f50570",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:2061"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.restriction_fraction_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "389d3225a8421954adc34ebc3a9b1036f9e816b373d786db495ab1c1d44bbdef",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:1587"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.restriction_mk_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fdd6eab3f027e24cb9777694312b4903fd526531d44e83618367a7b87d5a1ca7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:1387"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.setRestriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dc6bac317bfd12d1c39399e798cc260e1731154f405346226de79536cabfaeec",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:7116"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.tupleSet",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e5e532e2011fd69750892a1716165f5d135ff5f2e1e275482474c690a80d8c4c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:8470"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.tupleSet_comp_subset",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "38dd52137ac01b41d6e263b1f57ad76853633820461a70018b212d58873a5b86",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:8548"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.tupleSet_subset",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0ea2364dcde9b1f13ff137c0291ced16f9b1e27072d0b9d99a050fb1a41242ef",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:9734"
    },
    {
      sourceName := "OAI.PiExponent.GradedCechExactness.augmentation_recovery_of_shortExact",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechExactness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "06281bc31a4a21475a97c8145dd9ed5835898292af923ca3dbccc6be244fd136",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechExactness:1366",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechExactness:1366"
    },
    {
      sourceName := "OAI.PiExponent.GradedCechExactness.primitives_of_shortExact",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechExactness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c2accc2c8c8224dfb4d55f5053bf5e4b4580c13fd0faca76ee84c0770639bbe7",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechExactness:3397",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechExactness:3397"
    },
    {
      sourceName := "OAI.PiExponent.GradedCechRecovery.augmentation_surjective_on_closed",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechRecovery",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "317a7d1a430a508e2acc116ec2abd3071e534bd1d964ab957cb0eea879eecdac",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechRecovery:113",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechRecovery:113"
    },
    {
      sourceName := "OAI.PiExponent.GradedFreeCech.coordinateCochain",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedFreeCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eef33bafaa4527ab314ba2de910c1de30e8c11ea4503a10eea8bb547f8a52e91",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedFreeCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedFreeCech:1454"
    },
    {
      sourceName := "OAI.PiExponent.GradedFreeCech.coordinateCochain_differential",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedFreeCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a1baa9851567011544e115c295bd5f671709ac300a5a7419a22ac466d41b12cb",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedFreeCech:3996",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedFreeCech:3996"
    },
    {
      sourceName := "OAI.PiExponent.GradedFreeCech.coordinateIntersection",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedFreeCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0c350dc110f6618d170c4c27ec97d91640ea5bad2ac311dfdbb60f8cb4f56e35",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedFreeCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedFreeCech:507"
    },
    {
      sourceName := "OAI.PiExponent.GradedFreeCech.free_augmentation_recovery",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedFreeCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "28c9898099404825ae214bfaedd1bce3d7e1d96cbc1495838fc15f38698a7207",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedFreeCech:8591",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedFreeCech:8591"
    },
    {
      sourceName := "OAI.PiExponent.GradedFreeCech.free_cech_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedFreeCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5cec61949a23daab81ee65ad7d48f9cb8468db283c205352b55f4e3c3bd808e3",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedFreeCech:5493",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedFreeCech:5493"
    },
    {
      sourceName := "OAI.PiExponent.GradedH0.NonnegativeMonomialSet",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedH0",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9c7f69df01ec8fae1d14e4d4673dd66bdfb1c86d62aa875a28967f401ec91f8b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedH0",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedH0:367"
    },
    {
      sourceName := "OAI.PiExponent.GradedH0.PolynomialExponent",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedH0",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3a90bbf3314e1caf1baebf03d7e38eee85609b8b3447ffdec5cc00e36096b2ee",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedH0",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedH0:292"
    },
    {
      sourceName := "OAI.PiExponent.GradedH0.decode",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedH0",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3074b9d343bfe88bff9d61f0a41602b3d1004255769055ae03a78873f671fd11",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedH0",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedH0:962"
    },
    {
      sourceName := "OAI.PiExponent.GradedH0.encode",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedH0",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "70d1dd2fc69aac2cc8ec1df33367ea79dcd819443acad6ba94e9f77e1255ee5c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedH0",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedH0:462"
    },
    {
      sourceName := "OAI.PiExponent.GradedH0.encode_nonnegative",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedH0",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e7f7acf642531a6965f0e56c2fc0e3ac8bcb98b194d1414b99aacdab847a99cf",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedH0",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedH0:795"
    },
    {
      sourceName := "OAI.PiExponent.GradedH0.exponentEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedH0",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "605891088c795d034e251491f0df2ae153413f06a0d77c7412f794341f2d8a3c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedH0",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedH0:1678"
    },
    {
      sourceName := "OAI.PiExponent.GradedH0.homogeneousPolynomialEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedH0",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e65f93d3f749a7c23677a964a25a58a04a091f6e942cc01900fa5c620c1f5b98",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedH0",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedH0:2114"
    },
    {
      sourceName := "OAI.PiExponent.GradedH0.integer_grading_eq_homogeneous",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedH0",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "70c4d16fe6fa80ea9ca2aaf88e404339848276f53227a5777b4f5148add54699",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedH0",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedH0:2626"
    },
    {
      sourceName := "OAI.PiExponent.GradedH0.polynomialLaurent",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedH0",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ec11253bc72e13b2a7a4124984f87049bd41279d56edfd9cb392293cd7b1682c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedH0",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedH0:3583"
    },
    {
      sourceName := "OAI.PiExponent.GradedH0.zeroth_cocycle_unique_homogeneous_polynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedH0",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3da3a52b8c4d48444709effef6a9dfba6aa29db3b3060581bef33896c99f2b9a",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedH0:6907",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedH0:6907"
    },
    {
      sourceName := "OAI.PiExponent.GradedH0.zeroth_cocycle_vertices_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedH0",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9f87b1cfadff0524d8520971c8128dc4c21ee374d95ee04a977b25d108b6de04",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedH0:6045",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedH0:6045"
    },
    {
      sourceName := "OAI.PiExponent.GradedLocalizationExact.degreePiece",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a54578ff0ab0d19c621acd35323cb5cfa82f2f0d7812309e9538777cba79fc3c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:2871"
    },
    {
      sourceName := "OAI.PiExponent.GradedLocalizationExact.fraction",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1c87890a204b3afd977205b2ab8be54c59304c00d44d96bd6bdc4095abf51849",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:972"
    },
    {
      sourceName := "OAI.PiExponent.GradedLocalizationExact.fraction_add",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "691b36136f71ac7be7c3ccaa841e247715a9c4448afc1088843f2c328d5b531f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:1342"
    },
    {
      sourceName := "OAI.PiExponent.GradedLocalizationExact.fraction_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c0561d93d158c5bb45fd84c53fcfdea9e6791e33672aba0908b6e48c154e2e0e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:1930"
    },
    {
      sourceName := "OAI.PiExponent.GradedLocalizationExact.fraction_neg",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "68d39e482ad1af38056654b59fef938cb388414c4e0114514996471a9bf69ef0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:1215"
    },
    {
      sourceName := "OAI.PiExponent.GradedLocalizationExact.fraction_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a2c711541849b7ec7560f1ae9ee5607b8495b2e1cadd3a60e74d7a3f606763e2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:1105"
    },
    {
      sourceName := "OAI.PiExponent.GradedLocalizationExact.localizedMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b68a7f3ca999331e50dfac88fc1c8da68823ded075d3cbf5b23aac7f041e6e32",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:3872"
    },
    {
      sourceName := "OAI.PiExponent.GradedLocalizationExact.localizedMap_fraction",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4cc54ea8f9b7c0ab2de68a42716d825614cd40deb5d87c3f7e983ed526910d90",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:4131"
    },
    {
      sourceName := "OAI.PiExponent.GradedLocalizationExact.pieceMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7badd76a902d54ea4eb2221d0222ebf92ce294edf959d5968836728af9d6626f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:4389"
    },
    {
      sourceName := "OAI.PiExponent.GradedLocalizationExact.pieceMap_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "413ffb6dc95c27521bf127df71ca4af6dee7c115c10541d165c5bb7c8d0385ed",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:6712",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:6712"
    },
    {
      sourceName := "OAI.PiExponent.GradedLocalizationExact.powerDenominator",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2cf016b70e320088e230e6340f68ffb81e0d6c03b84a1e37c6a1e5c24007ef0d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:458"
    },
    {
      sourceName := "OAI.PiExponent.GradedLocalizationExact.powerDenominator_add",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b11da4ff7156778f2b5da57e601fd1d3d7e7f77a3319d296c1e852f9e0eb48bb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:790"
    },
    {
      sourceName := "OAI.PiExponent.GradedLocalizationExact.powerDenominator_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "413593ee3cc1ee67489fd73ab91aa25fcd8399e9e8036b643aaac958eff28b0b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:660"
    },
    {
      sourceName := "OAI.PiExponent.GradedLocalizationExact.power_smul_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2b5da4e0f3678eb22435353cf29bab6f35badf5af174698f9880d50285846d74",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:2560"
    },
    {
      sourceName := "OAI.PiExponent.GradedLocalizationFree.coordinateMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationFree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "634722bcbbc03a814f8c5bfd0b61bb02152f0b346c8eef2f41ecb237558c1b75",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationFree",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationFree:318"
    },
    {
      sourceName := "OAI.PiExponent.GradedLocalizationFree.coordinateMap_fraction",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationFree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1716a1ed98356e037b9f0b57db23228a9eb3d16431ffd78610823099be33ca12",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationFree",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationFree:529"
    },
    {
      sourceName := "OAI.PiExponent.GradedLocalizationFree.coordinateMap_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationFree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e79653212dec674af4b11b7dddbe6c8c6cce2372b544e9fee5159975115ab9f8",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationFree:868",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationFree:868"
    },
    {
      sourceName := "OAI.PiExponent.GradedLocalizationFree.coordinatePieces",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationFree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ed76f9558ff4fa62869d40680afda3c988fac8ee780f066a51147d9b7909e720",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationFree",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationFree:2144"
    },
    {
      sourceName := "OAI.PiExponent.GradedLocalizationFree.coordinatePieces_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationFree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "76830afbfc4037f183078a4ba8def93a446320383b0591d61306f6268d544831",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationFree:3233",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationFree:3233"
    },
    {
      sourceName := "OAI.PiExponent.GradedPolynomialCech.cochainToLaurent",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "344c528cbfd081d57d266071109d900ad3433d9f12ab3b49ba15327357bed4fb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialCech:1239"
    },
    {
      sourceName := "OAI.PiExponent.GradedPolynomialCech.cochainToLaurent_differential",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6c70ceb5230069899ca6e95d9f2ce639c25bdc714faf2b66ed0f391c0f26fe44",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialCech:3095",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialCech:3095"
    },
    {
      sourceName := "OAI.PiExponent.GradedPolynomialCech.intersectionToLaurent",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e973cfef777dca1801adda0b11c04c874296bf5a4a4909021e5873838f697595",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialCech:727"
    },
    {
      sourceName := "OAI.PiExponent.GradedPolynomialCech.intersectionToPiece",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "788a46600f322f02f5d53e50877633c4c8ab90baf36c62a6b0845b23b1095bab",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialCech",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialCech:444"
    },
    {
      sourceName := "OAI.PiExponent.GradedPolynomialCech.nonnegative_polynomial_augmentation_recovery",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "526368e0010b7e0d67d77b8e5d298c757981d3c6f3a2ccfd9bbbb1a795de394c",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialCech:5155",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialCech:5155"
    },
    {
      sourceName := "OAI.PiExponent.GradedPolynomialLaurent.GroupAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8a73f0d07fdf3d8c72bc43adc0c992a9f28e70c2db3289303d19d85c73f7ad08",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent:451"
    },
    {
      sourceName := "OAI.PiExponent.GradedPolynomialLaurent.Piece",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8c70284553d78dae93965c24b2565e9117fcc59777d2a93b4b36f35a573e5fb6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent:7860"
    },
    {
      sourceName := "OAI.PiExponent.GradedPolynomialLaurent.grading",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "89b9466ba82592e3864925a547fcde2f844fb8d5ddfc126bb7091c68f82f21d5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent:7369"
    },
    {
      sourceName := "OAI.PiExponent.GradedPolynomialLaurent.moduleRingEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6c7198e4a05c9ee039ccb1cbfa49c905adc7b3afacf5003e3ee489cd4c4ffd63",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent:3457"
    },
    {
      sourceName := "OAI.PiExponent.GradedPolynomialLaurent.moduleToGroupAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6a0a883252cc8201bc5fb2f078be6bc9ac4df4252daaaee44570b7bd2eb475c4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent:4123"
    },
    {
      sourceName := "OAI.PiExponent.GradedPolynomialLaurent.moduleToGroupAlgebra_fraction",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5adf5bc9438a9733c3645f9479645af5bca3f35d3e20b27922c80d80a1e0d0ff",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent:4568",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent:4568"
    },
    {
      sourceName := "OAI.PiExponent.GradedPolynomialLaurent.moduleToGroupAlgebra_restriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e39f3974d46cb2a1e2f7814d0a85744fdd642350bf17bc02a7bed3a4e1db3f92",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent:13847",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent:13847"
    },
    {
      sourceName := "OAI.PiExponent.GradedPolynomialLaurent.natExponentHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3a2f1e72bfae117ca8711e82148f7666754f3b89ac9ebdf5714715daa8885426",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent:508"
    },
    {
      sourceName := "OAI.PiExponent.GradedPolynomialLaurent.pieceToLaurent",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5fbb8b0f5233691590b4084203a59180312d2b0042d1ded2b14995b23b7c5272",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent:8738"
    },
    {
      sourceName := "OAI.PiExponent.GradedPolynomialLaurent.pieceToLaurent_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7bf8cebac671b8713773a4f48340e69b9694aaa9a3e18c7c618202a72281c157",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent:9546",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent:9546"
    },
    {
      sourceName := "OAI.PiExponent.GradedPolynomialLaurent.pieceToLaurent_surjective_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "46eb95d5bfbe2f23c37c6459e40a00dfe095cfa1f65b9cc8bb185d2c85dd4d15",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent:12567",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent:12567"
    },
    {
      sourceName := "OAI.PiExponent.GradedPolynomialLaurent.polynomialToGroupAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c596c764b464bdf979d3b8c515797fff43763084c5e077a7ba347f37aae03da0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent:662"
    },
    {
      sourceName := "OAI.PiExponent.GradedPolynomialLaurent.polynomialToGroupAlgebra_X",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "81b3fad271a14e594757957fe7fbf9f272707ea322fef2c0cc14125bdffb8e80",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent:1536"
    },
    {
      sourceName := "OAI.PiExponent.GradedPolynomialLaurent.polynomialToGroupAlgebra_product",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "716f3977ff9634034b6a9563c3b589f333564d49db321dda99881ae40f0507e7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent:1845"
    },
    {
      sourceName := "OAI.PiExponent.GradedPolynomialLaurent.product",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1a14609542545297941f4730ed10cabde11cf42bb7569778479f0e99a5af5ac5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent:1047"
    },
    {
      sourceName := "OAI.PiExponent.GradedPolynomialLaurent.productExponent",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dc2c09e2781e2ec7ed9e0d9ea049c16ef5b0b76186e25c05248d3e71e5be7048",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent:1129"
    },
    {
      sourceName := "OAI.PiExponent.GradedPolynomialLaurent.product_isUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3ab17e4f0e10e2e5670aa75cafc80eecaf17d31090f495102c0fbbfcb5474b88",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent:2403"
    },
    {
      sourceName := "OAI.PiExponent.GradedPolynomialLaurent.product_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6c0303da295037bce1f3dfdb4156c9bc8433cc474807e102db6b5ce6bde9bda8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent:7661"
    },
    {
      sourceName := "OAI.PiExponent.GradedPolynomialLaurent.ringLocalizationMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "372e4fc0bd3197e090233147fc9f102b14c7494202e08df289df31e82aad7cee",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent:2578"
    },
    {
      sourceName := "OAI.PiExponent.GradedPolynomialLaurent.single_isUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "222acc8ba42a67c941721a4d91a2a3ca6b99f7dea26b195954cdf13699d9ec41",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent:1231"
    },
    {
      sourceName := "OAI.PiExponent.GradedPolynomialLaurent.variable_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0d7f9fc824472789f830b303bf62da5869c45639dedea851092ff6908881faef",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedPolynomialLaurent:7494"
    },
    {
      sourceName := "OAI.PiExponent.GradedSerre.exists_graded_free_map",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedSerre",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f3b424745b325900fa6ce6c7cf1e3617d4d71634c53db26e7e02e035480d1c2e",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedSerre:5682",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedSerre:5682"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_011.jsonl"
