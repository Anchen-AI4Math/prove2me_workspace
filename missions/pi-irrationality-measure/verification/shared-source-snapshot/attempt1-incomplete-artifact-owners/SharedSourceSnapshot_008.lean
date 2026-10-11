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
      sourceName := "OAI.PiExponent.FiniteGlobalPresentation.presentationOver_of_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0cdb80246d755112bd1c99e61dfae6ae020b4df5e0b87f0439500da0fff50c3a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:5743"
    },
    {
      sourceName := "OAI.PiExponent.FiniteGlobalPresentation.presentationOver_of_restrict_isFinite",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1eba5c90a95f65ff37268d8d331e3476e75432e92304e000ac277e0978cc8b1e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:6426"
    },
    {
      sourceName := "OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4c58dbd0f53d8caf61e3a29285d4871b6e55b514a297a38fcb30ef05f9377a40",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:879"
    },
    {
      sourceName := "OAI.PiExponent.FiniteGlobalPresentation.restrictIsoOfLE",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "696f0248487ded9764f1bebfe8070111ca1d1073f3a0978fafc3271a0f5416ec",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:14085"
    },
    {
      sourceName := "OAI.PiExponent.FiniteGlobalPresentation.spec_exists_finitePresentation_of_sections",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8a055fc675cdcacb7c4b8ba58f76a8f9ea2d41bd2bc6b0b675d73917d6ef1f95",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:4116"
    },
    {
      sourceName := "OAI.PiExponent.FiniteGlobalPresentation.spec_kernel_exists_finitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0723b3d7474ab61a4393b9f74e6ec34a0399d27dc3bc3a3b3725a707b2d72204",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:4797"
    },
    {
      sourceName := "OAI.PiExponent.FiniteGlobalPresentation.spec_kernel_isQuasicoherent",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b12d123e083ed5e5f441ce92ad4ffb77209c90a0b419fb70888a0ba75ad68862",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:2938"
    },
    {
      sourceName := "OAI.PiExponent.FiniteGlobalPresentation.tilde_exists_finitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4bd2c7a1e7617b55eb746f0afb630d166858a12b04d14d07bf4e5c2e97cfbfbd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:1999"
    },
    {
      sourceName := "OAI.PiExponent.FiniteTupleCech.Cochain",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d49f095708b22bd5732bc3a2a6e1828b82b1d55152a207e2631c2942f7e02734",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:617"
    },
    {
      sourceName := "OAI.PiExponent.FiniteTupleCech.assemble",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b647667423b5537bf206c518abd3285af3b121e7090fdbf8d7595d2358b3f6a4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:3212"
    },
    {
      sourceName := "OAI.PiExponent.FiniteTupleCech.assemble_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6ce7592d1e54d70854b6af4d80310f17eeabfaf9620a9f8e7fa098ab2a5df1ce",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:3454",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:3454"
    },
    {
      sourceName := "OAI.PiExponent.FiniteTupleCech.differential",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "473e96a39f47514a7a917ea3cef70d20124e17bd3d2ae7302151ea88522d38e4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:690"
    },
    {
      sourceName := "OAI.PiExponent.FiniteTupleCech.evaluate",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "20f8517ae8a7b25b76d282a01e6bbb0893bece7e0bce31d4223c5af2cd8d8f90",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:1757"
    },
    {
      sourceName := "OAI.PiExponent.FiniteTupleCech.level_correction",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "567bc5286c2099ad7a25f79391985b4cb462fee98ee64384395475d5318e2c3e",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:4908",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:4908"
    },
    {
      sourceName := "OAI.PiExponent.FiniteTupleCech.liftTo",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "178b87044fb97526d46d6fe690c092c3ccc68caa549483cbf31338260b97b0e9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:1612"
    },
    {
      sourceName := "OAI.PiExponent.FiniteTupleCech.mem_tupleSet",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f9e8bddc0e24239d655e1f5d11b9f7ba9f3c118784a6f39e48266272e70cc20f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:1470"
    },
    {
      sourceName := "OAI.PiExponent.FiniteTupleCech.primitives",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "df6f8134a3efc211c1ee4022d0811b21d5d97935ebe013dce68747e64ada5b5f",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:6753",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:6753"
    },
    {
      sourceName := "OAI.PiExponent.FiniteZeroEuler.finrank_eq_sum_localizations",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteZeroEuler",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0d44fce4db2476637fe91d18e642643eb6f07535db5454d0fb2ad3a4a8ef77d1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteZeroEuler",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteZeroEuler:275"
    },
    {
      sourceName := "OAI.PiExponent.FormalBranchContact.branchCoordinates_constantCoeff",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalBranchCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c21e19223e3cee226a6191ea17843a13596e4cd630ee9a9ea63cb1f5a99a93f6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalBranchCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalBranchCoordinates:737"
    },
    {
      sourceName := "OAI.PiExponent.FormalBranchContact.composedLogTails",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalBranchCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4b65ce4799e7a9e4a6536f7c2ea6af579ff037f884f315ab79abc7cda54885b1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalBranchCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalBranchCoordinates:203"
    },
    {
      sourceName := "OAI.PiExponent.FormalBranchContact.composedLogTails_strict_contact",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalBranchContact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b224ec39f710af525a10e7a4420827b3125b45a02f6a639f0c14ca323b879d4f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalBranchContact",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalBranchContact:248"
    },
    {
      sourceName := "OAI.PiExponent.FormalBranchContact.composed_logTail_order_ge",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTailOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7332418337616b79d0b62fa0072df58c720a03e0c1eb1e1356ed6505fdac1a5c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTailOrder",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTailOrder:382"
    },
    {
      sourceName := "OAI.PiExponent.FormalBranchContact.composed_logTail_strict_contact",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTailOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a1de65506137d7e348c0ed5d99b3d568e2054fe5a4f490c0ac9ce2d002b5afb5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTailOrder",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTailOrder:1060"
    },
    {
      sourceName := "OAI.PiExponent.FormalBranchContact.contact_truncatedBranchCoordinates_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalBranchContact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a836f891d811e3ddfc6a93c5ebcf3a3d084d9f40fb63a7a02697fa9c86900958",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalBranchContact",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalBranchContact:1540"
    },
    {
      sourceName := "OAI.PiExponent.FormalBranchContact.logTail_order_ge",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTailOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e7aa9ac070be108295cef4b0e51d562fd904a48193498e9380f7b086b6e46bc7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTailOrder",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTailOrder:236"
    },
    {
      sourceName := "OAI.PiExponent.FormalBranchContact.truncatedBranchCoordinates",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalBranchCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8d660ac3b2665a6480c6d89ad9e62a44905ef8969ef746f08330f8e2cc5d3448",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalBranchCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalBranchCoordinates:399"
    },
    {
      sourceName := "OAI.PiExponent.FormalBranchContact.truncatedBranchCoordinates_eq_add_tail",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalBranchCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "81fb288ebb62d5cffa0e04477bbcb1ff12a10b69900f87d9bb8459d56c2be2bd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalBranchCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalBranchCoordinates:1221"
    },
    {
      sourceName := "OAI.PiExponent.FormalBranchContact.truncatedBranchCoordinates_not_all_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalBranchContact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1f2150d0becf3f8960a56b3491e8151264c4608235e60602faaf3f97ddbc9a4d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalBranchContact",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalBranchContact:846"
    },
    {
      sourceName := "OAI.PiExponent.FormalBranchEvaluation.branchCoordinates",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalBranchEvaluation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8716e47c271c986e70d1799fd274d4ad596ec5304cd614b3a862b3baf02401a9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalBranchEvaluation",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalBranchEvaluation:280"
    },
    {
      sourceName := "OAI.PiExponent.FormalBranchEvaluation.branchCoordinates_hasSubst",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalBranchEvaluation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7168f458010869d30e007644f33916b1abf6643bf77350ffea6f769523f95f88",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalBranchEvaluation",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalBranchEvaluation:538"
    },
    {
      sourceName := "OAI.PiExponent.FormalBranchOrder.rational_order_subst_of_jet_vanishing",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalBranchOrderRational",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "64cc1e3655a790844239c65b6aaed9f45ee4822aeff7e6bbb6b792cc17fb3187",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalBranchOrderRational:1872",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalBranchOrderRational:1872"
    },
    {
      sourceName := "OAI.PiExponent.FormalBranchOrder.rational_weight_le_of_contact",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalBranchOrderRational",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c9acb93be431d32351b340fe88e38bd5d68e07fdfdd151e8fee87542b2eb2230",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalBranchOrderRational:292",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalBranchOrderRational:292"
    },
    {
      sourceName := "OAI.PiExponent.FormalJetDerivatives.jetFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalJetDerivatives",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "69d22f80d0373ed91875fd9062279eb13aceab9353cc5f492ebf3081d03cce78",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalJetDerivatives",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalJetDerivatives:1003"
    },
    {
      sourceName := "OAI.PiExponent.FormalJetDerivatives.jetFrameWord",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalJetDerivatives",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2bf100fb2298682e249db7e647067b8668cf7effcca018cd1e6a769c85021fac",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalJetDerivatives",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalJetDerivatives:2119"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogJet.formalJet",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "171b0c4d75d407c80819c4737daad61a712e62bd5bf260ac9e7b941171b54fb9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:2786"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogJet.formalLog",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "63502c455521d85d296e3e9e61cfd7decd76e44f78e2d20f99cc1048af622a7b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:1982"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogJet.liftSeries",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f29ece8d37a43165610bdfd424af8f4c2f667a36b3035f9fd25dd2b41d0414c8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:351"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.coeff_logTail_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f7ff2343de0159bbe6f7c9ce66c06cf7e3d930a1233a4f353754eb006f06a802",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:12577"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.formalLog_packets_surjective_iff_truncated",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "765a99a77fd142aaeb3df1bcc101b03f3293b01e0ffa931f7cb80e52a4d8fd40",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:17060",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:17060"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.liftSeries_eq_toMvPowerSeries",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f704e41dcf8eb20cf097719347c61a77410f7a334993d806c46186f0ffe28ddb",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:356",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:356"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.logTail",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7059cab353e93dad43da92d68b12ca3340ad8cdd10ff085bf7f7cb6fd63896a2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:12228"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.logTail_mem_rationalWeightedIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c79d445b1cd21881baff3970f2e78b670a8e5a26f64a9804ed1287b08967e0d3",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:12753",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:12753"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.rationalWeightedIdeal_prod",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f33b3cab9cc487d18eade93b242ccbb9a27f685ca1af3c659db52c244d47eb10",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:5661",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:5661"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.shiftEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8cb02284393971870cf7f485d61e89645f85e1c3985fc20701eaa3f6d04e665e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:4823"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.shiftMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2d67a334735de0ce0cbd5ed424e3ab1712706a26c4f53aed8d8b814d651a4780",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:2212"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.shiftMap_X_succ",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8794b72880dfe300220df557d61ea2c43e35837f6a08fc634ceae06c9edcecef",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:2680"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.shiftMap_X_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c77127ce9c1356f570e6db1fed914bff084236e58727dac2d3128c25409bed3b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:2463"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.shiftMap_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2af74c3d76107dbed36459dde797b8e5de723b838f089697160be4dcfe8239f8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:3738"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.shiftMap_inverse",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c00a365b065dc7b70a52037b49a0b2c46ec40e5c40edd78d97890cd122885cf2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:3955"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.shiftMap_toMvPowerSeries",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "94254c5f5ca9b475c60da1226d1e961ebe8e37c57b3ddb143359a4909edf78d0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:2948"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.shiftMap_truncatedFormalJet",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c1454eab1a53cd667dd8876a0cdf7b3a495045845b7191ab04eb6462a76b764d",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:14165",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:14165"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.shiftVars",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b3ef70191454e1517227942e8a21eb5ef62eb87a92b55433d62b15511677feaa",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:1560"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.shiftVars_hasSubst",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ad59535979bf669ba282d2622e0a8aa8eb1a059831af188918af89bedbe6278f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:1754"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.subst_mem_rationalWeightedIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1bf053ca81251ec2cbf33428c957a43265d3deb25aac9046cadcf4ee2f5de964",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:6447",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:6447"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.truncatedFormalJet",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "db33108348d20b5b45e87b9d8562e28fba263be2e4a9e3cd5457a3b411dcb6f9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:13808"
    },
    {
      sourceName := "OAI.PiExponent.FormalMatrixBridge.cast_finsupp_weight",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalJetIndices",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b27af738b4aa65ce0c0383fa1101769a6c3e578dd6154e162f25f171d31cefc7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalJetIndices",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalJetIndices:310"
    },
    {
      sourceName := "OAI.PiExponent.FormalMatrixBridge.exponentVector_coe",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalJetIndices",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2e0a7660da497b560e68d7c962a838bc85a52b47d2126a8b27086b1ae7810da8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalJetIndices",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalJetIndices:155"
    },
    {
      sourceName := "OAI.PiExponent.FormalMatrixBridge.flatten",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FormalMatrixBridge",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "859de1334990532b2025cf57e370e53c5162a8237d72f60fdddd9a9c712e4cb8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FormalMatrixBridge",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FormalMatrixBridge:326"
    },
    {
      sourceName := "OAI.PiExponent.FormalMatrixBridge.nestedPolynomialSwap",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.NestedPolynomialSwap",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1c5cd881bcf1741d8f6a5a5b2145b4fc2c87b85d22285cc5877d8839092c092d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.NestedPolynomialSwap",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.NestedPolynomialSwap:138"
    },
    {
      sourceName := "OAI.PiExponent.FormalMatrixBridge.polynomialOfCoefficients_of_weighted",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalJetIndices",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6dbc636ab6eca6ec3a5fa4122e22f5c3b2ba640289d8629643d0be8bdac1f661",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalJetIndices:2052",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalJetIndices:2052"
    },
    {
      sourceName := "OAI.PiExponent.FormalMatrixBridge.rationalJetIndexEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalJetIndices",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "08aa31f4252d6d7ae29580bf78ccb5c398f64889ce9eef1201963f9bb2bada70",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalJetIndices",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalJetIndices:581"
    },
    {
      sourceName := "OAI.PiExponent.FrameEquationFamily.BoundedWords",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameEquationFamily",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7bc7d1b2dc716bbe4b9a0cf8ac00238bb17963e86436e298b994f0ffdb852d60",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameEquationFamily",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameEquationFamily:242"
    },
    {
      sourceName := "OAI.PiExponent.FrameEquationFamily.equations",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameEquationFamily",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c7b3705f21b8156d8e6a048ab7c057518b09a405c12023e7762739e178925006",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameEquationFamily",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameEquationFamily:389"
    },
    {
      sourceName := "OAI.PiExponent.FrameTransverseMultiplicity.frameRectangularHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FrameTransverseMultiplicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c622b72198506011476c82a1bd855afe78d1009a52df6c67091c61ceb50166e2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FrameTransverseMultiplicity",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FrameTransverseMultiplicity:3399"
    },
    {
      sourceName := "OAI.PiExponent.FrameTransverseMultiplicity.frameTaylor",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FrameTransverseMultiplicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "497588e3291e7b20aa13aeeeb017c834c674e7c6cc068d97879cb11a5648bc10",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FrameTransverseMultiplicity",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FrameTransverseMultiplicity:322"
    },
    {
      sourceName := "OAI.PiExponent.FrameTransverseMultiplicity.frameTaylor_constant",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FrameTransverseMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "599b740f22bb4cc3a06e8ebf9ebf4f2dc1153168585e5af58927738e5cfda81a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FrameTransverseMultiplicity",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FrameTransverseMultiplicity:600"
    },
    {
      sourceName := "OAI.PiExponent.FrameTransverseMultiplicity.localizedFrameTaylor",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FrameTransverseMultiplicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bed7d38db7eaa80c4718bae9cba2a245c17b506d38a3c3f1637ee2f0e879de9e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FrameTransverseMultiplicity",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FrameTransverseMultiplicity:924"
    },
    {
      sourceName := "OAI.PiExponent.GeneralCartierDegreeLength.regular_section_tensor_euler_eq_sum_local_lengths",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.GeneralCartierDegreeLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bcec1225c19f2c20353a0f7afa58e912e6469c082de3fce86396298ab1b30514",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.GeneralCartierDegreeLength:3529",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.GeneralCartierDegreeLength:3529"
    },
    {
      sourceName := "OAI.PiExponent.GeneratorsSectionCover.freeProjection",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b9010849a80580c35d98519914ad014da375ff1ec79cd7865a7168910008ae54",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover:903"
    },
    {
      sourceName := "OAI.PiExponent.GeneratorsSectionCover.generatorSection",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "822b2e54ec78e4599cf2bfa13a0e01b3c3bd5191d9e9deb077cea9f384096c89",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover:5197"
    },
    {
      sourceName := "OAI.PiExponent.GeneratorsSectionCover.generators_sectionOpen_cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eb386ccf25fa2b680d654b92165f03f58125dd0170e931fdbb0d182cc5e6e877",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover:5345",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover:5345"
    },
    {
      sourceName := "OAI.PiExponent.GeneratorsSectionCover.unit_epimorphism_cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b568a398ca2d27dba5b14ce3d225e6663cad8e6dd45387825754b5beb6c21ae5",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover:2266",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover:2266"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ActualLaurentExtFinite.actualExt_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LaurentExtFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "74ebb476d0096b84e25a93cbf5774e084f6f7a5e920cddcf0222b330aee4f0a2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LaurentExtFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LaurentExtFinite:2357"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ActualLaurentExtFinite.actualExt_succ_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LaurentExtFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "21df4d63b250a27dea728d4e5b8f0b309ef2af548d1b4504dc67d76b351c8a64",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LaurentExtFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LaurentExtFinite:1870"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ActualLaurentExtFinite.actualExt_zero_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LaurentExtFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b54f751d0e0da32926a95a20e0db09d2bc7a4dadca0473619ff73ff8c12d45f6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LaurentExtFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LaurentExtFinite:1248"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ActualLaurentExtFinite.cohomology_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LaurentExtFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2a848adf9e3948b55efecfb6b7a5f806d82a7cceb24efbc8dd4da874144740a3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LaurentExtFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LaurentExtFinite:2803"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ActualLaurentExtFinite.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomSheafOfModulesRingCatSheafFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LaurentExtFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a65a1df60912217a8cde7bbbcc736c558ca60d25a29c079d44c244343b8b1ffa",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LaurentExtFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LaurentExtFinite:958"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.AffineIdealSections.equiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e19aed88d56dcc0c9f05d148f1522088016ea71b37e369d6afdcfad964cd02ae",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections:2869"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.AffineIdealSections.toIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b465e1e419f8d8129e7b8de71037651753f6421fc86e75201157f4ff11bdfc52",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections:1105"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.AffineIdealSections.toIdeal_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ffaa72404f2876d565040e2131bb685d9bdc6591c3b52ce4a34eb0d5c47b9b13",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections:1550"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.AffineIdealSections.toIdeal_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "db528d4e9d1c25f16b32d04f08c4d51ae442611153d3471e4878bcbee098a2c2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections:2208"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.AffineIdealSections.value",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e448e49be1023ed9c606d446581e019ab9744e3a461a17ec3ee0f70ea7a9c6b4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections:371"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.AffineIdealSections.value_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d6f22ebe7e064c1a7e4ec1e4c0bffa3bd01d28eff95bbf7170a4657ce8111e86",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections:527"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.AssociatedPrimeAvoidance.exists_regular_combination",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AssociatedPrimeAvoidance",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "761f76d41be1033201160e18746bbdf77c11eb6e73ca54d4b266885d95cd216b",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AssociatedPrimeAvoidance:184",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AssociatedPrimeAvoidance:184"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechExtFinite.ActualExt",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "31848440eaf0f2fca8b46a1e6f3df0b0991d4f11d5e28b86e90b69b8644d37ca",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:782"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechExtFinite.LocallyAcyclic",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8ac30a755ad33bfc9b0430e86359c3a1aa5243f654bd9797661807519526be9c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:2053"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechExtFinite.affine_exists_comparison",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "270823cf1faf9ed5a365cc7b93f2913b46122083004e6ff7cfd8f6aeb88b443a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:12005"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechExtFinite.comparisonStep",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eb7dd37953cab71c7f74142cc1f59a4eb4a90841bf5605ac743a61ac32cf2651",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:4381"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechExtFinite.comparisonStep_boundary",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "145c029cf9836d0d036483ef30773c7c2ec25547c3ce73e136a979bac5374b05",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:5902"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechExtFinite.comparisonStep_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5da0c55f815b91fcc9a440ee09c6bcb03ebd785861627f2a5a3a9f07fc0dd2d1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:4702"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechExtFinite.connecting",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fa3d6c0e9aa22dd93ff632d60976f50e4ad1b6ff3ca6b9cfa432f910202da18f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:1274"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechExtFinite.connecting_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "559731b7b1dd8afc881afd19bb6678536f27d1a159c2a91a08eff3f375566e5c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:1773"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechExtFinite.descent",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4b53ca1c539e4a0960c0cca7f3156165ccbfd057db2f5cf2265df019255e2630",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:2671"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechExtFinite.descent_lift",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "db76c2438f2e6a4d1abe84433bdf430c18fc49ed732dbcd4dc357ebaff3ec027",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:3494"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechExtFinite.exists_comparison",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eb70c7541d5a2f553261f788dec0a09c2d4033b611db9f4dc7326632bddef676",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:9223"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechExtFinite.globalModule",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "709c4bc48e10d077a8930c9dbb1883912a3a011cea0a0e1c31020ae2416970ab",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:1008"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechExtFinite.instAddCommGroupActualExt",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "72e5836d68a89d1c0fe9b93241a08daa2429e660bb65e628970c253e809ccac5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:879"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechExtFinite.locallyAcyclic_quotient",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e6931140438ef8bb8658692a97c2a71d07f4fc281fa1553d089b496ec64f8788",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:2231"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechExtFinite.mkZeroLinear",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "20c44386b3516e4e3389f8acd24da34a53f35162ce3bf13f96529d21c4b202cb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:6985"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechExtFinite.scalarModule",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d71516cf76b204d5c1a13207d87793dfe6a267989e999a4dd2895a431d13f7f0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:1163"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechExtFinite.sourceIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9d823a32c1eed908d97cd142e660566851c7e2b7a6ae2f16dfa6c460630b1680",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:11059"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechExtFinite.zeroComparison",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dbdb3c3f7918ebcad6661bdd1f6266757b647bc353538ef05009996d4e403a1b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:7673"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechExtFinite.zeroComparison_middle",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6f60a493e4099ef4bfb27527578f78b3c7d57b171ab27eada2445b19c79fdd0b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:8625"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechExtFinite.zeroComparison_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3d0fbb114eb9fb94c2c1c3ab59342d5769ee974aad2253410c9cda524c864fa7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:8108"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "inductive",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "495cad9fe2f420bbc87366d4b390bb536f0ce52750209075fe0c5284db88fa48",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:1241"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison.casesOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "41ec986cac6af1482ff56183a73583bfb302a85cfac5ef060b78bc849eb68221",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:1241"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison.cochainOne",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f1eeee05a66e17440c21b2257cf9eef055bc6c5da50835bd75832f05f1e3a35c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:2757"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison.cochainTwo",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "66b62f1d45dc33d966e1528e3e35fa7f9c04503fb71da863f20a488ab18af5b1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:3020"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison.cochainZero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3af83fc0533968551ba346117580ca22efe3515803c1fd894790d874e86a3fce",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:2366"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison.cohomology_one_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a357555b4554274b048675ddfc4395dc6483c3328de25cf59f596ae0c3539fc8",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:4833",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:4833"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison.mk",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "ctor",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1741d9bcd75fdf3d57e4f5449501be95767d5c2ac7cbaebf3760da3b4ffbcf1e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:1241"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison.mk.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "624100f581874d4dec1eddb89ca724ab1b36248ee3a83130892550f43a3dbc40",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:1241"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "604bac9f523b45ac88875c57b2e0dd156e42698a386e992740afd3d1420237ae",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:1241"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison.pair",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "35816fb597ef9c1f8290e0910c1259b39bd4c2963df52bd6e06b978ade0458c5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:1241"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison.pair_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0eedc4fe3c241a56b54b10fab988a102f836585698a20f451c2315e998e1758e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:1241"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison.pair_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6f6a9b84fd1a700796c03e4f157dd69235163128eee9fc8b3193b12905003d5c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:1241"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison.rec",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "rec",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "422f76da3404129c928875fc2445c61daf1f7d664c1fc77d916af9f6d7c54bea",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:1241"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison.recOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0282b465068bde9dce12edd8a6a8f843a512fa484ad016acac932391d4cdae96",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:1241"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison.triple",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c0ba775b66760be4f0569893ac28012c5f2ac79746903dd3db21b778e81ef139",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:1241"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison.triple_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a33c2299685063f4887ecf5d448df859b176860d00e5eafd42139883ae4d9df9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:1241"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison.vertex",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "effffe946dc269323f11b876b004e6af15d0d6a13d2f12254fbc06863d87bea3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:1241"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.Cochain",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cd591eddc00d8510937999c60afbbb17e676cf317bba4560ecdf361f36fbd464",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:997"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.HasPrimitives",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2a7a6fad2db55b8b7e831050c00e67faa99939a8a4fe97fb82d9e33051dbf8c0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:1287"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.augmentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "13595a30bc86e6443fb0004a3cc01ba28e9c7807fe0d8c791919240b53fc62fc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:12834"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.augmentation_closed",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eadd8d237245a827f5f3506a3cedc47032d8605ad1cc770300cfaa65ca85dd3e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:13023"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.connecting_cocycle",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fcef344aff4a708be4534ff60af80840c5c53e82f181588be4ee0a633ecff73c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:5907"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.differential",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "654abeb48a1c9d6026863549aa98bdb853ed95507c715069c03a0e0eec8c19a2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:1094"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.differential_squared",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f9d06005c77116c840cd58a1480d739690b1731fc41882c9de4c3dde9cc69bb5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:2960"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_008.jsonl"
