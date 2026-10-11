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
      sourceName := "OAI.PiExponent.PrimeWeightedBezout.weighted_prime_length_bound",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeWeightedBezout",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6e058c53dff3f9699328157fb7aed852d8118d1d28ede1be385f84cee9a98f25",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeWeightedBezout:415",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeWeightedBezout:415"
    },
    {
      sourceName := "OAI.PiExponent.ProjectionFormula.framed_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0a747976d3777c56769bc51605b48ce3f330b8da3c210a1c5f155dffb9c5b94b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula:4825",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula:4825"
    },
    {
      sourceName := "OAI.PiExponent.ProjectionFormula.hom",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "699272395bda01f6d103dbd76dcf3c053662a40fdc6ec2598f0e779a4db6e0cc",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula:551",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula:551"
    },
    {
      sourceName := "OAI.PiExponent.ProjectionFormula.hom_pure",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c47897a5890e72784b7b941df9431dda91299ada7742c4c94baa8ab8f781c9af",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula:916",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula:916"
    },
    {
      sourceName := "OAI.PiExponent.ProjectionFormula.iso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3ac1d58aa501d21e3531e3ec4698f687330ba5f550db7e42b990d755fb96c2ba",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula:8263",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula:8263"
    },
    {
      sourceName := "OAI.PiExponent.ProjectionFormula.line_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "46add9b3e4f7d9a7585fadc49f2a8ddfe165901314a9b76b981f23fc5a5c9e82",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula:7433",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula:7433"
    },
    {
      sourceName := "OAI.PiExponent.ProjectionFormula.naturality",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f80cdc0a613835844d7d6ffb1bc6c1404df49b4234c762b3a2ac747ce04e2303",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula:1746",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula:1746"
    },
    {
      sourceName := "OAI.PiExponent.ProjectionFormula.naturality_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "41b9768ff344b6309c1de0a41969869cc16d410134a670089fed34b91fe01960",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula:1746",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula:1746"
    },
    {
      sourceName := "OAI.PiExponent.ProjectionFormula.pullback_unit_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5aa0ea1855578e8dcb14e001f29fb5c9679a0d86fd1cf9e3b3932cb1749d8f8e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula:2587",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula:2587"
    },
    {
      sourceName := "OAI.PiExponent.ProjectionFormula.restrict_compatibility",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "528bb4b244f0e39adf602e539ffec06453ca2a0a68941b7da2eb06ec38ff0f23",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula:5357",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula:5357"
    },
    {
      sourceName := "OAI.PiExponent.ProjectionFormula.twistIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "690fa62e9633f8607197bfe2abcd4605b194e445523c8d839fa4c5f51e175c69",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula:8530",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula:8530"
    },
    {
      sourceName := "OAI.PiExponent.ProjectionFormula.unit_compatibility",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f2f6fc15ef4e4f82f04ad772d8a7c38c783f1abcdcf4bf3c683ed99b89d8c81f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula:2899",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula:2899"
    },
    {
      sourceName := "OAI.PiExponent.ProjectionFormula.unit_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9d83b7aab97a4e1d02dd360a760c0d7a80e9f6f91a8f9fe6b5c9ac770d8c1568",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula:4190",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula:4190"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveCoefficientBound.EventualBound",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoefficientBound",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bbcfb42672aaea2911333491e95211d137927b16016e8be2af40778824589b42",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoefficientBound:416",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoefficientBound:416"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveCoefficientBound.HomogeneousPullbackBound",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoefficientBound",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3fd6b7f4ae85761edc16662f813b371c9126002bc0973c124356dffe0194042e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoefficientBound:863",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoefficientBound:863"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveCoefficientBound.eventual_of_homogeneous",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoefficientBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ed8229f494b86e2f29ef5d3b4703fc5393458f75f7d27f01ac3584a51b12ab2f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoefficientBound:1738",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoefficientBound:1738"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveCurveTwoAffine.exists_hyperplane_avoiding",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCurveTwoAffine",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "25a746d370fd2bbe136a89a0246f84a2c39a50ac1731fac70dae3e5445497ab5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCurveTwoAffine:1172",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCurveTwoAffine:1172"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveCurveTwoAffine.linearEquation",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCurveTwoAffine",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5d7d4b9feae47d494716a110daeaa588d047f55b125c977859860de3055204b8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCurveTwoAffine:455",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCurveTwoAffine:455"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveCurveTwoAffine.linearEquationLinear",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCurveTwoAffine",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ba0cb0b49abbfa31f5b0c8c260c79669cf7dfc4331294d4925a0fcf09cb6664a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCurveTwoAffine:704",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCurveTwoAffine:704"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveCurveTwoAffine.linearEquation_homogeneous",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCurveTwoAffine",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5f118818c1cf6a4db0ad4c864065cf2395dc460ef9fc31a5b29644ad0871b6a9",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCurveTwoAffine:536",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCurveTwoAffine:536"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveCurveTwoAffine.linearEquation_single_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCurveTwoAffine",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "23ffb89d2867541c48a0e8d6d2ea9f3565423c2d977ba6c169d00da27e52dd3e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCurveTwoAffine:978",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCurveTwoAffine:978"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveCurveTwoAffine.two_affine_cover_of_affine_projective_map",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCurveTwoAffine",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "34ce7d292653a62c70022cafda6b2eaa3ebec477577d1421d7c50182e0bd1448",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCurveTwoAffine:2136",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCurveTwoAffine:2136"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveCurveTwoAffine.two_affine_cover_of_closed_embedding",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCurveTwoAffine",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b552598a23c96032247ed1a6056c51fb7cb56bb8eb8b82f8751a9a73a54f7999",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCurveTwoAffine:3498",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCurveTwoAffine:3498"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveFiniteCoordinates.projectiveEmbedding_cohomology_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFiniteCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "33dd4a6b213a7ba66393c7b8fa70914cebad8a469d18f7f34977af243b4f936e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFiniteCoordinates:3252",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFiniteCoordinates:3252"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveFiniteCoordinates.projectiveOver_cohomology_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFiniteCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5f27b94645e5fe6f5d1a225528f4b4fb760d6c76f5b7ac72df308fd8c2e5376c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFiniteCoordinates:3822",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFiniteCoordinates:3822"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveFiniteCoordinates.projectiveSpace_cohomology_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFiniteCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6046d677edb2ebd3f6f19aedac78c109dd927d6a5502b8bcd7c290b55401e962",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFiniteCoordinates:2281",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFiniteCoordinates:2281"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveGlobalPolynomials.coordinateChartPolynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomials",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b07ccc0bdebd541294a0123d49cc08818927ce01d4fe26c8812b7497b778ee42",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomials:5894",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomials:5894"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveGlobalPolynomials.coordinateChartPolynomial_coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomials",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "685a674d968239bd4711ab990d7ebe55ce398688a009ffbcd55c4b4c60c5f750",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomials:6284",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomials:6284"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveGlobalPolynomials.coordinate_existsUnique_polynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomials",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "00275f6bb476bdada6ce1dbe9be64060176b7743c571221b8a55d1ef9f6b8762",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomials:7595",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomials:7595"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveGlobalPolynomials.coordinate_globalLaurent_vertex",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomials",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5a13918deaba2262ed11549162784b3e47245b8611ce6e2ff936c2e6a87f0e30",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomials:7054",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomials:7054"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveGlobalPolynomials.existsUnique_polynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomials",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "33555f7b3d3e50f839025735d52c77936c5bb135c4d62dc26380046a5a3d97d7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomials:1850",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomials:1850"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveGlobalPolynomials.globalCochain",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomials",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2156226cb9447591934135d5919c050a3cccfccb2764f86f194a2ca1e7a95caf",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomials:1004",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomials:1004"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveGlobalPolynomials.globalCochain_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomials",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dc2a8ab0d106e36eb064a0268d2dc5bbc3fd12b19ed4748433ddac0e8008eeba",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomials:4773",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomials:4773"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveGlobalPolynomials.globalLaurent",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomials",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e4c0d67ae9e4b614b8bccddc3d930f3f60578cf9ba300056935640bf160c8af3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomials:1286",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomials:1286"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveGlobalPolynomials.globalLaurent_closed",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomials",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "edd20cd14ed63ca54cccf04698d2902a855e4c1a3a6b6cd82772ad1691b9dfdc",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomials:1508",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomials:1508"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveGlobalPolynomials.representedRestriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomials",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4a14f625dfb6724963c61f80df58e566ef66b4492eaafb73b445a0a709ebf1a0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomials:4494",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomials:4494"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveIntrinsicCoefficientLaw.CoordinateData",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw",
      graphKind := "inductive",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3ee2e4631246ed0ada9b1e9801307e9152acb77ee002cf1656239fa4c2799f92",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:440",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:440"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveIntrinsicCoefficientLaw.CoordinateData.Frame",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0776fea2f9123a4075a9f02c73e7c29cd493d294f819a2d2fa1dbc20f9f95d25",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:1136",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:1136"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveIntrinsicCoefficientLaw.CoordinateData.Law",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0886b52c81e44a02f2a758d218e80c1e8a283c7442eef459fca5ce948a91028d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:1803",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:1803"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveIntrinsicCoefficientLaw.CoordinateData.Sections",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8cac27f79d33dc64c58642059ab674c987d90abb7fb801aff3ae9796f714c5b8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:1043",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:1043"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveIntrinsicCoefficientLaw.CoordinateData.casesOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "19143494fe73766ac42c6cb368fe824c04c9667c70150f5737733306a1e65c8f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:440",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:440"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveIntrinsicCoefficientLaw.CoordinateData.chartOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b58ca4d21225473e33d847a762f067976d16c071205470670e7a8f9f661e3b45",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:942",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:942"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveIntrinsicCoefficientLaw.CoordinateData.cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1d831497368eb47c892d1b0310c80190fd19b5983ef0c45cbc4af25afaa5f531",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:440",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:440"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveIntrinsicCoefficientLaw.CoordinateData.frame",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "28cd68337e3c9b0ff048628f40e93a9a45019484a909cc6812c1e3be07a74cda",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:1289",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:1289"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveIntrinsicCoefficientLaw.CoordinateData.law",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9149b673480a0f87a63a90df51ac69d39ceab0427f656e930d2373064da6edd3",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:1962",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:1962"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveIntrinsicCoefficientLaw.CoordinateData.mk",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw",
      graphKind := "ctor",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0a34f5b239892bf04679b2f5ad43e41f60dc7585c7afda7a36d48134f3cd3c6a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:440",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:440"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveIntrinsicCoefficientLaw.CoordinateData.mk.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3dd6f25ca9f92f0bd9b7ecfb0564c4f01de8b555b6ec31ff92c2ba4fad3d89f4",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:440",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:440"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveIntrinsicCoefficientLaw.CoordinateData.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dae9f27281e72c2b77cf6246cda970e250db38ff001645183530d215e25dc448",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:440",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:440"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveIntrinsicCoefficientLaw.CoordinateData.polynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6eee4d873c2506a8474f6c5cc2675afd66c56442ad4b21bd956349bb65cb43dc",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:1575",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:1575"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveIntrinsicCoefficientLaw.CoordinateData.projectiveIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d1be33a8407bc4396bb4d53fe24d4887e515e61a5fb3e891fb861844af51aafc",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:440",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:440"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveIntrinsicCoefficientLaw.CoordinateData.projective_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "683d3c7676724e3c0fd89105d4e1d06c5fb2148333623d6acb55a510b971b3ae",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:440",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:440"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveIntrinsicCoefficientLaw.CoordinateData.rec",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw",
      graphKind := "rec",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eca21d0f876f0c620cda09a93888302b139b9810cafedf6bbd384f64b01a0b2c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:440",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:440"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveIntrinsicCoefficientLaw.CoordinateData.recOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "de041388a66586685513a542a126337c23163e17064c00861575844c2fcf3e7d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:440",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:440"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveIntrinsicCoefficientLaw.CoordinateData.ringEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "60575088e38d3f8f4160064461b59ba625679c54b61f9e52ba01903f25e64543",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:1376",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:1376"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveIntrinsicCoefficientLaw.CoordinateData.scalars",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b01cd51b79b8eb05aa49f21029452a032efe1359423e2b60550615fd885fc0bc",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:440",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:440"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveIntrinsicCoefficientLaw.CoordinateData.scheme",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "af82ebac33f9014f8447ef0870c6c88d54b24d6ceb86bb5a9af48a048279ed0d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:440",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:440"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveIntrinsicCoefficientLaw.CoordinateData.sections",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c4bb0798381e2160fae8e1a10a86046dad27787e63f0130534d1b8262a3e48cb",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:440",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:440"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveIntrinsicCoefficientLaw.CoordinateData.sheaf",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "12ac126c74d4f2e7331e0d3b89570480c1fef530f0164ae5c7eb6aa60e8943e6",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:440",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:440"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveIntrinsicCoefficientLaw.intrinsicBundle",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e8e32476ff83972e223921f12f659d2c4c16096ac405dcfc14369177bffeec91",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:3001",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:3001"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveIntrinsicCoefficientLaw.intrinsicData",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6d41849752fd042443e9f3924d2069b34e67d4c12d70f78cb0f58e4e53a54367",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:2576",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:2576"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveIntrinsicCoefficientLaw.intrinsic_law",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d867de594674e42a0718381745574c9229baf63bcbc11d63f5707ed5e985b5ba",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:3935",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:3935"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveIntrinsicCoefficientLaw.intrinsic_polynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "63aea874d39db32311f769429c729009795294b4fee649520bfcb65c8ef8d1c7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:3411",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:3411"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveIntrinsicCoefficientLaw.intrinsic_ringEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2d3188e337fc7f8b50eb498b1f3b14883058d5e5a89cc8908f2011e2a7369895",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:3602",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw:3602"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLatticeOrder.exists_frame_coordinate_orders",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLatticeOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fd1efad60c356476bb7f7ff59a8d031c0768b50e4df70cdba02a3ac10f31579b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLatticeOrder:1858",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLatticeOrder:1858"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLatticeOrder.latticeCoordinates_order",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLatticeOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7ff5b82473cbe93970ceb4db826f6fad0e748b9f8beee5123dbd48be3676b7d5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLatticeOrder:624",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLatticeOrder:624"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLatticePullback.latticeCoordinates",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLatticePullback",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "34d979f0cc057b8157e3bc7c555be79ec44634b0da3fc8e8a7ff4f2debebeff1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLatticePullback:604",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLatticePullback:604"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLatticePullback.latticeCoordinates_self",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLatticePullback",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f08ae354395ef6211739d28d477cb5bef5bccb180bd1943295ae67aa90d3f1e8",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLatticePullback:914",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLatticePullback:914"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLatticePullback.latticeProjectiveMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLatticePullback",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7bffc251a90e94e3e6b166f4a9261eb78303c2562599c776b1051ad2712d71a2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLatticePullback:1304",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLatticePullback:1304"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLine.affineChartCover",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineReciprocal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "75c55340daf17dfaeb9a9ae155bf6d013a8fe9e5d53a9848743b799bdc352949",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineReciprocal:3705",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineReciprocal:3705"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLine.boolChartVariablesUnique",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "052eec3cee58a90a49026bdbe30ab6b47cad0b78921b0044574e9a0499b0e0d4",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts:418",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts:418"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLine.chartMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d02311508c6d08e68d3a51cd0b9a757ebd691232255a63292c1ad68db4496b32",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts:2443",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts:2443"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLine.chartMap_cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "21772e86c84ddd75b561ecc8bc97900b25d5243a64406d1fc71ae08a46b499d1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts:3460",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts:3460"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLine.chartMap_eq_fromUnitCoordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0967b71edbb6cb316f1da6a1542a2bacbff42b51de44ab2cde0b5ee624b74fc1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts:2968",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts:2968"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLine.chartMap_isOpenImmersion",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c347fc61efc1b2fa1012bf7b26592cd28ad99f322063ec96080981a91123f5a0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts:2844",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts:2844"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLine.chartMap_opensRange",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5018abd8a0c247d55c19f7bd18705348c8d3bf597f18b8534ef52c5068ae9084",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts:3231",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts:3231"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLine.chartMap_preimage",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c1889f44a8d78e2530dbd731831434d66dd14d907b67186e9334afd994619865",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts:3604",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts:3604"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLine.chartMap_preimage_other",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "befb1dbaac14cbd95ae96183c8dac06f2cb3f2e74b3ecd2113d66ad3caf23d72",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts:3973",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts:3973"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLine.chartMap_structureMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d4b0cafd43bf94608116c0ddf1edb3f28b117b097217d94c7fd78980f686fbd5",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts:4219",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts:4219"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLine.chartMap_structureMap_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3463fbc3c73584354261b95d535c3709300ea183534984cde922b1c3968d8708",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts:4219",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts:4219"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLine.chartRingEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "57230f8d1edd07b84811946a5d59762204bed2d185331f2af31a9a78a7900130",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts:1125",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts:1125"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLine.chartRingEquiv_eq_evalAway",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ada81c731a8970fb38ca4d10fc43fa3ec3c7702e28333b22e9fa48d6d7382670",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts:1718",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts:1718"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLine.chartRingEquiv_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e78030af266f48344eed6ca80c65ffe6848e68e3811a513a70df24fe7f2e90e6",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts:2682",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts:2682"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLine.constantsInDegreeZero",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineProper",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1b3c49795462e5fd69120f60df6780065a0d2579b0767cff78f3b0fe36def7c0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineProper:419",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineProper:419"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLine.constantsInDegreeZero_bijective",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineProper",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c82969ee65953d299666d53975991b5a56eb649c0628710c549f7b0421a17c43",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineProper:842",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineProper:842"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLine.constantsInDegreeZero_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineProper",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0a87eeb492098b5919faced5c4a6d3b81be8661d56d140a02c7b3ded8b0a48f5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineProper:1517",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineProper:1517"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLine.degreeZeroEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineProper",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "65296e3b98b173b04fc89f5ce60afc13df5899f60a84500832862c96397f86b0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineProper:1318",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineProper:1318"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLine.infinityChartOverlap",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "59135afa9b3c8b083524935f8440bfe31e50714f0c4467d400ecce2f7ca4ef70",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent:2000",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent:2000"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLine.infinityChartOverlap_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3cd5be1c67b8c727b4615fd3da5e9ff97f4f005d22eba06742b32d7dae2f395c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent:2181",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent:2181"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLine.infinityChartOverlap_isOpenImmersion",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d761060bb73df032906ae902e5b691a387c854c36ba307fc383346b508809864",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent:2626",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent:2626"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLine.infinityPolynomialMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cee9b50dec902d5a174bd50939cec5e260bfc5634f62d3f316619fbc69d22929",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent:354",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent:354"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLine.infinityPolynomialMap_C",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2211eb240413e889b6b199b76c262b6a993051b519ae3f48e70cd9f348c6c056",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent:789",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent:789"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLine.infinityPolynomialMap_X",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "070ec4a7cc31b63048d7afe3cf7f5763accc1f7f138e0b64e11144de47e422be",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent:950",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent:950"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLine.infinityPolynomialMap_eq_invert_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "be9d71a8d285da98cedf1344c866eb207338c7afad81bc98362ab7d7d72fbbdf",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent:1102",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent:1102"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLine.laurentInversion",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4fdf0f245171e8212f7d2a8394f9e798584d132fba120c3790496c2bb1fd65dd",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent:1336",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent:1336"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLine.laurentInversion_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2c11c17ce40d5ba3266f187ec326d2a593618f09c550304b2adfae9caad402be",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent:1547",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent:1547"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLine.lineEvaluation",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7c2aefbba0ad39e59e8012b3661acd73446f7b7b9b94ca72f92a68b7c6202692",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts:654",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts:654"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLine.lineEvaluation_C",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1025e2cebe39b5136887958b9935ca72f380b5ab8068b8106e50b327a79da1e3",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts:977",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts:977"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLine.lineEvaluation_X",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f8862c41245bc5758a69aea73e52a379d7737842bf58cf61badfcd3b902a612c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts:816",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts:816"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLine.projectiveLine",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineProper",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c772cc18fea5acc1d7500533a6deff8b29eb1f9e8640c34f9589b93d2183043b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineProper:301",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineProper:301"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLine.reciprocalChart_compatibility",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineReciprocal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cf2fe1d5f31a14378d02fe8fa24603204eb92b7efaf41ea5cf89dc6391cc5d13",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineReciprocal:1893",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineReciprocal:1893"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLine.reciprocalChart_compatibility_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineReciprocal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e6f1f6cbc304238243411da6846dd39a6ca3cb321752177cdcf14ec4ff599ca0",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineReciprocal:1893",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineReciprocal:1893"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLine.structureMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineProper",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a2350fb924277894f7133853db92849089714c09ef7dc1e58065ddedf8d02fe3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineProper:1695",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineProper:1695"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLine.structureMap_isProper",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineProper",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "35aa0833e2540c4f13b7fabed0065218864e3d6084244f5493c46b654fca107a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineProper:1922",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineProper:1922"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLine.unique_dehomogenize",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6afab379b3a90e47335716bc1be01e0c92d9bdef5cf1d89dccb33044bf7ccbf5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts:1305",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineCharts:1305"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLine.zeroChartOverlap",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cb9c415da66ba71e65c975346bde471816f77501e602ca54542b96fb96b8f9a4",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent:1827",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent:1827"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLine.zeroChartOverlap_isOpenImmersion",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7b29b686acd58b6cc2f7a493ede63ca3a1bb923dc19e7ba096b795c3d12ade3e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent:2445",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent:2445"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLine.zeroPolynomialMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d639e4000f4c1a3c1a0c6732a1e70da07e835eeaa78c49f59f31f0d08d472c9a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent:261",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent:261"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLine.zeroPolynomialMap_C",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1f920131a8d0fd7bed498de321934af2395077646d0eee30db884d39861a337b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent:503",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent:503"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLine.zeroPolynomialMap_X",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6859827c8021f1cfce89935df484ae32929fd4afcdfbbb3f57c6e6c42f4598d1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent:652",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLineLaurent:652"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLocalCoefficients.chart_inverse_ratio",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLocalCoefficients",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "27592e7ac2cfddbf185b0c57592b018b24a0aa31c35edd027d4f04a809dc631b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLocalCoefficients:954",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLocalCoefficients:954"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLocalCoefficients.exists_frame_coordinate_coefficients",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLocalCoefficients",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a11b0a46f3e112163537c22d5234bd3aafe0f7764f40ae75b2cf88f4fc5ceed0",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLocalCoefficients:2055",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLocalCoefficients:2055"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLocalCoefficients.normalizedMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLocalCoefficients",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "26301e687324853111e43c9b863a3f1d712225c671febad8a725d3814d0d87e2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLocalCoefficients:663",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveLocalCoefficients:663"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLocalCoefficients.normalizedMap_natural",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveGlobalMonomialLocal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "11fbfd246377d16b4ecd240896ec5f27a36911db7a645a8d6f538ef37eaefbe8",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveGlobalMonomialLocal:571",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveGlobalMonomialLocal:571"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveLocalCoefficients.normalizedMap_scale",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveGlobalMonomialLocal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8cd19f35de8ec0ca22bbaa7b7df12eefa8391bb1f721631921cc2c3ab86090f9",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveGlobalMonomialLocal:938",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveGlobalMonomialLocal:938"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialCech.Laurent",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0de044fccc58ffeb55b5e0f9266c6d6d5ed988ca2b4dc9238bec61bf38141acd",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCech:441",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCech:441"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialCech.Monomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e5d353d3b8f6673e792cc603a2b199721132d56d3a05dfa6f4044379e8eed648",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCech:348",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCech:348"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialCech.RegularOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "286af8200827bb7a83ad9e250fcf742db117ddf1edab4fa081b5d74cce1c4022",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCech:535",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCech:535"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialCech.exists_nonnegative_coordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a288776525a1a5ae8df7d663d9d60c6c7864afc11671df70636bdfb1345a7126",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCech:3065",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCech:3065"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialCechHigher.Cochain",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c5dbf3e10dd8dfa04b20af4736ae8dac55ebcf3b738faaaafc75e7c2f935f6af",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher:416",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher:416"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialCechHigher.Regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e5d771fa18eda0d63bfdb022f8eacac3a075a1f38db08feafa6457f057bc44c0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher:2823",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher:2823"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialCechHigher.contraction",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "98832301af37987cfa699dbb0a0226f23032ee880ac21080b15113be96155860",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher:3174",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher:3174"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialCechHigher.contraction_identity",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "908dac9a158b65ecfe87274444a39fed72f13cd126b85ec5963ec5d96859db34",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher:5474",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher:5474"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialCechHigher.contraction_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "464baffd5872764f9eb5096ccb7a510c3e6f95f0b10aa1340f6ec1fc1b3f7dd1",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher:4094",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher:4094"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialCechHigher.differential",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4d679d9fa18368166af9fe8e87d3495c07bd396e198ffe1065b8e61e13722458",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher:489",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher:489"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialCechHigher.differential_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bf793500f24c7abad7d0b03fa8c74d472c98e133a27d976d860b17c1a4750cd1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher:4659",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher:4659"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialCechHigher.differential_cons",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b5216f9f444816a1c737bfa9c4bbb64330f6538c2992ae17452c1a06a5dcbb9f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher:644",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher:644"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialCechHigher.differential_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0c0f9d20614c7ff824031797740a074b4708c5c9f0a8dc7bf75c8294d163cbee",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher:4934",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher:4934"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialCechHigher.differential_squared",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "35225c1687b80390f00e20d9664f58538357813153db05670cc723ece0a75ff2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher:1800",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher:1800"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_022.jsonl"
