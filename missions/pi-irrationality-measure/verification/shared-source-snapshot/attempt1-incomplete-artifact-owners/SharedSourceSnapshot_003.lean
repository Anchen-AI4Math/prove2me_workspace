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
      sourceName := "OAI.PiExponent.CommutingTaylor.taylorSeries",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b6982a73f33321ba1a742bb266685d58051ad087b0abbea6f845cffed0c48d0a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor:2312"
    },
    {
      sourceName := "OAI.PiExponent.CommutingTaylor.taylorSeries_mul",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6291d146d0d86b15f80d79715ecb144e54967a47fceabd93c7784dafeb3bb975",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CommutingTaylor",
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
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetIdeal:374"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetIdeal.image_support_isClosed",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e8cfc3cc7df904f17f67448d7256711244649562101adacc8f573ae707d9c4cb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetIdeal:1319"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetIdeal.restrict_eq_top_of_disjoint",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0a713148b4a17e5ab08db141d8bcf93bee0ae1e902e81ed920e44f0cb95fa558",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetIdeal:2509"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetIdeal.restrict_extend",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "408582dedf0b447aa6d90f5bbe78605488fc729868981c3f04f137b0e2bc89a0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetIdeal:455"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetIdeal.section_isClosedImmersion",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e6e4d22c1acb07091da4877b4b0eb01a9299d0209aa27d3ccefef9b81f71832d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetIdeal:1069"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetIdeal.support_extend",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bb9ff09f857f432b26f373149cbd46eaccea66e6348a28dd53025f7bc6521ca9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetIdeal:2011"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetPolynomial.aeval_coordinates",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dfa550ce5c2e4be638cd85396c64dbe0dd4ce50d02d387894686de8d3cb5bb67",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:8765"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetPolynomial.center",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7cfed9d6477f0f01f90fb1c7e3f68c25c612d50c918bbcf50babfb9a5b98c8df",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:394"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetPolynomial.centerPoint",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d32b879251e433548dcc7d3a28e9053b3c1f5441718bde68330e83ed2ce3785b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:3379"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetPolynomial.coordinates",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fe36040af5ba2097bbb44f2850005a74db8b420e6182ce010b3318c7fb082e49",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:461"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetPolynomial.eval_center_inverse",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7d4a342b7baef8908421cdbe1050140d6f5cf07dc7564ab2760de86a090e5d0c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:806"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetPolynomial.logPolynomials",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a73e6c015b35567e32b71f6943332785d659ca67c84aeb4f95c617d95d69e5e1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:4958"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetPolynomial.logPolynomials_eval_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2633dacd61a36d0e558c865858724571bbaa239da6c9f4a3490ebe5cb1e22cdc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:5088"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetPolynomial.map_powerIdeal_aeval",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "83fb18019015e23ad8540f1c5f8182ccb6f1d9da9de64f0c87f343f7f067db15",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:9459"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetPolynomial.powerIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "53d75f4bb1fd9cca48490ec83495438c3757741a51a6f3d56dab5e595645e824",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:611"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetPolynomial.radical_powerIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "12881a76af2dc64504cbc4bb851719436f696c2549464360ea496be26cd3090b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:2483"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetPolynomial.span_coordinates",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4148041017953b9a2040d5d7e31fafb93cd0bef8d92cb4a4082294433b1eefcd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:1379"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetPolynomial.zeroLocus_finset_prod_powerIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "444f50a5e0e8badd11251b4c13f4476089bd61edca1bdadc4872e1fecb1e9d90",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:3892"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetPolynomial.zeroLocus_powerIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1d97de20785dcba1380eaaab86abe26b7b162ccb5e92fcb5431b049391542ad1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:3525"
    },
    {
      sourceName := "OAI.PiExponent.CompactJetPolynomial.zeroLocus_prod_powerIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "13c86cf0f823a5315bdb07c0cf34ec3dcd7a40687efceb9a2fb167b498dfae54",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial:4521"
    },
    {
      sourceName := "OAI.PiExponent.CompactLogJetIdeal.affineIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a95ea5b78d261709f278acb3cf80f0055a91a7863e2d5a80fa9bcc6c73662668",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:2268"
    },
    {
      sourceName := "OAI.PiExponent.CompactLogJetIdeal.affineSpace",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6a989e856438321d1508e4f7f076cfb1fa5dee6a73079e9777a4eced92df3029",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:453"
    },
    {
      sourceName := "OAI.PiExponent.CompactLogJetIdeal.base",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d2c92a9bac51cee435c5a537a554e81b4e72e2e897cef63b90fcfc80832362cf",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:536"
    },
    {
      sourceName := "OAI.PiExponent.CompactLogJetIdeal.compactIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "93d4277a9a02697ea68cf9a4e448af1ad9f792c43cb97addc1e9a6de5c6e9728",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:3157"
    },
    {
      sourceName := "OAI.PiExponent.CompactLogJetIdeal.coordinateRing",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6a30a7f3d3d62c8d4a9bde18f0d8e0a1120a18361cf5549ba85200f8284f5925",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:388"
    },
    {
      sourceName := "OAI.PiExponent.CompactLogJetIdeal.point",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "07665ac7c7b9c6fea38bad1bc002dde54ff71def8b97b6b80e84faa3be6d81bd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:715"
    },
    {
      sourceName := "OAI.PiExponent.CompactLogJetIdeal.point_section",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aef13bbc5086c619d3f70dd0d1f36250d0fed46d8308f9113de1444d10755639",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:850"
    },
    {
      sourceName := "OAI.PiExponent.CompactLogJetIdeal.polynomialIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ac584cc8cecb2f833caa4725654d78d6e9d4eb2fa0d204ef2c5f7320b5d16c74",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:2068"
    },
    {
      sourceName := "OAI.PiExponent.CompactLogJetIdeal.range_point",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "67c0a3cb62da53870f9a91e59a1a356e0b24669637ff8f24056b5e9b1b34ffb4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:1230"
    },
    {
      sourceName := "OAI.PiExponent.CompactLogJetIdeal.restrict_compactIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2077b7de38d754485845489accaed5b48dae3da61726463b4c9ec43464291575",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:3390"
    },
    {
      sourceName := "OAI.PiExponent.CompactLogJetIdeal.structureMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4fd57724e7ba40d13b3e420380af33f1fefbdf7168da112f720431fdc194acd7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:589"
    },
    {
      sourceName := "OAI.PiExponent.CompactLogJetIdeal.support_affineIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cf3cf53d926cc268069b5e403d84949712354c057aaba0c7c9ab33a6ec2a6796",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:2492"
    },
    {
      sourceName := "OAI.PiExponent.CompactLogJetIdeal.support_compactIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c420c9ed44768d4a0ec2f74e2493d0ad1145719aa1503442833b10aa7828961c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:3703"
    },
    {
      sourceName := "OAI.PiExponent.CompactLogJetIdeal.support_specIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7ae92155243e5e71cc3d3c9cf193b02a81a708ae76e143481049c788288edb47",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal:1591"
    },
    {
      sourceName := "OAI.PiExponent.CompositePullbackCoefficient.exists_frame",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CompositePullbackCoefficient",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "75e9fdc168577faa863ba685cd36cd3db3ecf59d1d1438f712add420bfb988d0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CompositePullbackCoefficient",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CompositePullbackCoefficient:271"
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
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ConstantPullbackDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ConstantPullbackDegree:1208"
    },
    {
      sourceName := "OAI.PiExponent.ConstantPullbackDegree.pullbackFrame_of_range_subset",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ConstantPullbackDegree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "45630a9b44806598147009db8bd93e930f567819401764a8e539f7542e2abfab",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ConstantPullbackDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ConstantPullbackDegree:440"
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
      sourceName := "OAI.PiExponent.CoordinateFiniteSlice.coordinateEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b217190cbc75ad31d58f293a8458846fde24dc7f0b5b151f701c508d1208bfe5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice:376"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateFiniteSlice.coordinateRenaming",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "da9e4b51e0ad6739102b2088175e0bf48a7fb4dc57b38327db311850e25beecc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice:839"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateFiniteSlice.residueCoordinates",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "583ea0b9e140321076963b5a794ba1621d80986455164850b7f9a53919479604",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice:4583"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateFiniteSlice.residueEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f9e8db2d919b0576c92b100cf25b59a99ab03255e3a73edef83aee6e6f8ae1d3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice:2096"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateFiniteSlice.slicePoint",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "65d86fb1a188143b714a5fe2676d63e9dc96ac39459da68a324b66c32769aba3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice:4750"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateFiniteSlice.splitPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "640916fe1b4263a30da67e46ed6e26b2295642305cdf2aab53bbfa9e80d41780",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice:1735"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateFiniteSlice.splitPrime_isPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e9b504dd83e6ad4b40f53560cc5e1b3d25c69d0d7e83e6659d2d65dce111c765",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateFiniteSlice:1920"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateSliceComparison.primeLength",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoordinateSliceComparison",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7b421796e3acff08975985370ace68c6d2550160809ec7227cac948b61d53947",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoordinateSliceComparison",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoordinateSliceComparison:512"
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
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:562"
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
    },
    {
      sourceName := "OAI.PiExponent.CoordinateSliceLength.rationalizePolynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0c73b97f7704166eaffeaf42044e61d0eb58947f5319c4fa972a89850d290438",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:1161"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateSliceLength.residueSlice",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9b93729e2e91f1df5ae3e41ed5114d4c25e4b90c514613b96746963fe135910b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:7892"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateSliceLength.slicePoint",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e76544845cac0594a369ce22a9ce82645fabff72cb467a882a0754e421d6a7ca",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:7735"
    },
    {
      sourceName := "OAI.PiExponent.CurveBlowupImage.blowup_restrict_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "badba0be15a8a9c41f4b711151baa6411adfb212a3d3569d98758f457adb92ae",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage:4705"
    },
    {
      sourceName := "OAI.PiExponent.CurveBlowupImage.exists_image_outside_closed_points",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveImageOpenLocus",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1db0b1a3073eb41470e05067472929b4ba26ca436902a3a37b5d393fb8d8a285",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveImageOpenLocus",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveImageOpenLocus:1243"
    },
    {
      sourceName := "OAI.PiExponent.CurveBlowupImage.functionFieldIso",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.OpenIsoFunctionField",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a234774dbc712ecb012ea6b88a5b920ff972e64647029be8be9b0a4e7f66840d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.OpenIsoFunctionField",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.OpenIsoFunctionField:950"
    },
    {
      sourceName := "OAI.PiExponent.CurveBlowupImage.functionFieldMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.OpenIsoFunctionField",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e6ea89fb93c42e27d3c1aaba3dc168ce1b791515b0d43375046ff76acae07552",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.OpenIsoFunctionField",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.OpenIsoFunctionField:267"
    },
    {
      sourceName := "OAI.PiExponent.CurveBlowupImage.functionFieldMap_fromSpecStalk",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.OpenIsoFunctionField",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ad74b774a01bf416bc13b25ccc7775447dccf1b518372eb56ebffa3a738129e5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.OpenIsoFunctionField",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.OpenIsoFunctionField:1412"
    },
    {
      sourceName := "OAI.PiExponent.CurveBlowupImage.functionFieldMap_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.OpenIsoFunctionField",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "984d716d1651898dad38b6553e6999b7b62c19cb5238aada29d7470753b02c29",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.OpenIsoFunctionField",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.OpenIsoFunctionField:489"
    },
    {
      sourceName := "OAI.PiExponent.CurveBlowupImage.genericPoint_eq_of_isDominant",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImageBase",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0ee5492093382ad175610a60cc44d2f5ed71378f6843066138dddf53f59f832a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImageBase",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImageBase:2956"
    },
    {
      sourceName := "OAI.PiExponent.CurveBlowupImage.imageCurve",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "283febd31c7e7ba1f75af97b9385e1dcabc880ea1df3fe784dd4dcdf9105bc97",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage:473"
    },
    {
      sourceName := "OAI.PiExponent.CurveBlowupImage.imageFunctionFieldIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d0795ac5365b15d17999c174affe8d63d13412b16d3748f590b47cc1b7777635",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage:3421"
    },
    {
      sourceName := "OAI.PiExponent.CurveBlowupImage.imageFunctionFieldIso_generic",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "423954a01e30aefe8938eb455769aa1699661b9a71aee3fd98be575217546755",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage:3942"
    },
    {
      sourceName := "OAI.PiExponent.CurveBlowupImage.imageMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9345b60400432ceb26a8a243b8ce9f9a1fc961b340d974994a62eaf14cff8945",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage:970"
    },
    {
      sourceName := "OAI.PiExponent.CurveBlowupImage.imageMap_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d1038db724c0c1db59419da49430925e4bbc9c154744c4c2df67d038eaf24fb6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage:1206"
    },
    {
      sourceName := "OAI.PiExponent.CurveBlowupImage.imageMap_isDominant",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3ef1052b4df9b7a25a87aa96e8cd83d9449ef0891596bd50c7cbf541013cb7a0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage:1729"
    },
    {
      sourceName := "OAI.PiExponent.CurveBlowupImage.imageMap_isProper",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "59ad24c6a1f48766fe556248ab8dcad89381167dc14b0f2075c917491a3ab7fc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage:1502"
    },
    {
      sourceName := "OAI.PiExponent.CurveBlowupImage.imageMap_preimage_nonempty",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "988e78af7e5baafa858104cb356e49d3cae7f5fe52bbfbf409595b84286fff0a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage:2886"
    },
    {
      sourceName := "OAI.PiExponent.CurveBlowupImage.imageMap_restrict_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4b197b12df8f022054fd7d3dfd0c9277869b6ff3d2c96652e3fea873a804159d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage:2478"
    },
    {
      sourceName := "OAI.PiExponent.CurveBlowupImage.restricted_curve_isClosedImmersion",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImageBase",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f1daedd3c180268dc88c368a03ad3980526dc6d626c07453aea5f17846e67d0d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImageBase",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImageBase:2647"
    },
    {
      sourceName := "OAI.PiExponent.CurveBlowupImage.stalkMap_isIso_of_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImageBase",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "326ad5cc276acd8a31a95e6eb012d4c077895bad3b91ce31fe52c903b4f7332d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImageBase",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImageBase:3272"
    },
    {
      sourceName := "OAI.PiExponent.CurveBlowupImage.toImage_isProper",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImageBase",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "776ab11e22fd4c994baa6065f3522765503f9fa2f9821d4735bc994566a9a19e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImageBase",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImageBase:1608"
    },
    {
      sourceName := "OAI.PiExponent.CurveBlowupImage.toImage_restrict_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImageBase",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "40074ae2592d456938d666c16e5db9f94b859dfc10eee4fd1655c7bc5f12c267",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImageBase",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImageBase:1825"
    },
    {
      sourceName := "OAI.PiExponent.CurveCenters.Centered",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f483da26020d0aa6b35e623bb987c94d8be256e131fe8807785c88219697e16d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters:289"
    },
    {
      sourceName := "OAI.PiExponent.CurveCenters.Centered.coordinate_nonneg",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bb13c13d764dd9297b4b3864c8106433bf737f716b36d2f99b4fb401add73a9a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters:4241"
    },
    {
      sourceName := "OAI.PiExponent.CurveCenters.Centered.exists_nonzero_difference",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "adf08a5346149cdad265af63d73fdf8da53a72c9f106028a62633d82fb7be4f5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters:5000"
    },
    {
      sourceName := "OAI.PiExponent.CurveCenters.centerPlaces",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "05c80770a3764b1041a6dcf59862eb7c463e12ac7501da3225b1c5189e6ddfa2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters:2527"
    },
    {
      sourceName := "OAI.PiExponent.CurveCenters.exists_transcendental_coordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "349018a9161035fb26e16bac0b099d16a964f13d636285117ff086606ff258cf",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters:667"
    },
    {
      sourceName := "OAI.PiExponent.CurveCenters.finite_centered",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e60bc3d7bcb943eeb1d69c753bded61770ea25566e3e27f47fea427d04ed9dcf",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters:1453"
    },
    {
      sourceName := "OAI.PiExponent.CurveCenters.finite_centered_family",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c4b05cddbeb00308d092f75d5aac88f0b0417e2131b2779bd353401fcf920b0d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters:1969"
    },
    {
      sourceName := "OAI.PiExponent.CurveCenters.mem_centerPlaces",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "197790b42ea6315697646d43e3acddb03a68807e7030f9e4dfc2f352b91690aa",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters:2848"
    },
    {
      sourceName := "OAI.PiExponent.CurveCenters.transcendental_sub_constant",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "57a225ce91aac6409a5b9d8d22443d9009148ab235a04b1ccadcebb591afa17f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters:432"
    },
    {
      sourceName := "OAI.PiExponent.CurveComponentRigidity.NormalProductComparison",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentRigidity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bb9f1420a2313daf6628586dcd506abeabd856f5833f57a330b61b6a72f61b79",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentRigidity",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentRigidity:673"
    },
    {
      sourceName := "OAI.PiExponent.CurveComponentRigidity.PersistentNormalComparison",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentRigidity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8078dff71b12d6dc45e432e39e5c2c9c76653f21f582af14b97a63991e6ae367",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentRigidity",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentRigidity:1305"
    },
    {
      sourceName := "OAI.PiExponent.CurveComponentRigidity.coordinate_constant_of_persistent_comparison",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentRigidity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "298f87e7ee58dd18d8144792b8260609c7a88a5e4834a032c53382c345947922",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentRigidity:2092",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentRigidity:2092"
    },
    {
      sourceName := "OAI.PiExponent.CurveComponentRigidity.residueY_ne_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentRigidity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eb21868b4590978fbec7e559e75a9235d100dc2707a2dea8633ab1ba5f3ac79d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentRigidity",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentRigidity:400"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactFamily.center",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "978986751621facce68d3ec5c8ecb8cc06329119ff0e193f514ef3886d448f31",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily:1578"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactFamily.centered",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8252bb53551c4ef65564f88c9541f808f7b5a1aa166bee69a9df41b2970691fe",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily:1945"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactFamily.contact",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "12ea61042aa09eb68ec3843111749f9da3a755cb4ae1f55c04557bf95b2694fc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily:2609"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactFamily.fibre",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9845e96dfca104e1011ce11af05906f0205238f51650fc100c9d92cd087c8998",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily:394"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactFamily.fullCenter",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ad952cb9062a7e2f2259927b4fbdd1bc27655b6d3444a1975ddea53ffae5fc39",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily:319"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactFamily.mem_places",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3d087dff3972a34f0a46e6d951d1a6063a15aeb2cff3b4b527b12fece18a1bad",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily:1151"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactFamily.nonconstant",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6653ff20c6b35009ac0a3d900f92d9de894511eb8687839fa3152e6b8a00b897",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily:2381"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactFamily.places",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "180057de50257c67495fe4e8e09c7cf7bcd98a0d89965bec86e45132cb6df469",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily:828"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactSum.contact_sum_le_of_principal_sum",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b46ae493c999d4d229a8245de008b8e2a6e6625558fdd660484151508cbb42e9",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum:522",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum:522"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactSum.coordinateOrderDivisor",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "661fee3c1cdf608165167d0f01dd272a375b6225247b26d6c8be338a1565e1cc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum:7173"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactSum.coordinateOrderDivisor_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8e9688acb978a937469a6aa98f18b2c1008eb3acbea1f6fef6ac1cecd91642f1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum:7542"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactSum.coordinateOrder_constant_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d289c89c2fffb3f1bb2a622df63369c5ce2558e0bdc53315c7e4a1b7bed48c43",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum:6734"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactSum.coordinatePole_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "690a68a404d82e835268f3310c1e18fe37ab2850c7e78bae47de97f10586ab40",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum:2810"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactSum.coordinatePole_finite_support",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "795e623733ad20208d785ee9045714f24225d3a366672e2264f11fe822b9eeb4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum:3287"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactSum.exists_constant_of_isAlgebraic",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "688365640b45bd2e21137e7b6ab9bf2e0f29c2bc71e728f1821e7da1ebf6554b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum:3866"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactSum.weightedDegree",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "be759ff660420d017076c15102792276c3d3527b9a9cb516a69a72cebd5c7204",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum:9717"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactSum.weightedPoleDivisor",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "50079b77ad5525eebff3c2d3fc67edc74a4d57850623e03747bdce560bdab4be",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum:8758"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.componentEulerDegree",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveCycleEuler",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "04edf66181fb7914fcf26037665744db6e9f62e3105d09b0d4712f3e75fb3296",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveCycleEuler",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveCycleEuler:397"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.componentIntegralCurve",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentsDimension",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e97597db44e9137ae7927c0a0e9f417ba3b7c35f81bc5bc0134601937e2573c8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentsDimension",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentsDimension:898"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.componentLocalCutLength",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentLocalLengths",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4317e47b1680b12389678e513dfac93576fd7989b4f9b0d2a3ca2e708ea68443",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentLocalLengths",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentLocalLengths:958"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.componentLocalPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentLocalLengths",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fbc579499ef1bdca40d209328ac2a5f51577bd8ebb7d915d966cc19e7d5528db",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentLocalLengths",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentLocalLengths:750"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.componentMultiplicity",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentMultiplicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a4ffe4f68d682f3a8da22ceeb2a92b33248c2fa120685cc882f70f02f22a0e2d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentMultiplicity",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentMultiplicity:1677"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.componentZeroPointEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentZeroPoints",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "36d949be6bff160a3eaac0acaf04b65fb31bf12956a80262e7d3a54e3b4247b4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentZeroPoints",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentZeroPoints:1628"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.componentZeroToGlobal",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentZeroPoints",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d6fb60b388756297406d265931fdd77d5defa4cbd1d414cd885688071bd837b9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentZeroPoints",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentZeroPoints:438"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.componentZeroToGlobal_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentZeroPoints",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8021b923b243cbdc2aa426fa78ae12723717a3f717d716f460fe37cf3d4ef010",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentZeroPoints",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentZeroPoints:1254"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.cutQuotientEquivOfSurjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveCutQuotient",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "97ec14f326286eaaeb9f193e9027c43884e18e863b91dbe28b711f1705ab00d5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveCutQuotient",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveCutQuotient:262"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.cycleEulerDegree",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveCycleEuler",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b441af2a6919012074230b8dceb4a2d2ba3ef2f449bdd5118c783414b93c872d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveCycleEuler",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveCycleEuler:746"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.exists_pullback_frame_sectionGerm",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RegularComponentSection",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7144a77905c860af52bd22504881203c28a5d8955a0bf8f6ad7209dcfcd94b4e",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RegularComponentSection:667",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RegularComponentSection:667"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.finite_componentZero",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentZeroPoints",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "df0f5ac757b7848063be75a3e3ee5cb13f3caacdf413ef4be190ce7f7a0ffcea",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentZeroPoints",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentZeroPoints:3159"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.finite_componentsThrough",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentLocalLengths",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4a73b00107ea369643d3204dee5980a0e838fed9ec1d9693df0fdc03cac024e0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentLocalLengths",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentLocalLengths:373"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.fromSpecStalk_generizing",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e236b7a430aa570dfe75c4407897eea2360b15e3fc1338559ef2cf2cce2b2cd5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks:3386"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.genericPointsEmbeddingEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "de4bc7a7125fb72ef101c731e4f292175ebcc55e658f5d869188284508537a8b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks:1896"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.genericPointsThroughEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f3de945468b594d1f0a47225e9b6fdc98409975ec899786a83a8bdcdd0a906f6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks:3822"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.generic_embedding_iff",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1fcb928095d1ecf147fe008cf2fdfac727115c8849c6f869ab54a836e8266f91",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks:1263"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.generic_iff_no_proper_generalization",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "db3966a81e82419fcd5658a52b36ccc2ab997ee50773e694e832bd5a7b7a9875",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks:193"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.generic_stalk_isArtinian",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6d465b94ee01d07e0d8d8c9fb9b2c07fe2f10e0213a1b10c2f929fb33681ce5f",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentMultiplicity:261",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentMultiplicity:261"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.localMinimalPrimeGenericStalkIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalMultiplicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b6e200a30dd0a222f5de27b508193f26721aa0cef75c3ebd6a828aeab0b216ed",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalMultiplicity",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalMultiplicity:916"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.minimalPrimesGenericEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d807a50cb1e12e4a853b795859e340460768ab2efcad34edcc9061eaba5e9030",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks:2755"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.reducedComponent",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentMultiplicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "168e5cd668d88a853db32dbae44a338e3a721392e24f4d74d76b68970527afb8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentMultiplicity",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentMultiplicity:2288"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_003.jsonl"
