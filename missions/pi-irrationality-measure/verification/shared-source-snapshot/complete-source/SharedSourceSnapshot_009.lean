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
      sourceName := "OAI.PiExponent.CurveZeroPole.fiberDegree_eq_rank",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b3659f922d8ad7b59b0c837b919c372aa3f750e6a3737c30de23223c26a2221d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:819",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:819"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.functionField_fiberDegree",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "23965ed947461470093287f9ae2ac39f86ceb27dc6980d850b02a0fa9db535dc",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:1679",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:1679"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.parameterAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a7488a2cc3e4e35f72334afd5076524b2dd404d94f7c2e1fcdbee770b145e04b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:3651",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:3651"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.parameterChart",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "554eba76f277e7511d87d36c7f722f2084074b64df62f86dac8f2d27a915b079",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:20257",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:20257"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.parameterEmbedding",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "69e78f1f513f647e45f560067ba18dc3af349ac4ac31f9e936481c405bf3c0b2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:3190",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:3190"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.parameterEmbedding_X",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "011524ece7ea326dd5ad45f82c00860d0f0865b827aee9db74c0cc8bdd8cc95f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:3449",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:3449"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.parameterFiberDegree",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d7eb0a91d4629f07524357dca5b969a1050cb3792ab05870ec0c972c01f111fc",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:5767",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:5767"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.parameterFiberDegree_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c2c71b61c94a6706be7dc909c304ee0e90109964d7fb8147fa6900a1991c6c5d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:6171",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:6171"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.parameterPlaceValuation",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c2b9de6969beb6edab848bd7efdded9c3f905fe01a48105166d70d3763dd393b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:21189",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:21189"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.parameterPolynomialAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ac300544d890795cbc06646061ca43fcb28564ea92daff73b17bc476ec063c65",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:4807",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:4807"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.parameterPolynomialAlgebra_map",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0234f52de28fb1a4782baa3e81255009e46c7fe09458e1a03c58dc9d5b26431f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:21888",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:21888"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.parameterZeroLength",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "51590c2413fc35de014d49dfed0bdaf6c3495fe9311dd84e7ab1e16026f3fc07",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:10218",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:10218"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.parameterZeroLength_eq_degree",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3085585bd726d851a228010ee2f0a7a7d6fdfef55da37baab2aeb40ab966a86e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:10613",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:10613"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.parameterZeroOrder",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e362567b92f532989adbe7c1ff53e5fd7e3f9443b75d93b80d1d72bf89167b83",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:18310",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:18310"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.parameterZeroOrder_eq_length",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "98967af502ce6fd200715860c388629412f11de8ade68200d69de18aa3e31ee4",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:18906",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:18906"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.parameterZeroOrder_eq_sum",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8c6bf2e56fd220528db1b10514e8befd6d257ca4aa801ef686c64c1aeddd9ee0",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:22478",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:22478"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.parameterZeroPlaces",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "17e58e5fbb7a13423db88c11fe383902d4a52884e935c52a90f498f1369bc184",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:20458",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:20458"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.parameterZeroPlacesFintype",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "356c30b280aa985e8eb31e6415357a7433d2843abff3e1cab9a4572b9fcf16ce",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:20678",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:20678"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.parameter_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9b5bbd5509fae2837c9f1fcb42e860843247e089852dada0c17233986b4502be",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:4243",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:4243"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.parameter_finrank",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d5e1f67f6c59603e260c1dff98d5268cb264fcf313b528e1ba2cc58a5fd54f56",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:3841",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:3841"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.parameter_inverse_degree_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "373a8c0dd1a9ba655bff514c169eb1d4dd5ee66b099a8da8a8ba5fb24e8001a0",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:2937",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:2937"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.parameter_scalarTower",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3e6b58bef9390a26b0f1ff7c3c87962572e4ef45670004ddf5c8b77838be7b50",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:5037",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:5037"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.primeFieldValuation",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4ccea6215d11d380716e88de8479ef984e0ce93f722913a82f4aca25a6d81ecb",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:11882",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:11882"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.primeFieldValuation_algebraMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6133b2b1c2d91a80b39c1c92294f8359d02c9feaed0de3f727db9bfe5f1e0236",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:12636",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:12636"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.primeField_integerOrder_algebraMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "54e17782c9df7c00d1253aef477fc73c63fdbb84d8deeca814e680a2dc63264c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:13930",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:13930"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.transcendental_inverse",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bd9ed53df00d9987036031a20b3ad3c01fa5acdee0b57e17d4eaf17a0e0fb995",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:6741",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:6741"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.zeroFiberHeightOne",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e17bfb741cc5a835b738d77a694b37b349c568e4f7e14e2774155f51d84e2031",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:15487",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:15487"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.zeroFiberIntegerOrderSum",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ad37cb0c9c35b5716a0c0ed5e78b3b62f9c3456254c075f82f2ce46ac627afb8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:16242",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:16242"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.zeroFiberIntegerOrderSum_eq_length",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dbc69cb62d544f3edfd5ca21c8e8c14a8e103503d3b25adbfe98efdd475292ee",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:16812",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:16812"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.zeroFiberLength",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "02112d2ed7e4ef08876cc9a0070808f9632e534504ffc3f49c660592e2b845e1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:8822",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:8822"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.zeroFiberLength_eq_fiberDegree",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b6fe6567943245b463439d8bb7458d4383b25f5856d3492e5efe0a8399890a86",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:9240",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:9240"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.zeroFiber_inertiaDeg_eq_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "26b47644da3af5c0403c972f5db80f225e6625842519c259b100d9109d393ca2",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:8124",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:8124"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.zeroPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "de006358f975e2928216f3f396debd62d600364af5c76f3336e174cbc44c0f1c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:5413",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:5413"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.zeroPrimeQuotientEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "510d7379c4076626254f39af6a5521b8b6abb9a5d9c1e015e90457051deaa7b3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:7967",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:7967"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.zeroPrime_eq_span_X",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a27b3889719eb97fcc57ab60898fa2997b07edc5c63f59c5cb6f4ed63e5b509f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:5635",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:5635"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.zeroPrime_isMaximal",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "45c57e299b8a7c1797dc6c01c267e017c3ea5fe59e72aad1219b5cc7997b465a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:7791",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:7791"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.zeroPrime_isPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0ee5954ee71b7138130a1278b23312eecd3209283212bfe08153e5818ef93f5d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:5508",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:5508"
    },
    {
      sourceName := "OAI.PiExponent.CurveZeroPole.zeroPrime_ne_bot",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a27db56e47a4ec1466f3c6104d305bee54ed503236f934d359baf63cc3c03b8a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:15216",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole:15216"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranch.expansion",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranch",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "595dd38b31deac5271e3cf0790a2d0b42f0d92f9c29dd7bf565a44b1f4bbeb04",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranch:1336",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranch:1336"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranch.expansion_constantCoeff",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranch",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5e9ccc64c6454893fe9f715cd9c3755ddee579e54e69c18d0a41100bc827a677",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranch:2141",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranch:2141"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranch.expansion_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranch",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7a76f567a9134b3cdf805010c7a029faae9bc2cc0603ceb202350d894ad212f3",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranch:1942",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranch:1942"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranch.expansion_order",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranch",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "585ac84fa9f9d820256b203e96d8e85f3f1b3d3f0db37eb6c4d629db7c70156e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranch:1688",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranch:1688"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranch.expansion_uniformizer",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranch",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f8e9a13166eaacf951963aa78992a10c44374171d07a73ff838a179561605d39",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranch:1541",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranch:1541"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranch.residueCoefficientMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranch",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4bac5aeb10198c53eb4734a90c1cc002a975ea2078fefb0a3bf58eb7ea1cff1e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranch:396",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranch:396"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranch.residueCoefficientMap_ker",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranch",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "976adea9d80d7aa2b654dd4326816b701f5036c4792bcc173691826310e5f631",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranch:538",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranch:538"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranch.residueCoefficientMap_ker_span",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranch",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "90bb40a0969098e68ad12ca0d2e4c182a58f86c45efb28d3ab48a5a11d70eabc",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranch:1123",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranch:1123"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranch.uniformizer",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranch",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ffe104b200499049d55eb60a8a639bc25973374f72264b15ae4c0628575ce38d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranch:893",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranch:893"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranch.uniformizer_irreducible",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranch",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "614be130ce726ab77f209231fd8075da4a071f6be51dfeed9476be53e1ddc1d2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranch:983",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranch:983"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.coeff_expansion",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d66d87581718c7b564973c46ff58dab04404abbea490b250d577da03af0d28b3",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:3166",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:3166"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.constantCoeff_expansionHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e5237b645134a0baaa491c6c29d7d18ae85a8a723e5a6c6637b0f72d19539a8b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:6805",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:6805"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.expansion",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "167e90d0004a5e724bb1573a5cd5ccf8ed9d2afc41c91eb08cafb85453e6876e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:3062",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:3062"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.expansionCoeff",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fbd70e6f831e73689e8f17fbbbe54e5eab16d17cea3fe220b374a6ebe3879464",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:2233",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:2233"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.expansionCoeff_add",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e69d6c84db94aa316eb164feb8e3dc343012178603d9a47a269cd88f32dc1a1b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:2664",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:2664"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.expansionCoeff_smul",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b6b3e529895570c215147b07f6a478b34e038f90e004e9740c494eaa5bb00f2a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:2877",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:2877"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.expansionCoeff_succ",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "86558c878a77de55ba0d8be373e6c83da07e094cad31ca5b6ce35be814bb8261",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:2421",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:2421"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.expansionCoeff_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "22e214fc7ed023d199bf36c35aa0fa7feb0fd1dc1130c3b1376a637615e459ee",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:2324",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:2324"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.expansionHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "284e85ce7a53d1b4de4a41faad8a895375971648da57b01bbc74d6e6a37d1e78",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:6452",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:6452"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.expansionHom_uniformizer",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f8cfcc816502bb3ad3159c47c4c4e044943c71b5e7a79747b47b3118581cbbf1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:7105",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:7105"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.expansion_add",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6e88bc7aee9bdc54d3722b5ba327bf4069735fa0fa06472058d59d66c40b0428",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:3342",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:3342"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.expansion_algebraMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "972ba9e3f8a69604630859e22d620dc8745c18c70d306fd95c958443df31f9a7",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:3773",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:3773"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.expansion_mul",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bfee91b93f8f68adcb2a811949ef99b47e7c7283bff876b593d9c00a41b38b12",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:4760",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:4760"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.expansion_rec",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3e3e2e7fb47887029a53f84030338bfcb5d05e3e19285e199af3aa59262df101",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:4065",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:4065"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.mul_remainder",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "194d26207cce27e561254b641ef582de149da09d1f0bda8fa4cdba1dad48122a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:618",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:618"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.remainder",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2e7e21bdb71f340eacafce1f49ab86a08221fee3e364bc6b211f9f52c763fc0c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:538",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:538"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.remainderLinear",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c04419f3309caa5756194a7ba93be1a686942380ec1070dc7b0ebf0b66ae463c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:2065",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:2065"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.remainder_add",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "19c3c485fa23e5cfe782b461013f0b649d38bde4e2fbcd978d553daf0e3d6576",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:800",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:800"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.remainder_algebraMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5a1c93e35ccca159ab8f7928e2a332c5ad35b3d5dd9fb408e0e55543c6f93e5b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:1436",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:1436"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.remainder_mul",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "44cf80951288de98c0dd99d42e7cda1c382fc79ee28ab4457856df735aa856c1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:4425",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:4425"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.remainder_smul",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a50781fc8bbfb2fb2f87ae41433a13bc5c173e5404d3a0dfe3e7c6e9a29d4fb6",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:1068",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:1068"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.remainder_uniformizer_mul",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7d00b23d3ed92f0e694a8915ade369dffe901eea35a230a646e07a966dd5d1cc",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:1826",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:1826"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.residue_sub_dvd",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "15dcbdda23565c49f28083eec736ef623fd682ed66d0109688a0bb87cb5a1a1b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:336",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:336"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.residue_uniformizer",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "818ffac987e6a6bd9ecd3cdb31f2e1bfae2c45f6dc3357932f54d8b34796d629",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:1646",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:1646"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchJet.contact",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchJet",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ea4e6aeb6ec7f7ccb8fbce97faf93e3150b2fb0e1dc1b49a7ee2b2563215cdc1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchJet:3436",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchJet:3436"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchJet.contact_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchJet",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cd8ea48678ec2ef134eff38b433c817dcf6a9704c75b383fd61dc63dc7c2ec23",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchJet:3682",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchJet:3682"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchJet.coordinates",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchJet",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7fc6dda40b70b3536d5144ed3c170428f91bbf8775f86b94cb6e15a48a25a5be",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchJet:952",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchJet:952"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchJet.coordinates_centered",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchJet",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "17a07a1122c16e852cd0d2f9395e45be47c168e45dfb1fa03a7322c244d03d91",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchJet:1168",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchJet:1168"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchJet.coordinates_nonzero",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchJet",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "466459e401d3371c39b7f61b90f71349f241880a0dce43233b8e08fce4b5f514",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchJet:2441",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchJet:2441"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchJet.expansion_aeval",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchJet",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5639832caf6f4caf39d645f2c2da78123c35b63c30c9a080c48eaaf9645b54b5",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchJet:496",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchJet:496"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchJet.frameWord_addVal_lower",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchJet",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "09eec19b359e12f122fa8c4e0cb5c409e8d0bd66ee377a89f5474c20872e5b92",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchJet:4115",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchJet:4115"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchJet.frameWord_colength_lower",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchJet",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1e84d29119bd0975a07d0b0a27f9121ebc8c55b050b332fdbea88877f4e5873e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchJet:5961",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchJet:5961"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchOrder.algHom_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "11fd756077779b6fd1aeef9218b37b4633c858dc8b7ae0750078e24ab5b56bc4",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchOrder:3825",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchOrder:3825"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchOrder.algHom_order_eq_addVal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bcb70163fc179c9f993c8eb3563041ddaf773c329992600a8d7c8ad89849011f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchOrder:3562",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchOrder:3562"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchOrder.injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "97e3b4d198399943b3831bc06feba5f859b1844119d3c3c4f71bfb1aaeb49194",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchOrder:846",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchOrder:846"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchOrder.order_eq_addVal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "785089981b85c2e51c0ca8bc97c6a702cb82f2897b325c7f64188f2502c00aa2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchOrder:232",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchOrder:232"
    },
    {
      sourceName := "OAI.PiExponent.DVRValuationUnique.eq_fractionAddValuation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4d37f703eee9162ac77a759c7011b8d4030e8b4295c4ed67ea5bffe94ba3bda1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique:3159",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique:3159"
    },
    {
      sourceName := "OAI.PiExponent.DVRValuationUnique.exists_order_eq_uniformizer_multiple",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d57957a552a50d22c043ad2099f2ae3605e09c30a5d08ea0e4fb4ead45c1845a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique:1380",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique:1380"
    },
    {
      sourceName := "OAI.PiExponent.DVRValuationUnique.fractionAddValuation_normalized",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7c1e9ad4ea52b3678834e47da594888307e2e0f723b744042e5cead402468729",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique:4684",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique:4684"
    },
    {
      sourceName := "OAI.PiExponent.DVRValuationUnique.integerOrder_unit_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2834e426d834446b75b531054bf94b23179f12eb0dee5f0f344542c0e92e9679",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique:753",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique:753"
    },
    {
      sourceName := "OAI.PiExponent.DVRValuationUnique.localFieldUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e91392c80c776612e50ec7e95dfc251eea119355b76cbca53d034c4e5c9965dc",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique:420",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique:420"
    },
    {
      sourceName := "OAI.PiExponent.DVRValuationUnique.localFieldUnit_val",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ef8117c3d43bbf8ee548ccb793d5caae5af33365b1e97ec0e69456b57e5b7331",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique:566",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique:566"
    },
    {
      sourceName := "OAI.PiExponent.DVRValuationUnique.uniformizer_order_dvd",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4e3fee31cac9731445068f0aabfaa172aeb66ee22ff8bfe5bb79296779de8ee1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique:2233",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique:2233"
    },
    {
      sourceName := "OAI.PiExponent.DerivativeIdeals.derivation_mem_derivativeIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "80a5e433f8492bb82afd83c73dda16de072a0c015fbc12e8a7b503c4c1021c8e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:2900",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:2900"
    },
    {
      sourceName := "OAI.PiExponent.DerivativeIdeals.derivativeCore",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1b54af6773e21ea739d03d1c672eaf3be47e48a13b68f36bffe2ce4ee327a69b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:2280",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:2280"
    },
    {
      sourceName := "OAI.PiExponent.DerivativeIdeals.derivativeIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0f498135f40e28c319f397b3a322c6a2dca0ed51618fc1343c23e637ac7f7e4a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:1290",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:1290"
    },
    {
      sourceName := "OAI.PiExponent.DerivativeIdeals.derivativeIdeal_levels_monotone",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7be8785c1e054fc0aa782d54ecb796f75d82b348407613ade487f6ef9f8b86b7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:4988",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:4988"
    },
    {
      sourceName := "OAI.PiExponent.DerivativeIdeals.derivativeIdeal_mono",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5f73d9f8bd6f6a71e31714cfbd88d5f9d53dd943424a49d261761dc40a68f311",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:1767",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:1767"
    },
    {
      sourceName := "OAI.PiExponent.DerivativeIdeals.derivative_vanishes_on_persistent_ideal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "568cf50c341d2dc5164d37603f342ed700458e4d5a8c53d2c18ca64e55c15836",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:4387",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:4387"
    },
    {
      sourceName := "OAI.PiExponent.DerivativeIdeals.exists_persistent_derivative_component",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aa414a3ef0cd2087f72226eb4d0d46c962b3e1c4c5c63ae586e2c55f43fc6eb5",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:5334",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:5334"
    },
    {
      sourceName := "OAI.PiExponent.DerivativeIdeals.self_mem_derivativeIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8b72b5e537151719ff7b881c79c605929d9c1217cf133f51ed09a2b8ec668c3e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:2057",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:2057"
    },
    {
      sourceName := "OAI.PiExponent.DerivativeIdeals.wordCost",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dc4355c9d45cdf02187fd4bd7b042cd5d3eb94ac29e27dcafcaab0a13d8621b7",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:743",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:743"
    },
    {
      sourceName := "OAI.PiExponent.DerivativeIdeals.wordDerivative",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1140a3db04690e9d57c37850c3d7719286b78d0d31e94f5c72a1bfe75b6d8bfb",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:328",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:328"
    },
    {
      sourceName := "OAI.PiExponent.DerivativeIdeals.wordDerivative_mem_derivativeIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9d6966d143c03dde24b6ed580d23d41473aa4340d2514cfd1d58072a06a0972b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:3701",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:3701"
    },
    {
      sourceName := "OAI.PiExponent.DerivativeIdeals.word_mem_derivativeIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e4c6de23311f25934ec772a851afef78376bcde06056f9d46aaf13f0282ca8d0",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:1491",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:1491"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantAnalyticBound.log_norm_sum_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.DeterminantAnalyticBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4f78a2336e845707f3bb1710d89946c4c325aec273b4337b82649f02b0c3d382",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.DeterminantAnalyticBound:5774",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.DeterminantAnalyticBound:5774"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantAnalyticBound.translated_summand_bound",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.DeterminantAnalyticBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2eceff6456ccbfe345cf0c6c66a229666f44bc38fc0136f6e5d1a9eae8864306",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.DeterminantAnalyticBound:4397",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.DeterminantAnalyticBound:4397"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantAnalyticBound.two_alternative_exponent",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.DeterminantAnalyticBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "790d81aa4b88b601cf932eb074f6062554a268cd91ff9874a5e655182b97604c",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.DeterminantAnalyticBound:215",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.DeterminantAnalyticBound:215"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantContradiction.AnalyticAggregateStatement",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7ff3637cf679513fca377c20a6da7b76705a89d07054edb7118e964250f295c2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:4587",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:4587"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantContradiction.Column",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d254537eeec190a12d8ff0ce95e052da1f9a345a68563291203cd32d1183cf36",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:1487",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:1487"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantContradiction.FixedData",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "121224e4a278e93b89f07eebcde883b9f77b943b3aceef201dd82c735f11504b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:677",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:677"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantContradiction.GlobalInterpolationStatement",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e631ecae0b10fd1511cd84cc1be084d3af8290c040ecfcfe3c84c4e65b48f642",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:4399",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:4399"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantContradiction.Row",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bd10ee494ae0d521d267cc74ad5168ac0bcde905a98dffe617198da4ffb4cee7",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:1321",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:1321"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantContradiction.actualMatrix",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c596b19a391f6687196e929f09f6f23874aaee52b5c16552ba7a24037956af5c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:1637",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:1637"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantContradiction.actualMean",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a6f2fbaca54c085fa54fb9973ba9b8a2eeb74448de555ce17d611b4a24cbe42f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:2320",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:2320"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantContradiction.actualMean_bounds",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6facf60dbfb86367886b9e2cbd6f2906e7b1f17ec2c74a1e5469257c197049a9",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:4002",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:4002"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantContradiction.actualMinor",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a28bf2bbe2b0e0f95c74f5a963edb00130a88fb224af1797083b0bf5a059a47f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:2042",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:2042"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantContradiction.actualRowCount",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fc4e13f893e5ea9a1732519e8ea9cdce538421d7c2144c95b981b41f3b0f3329",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:2482",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:2482"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantContradiction.actual_minor_arithmetic_lower_bound",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "916e0eab5d6e791d25a80e22a2a22699f8621dc201fe0d14b91daccf33bc0e46",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:3210",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:3210"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantContradiction.collisionConstant",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dd1f0febdc04faccd4b5e374f91928f327ce4a31bbeeebe0c7fb60c41e15115e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:463",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:463"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantContradiction.collisionConstant_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e438b1c64aecbfe969ddb1c29774204c1f6c172f81011488e6e24e9ca4641dae",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:526",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:526"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantContradiction.collisionLimit",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fbf7d66e807b98c2e715deb8230c9208758198cc7902864abce81c926c009172",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:2978",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:2978"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantContradiction.collisionRate",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1f70e5d4eb8de11f7c1960a315425afb988ce51775deb690dc5c0918c57cac46",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:2788",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:2788"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantContradiction.finiteDenominators",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "07144205a73259ce61ef5436ceafade674483476fe4e75c2f61202ce36998ade",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:887",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:887"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantContradiction.finiteDenominators_two_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "806eb63ebf6732abb61820f4500f98f785c31842c9e97269b03fe25d6e78a177",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:1000",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:1000"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantContradiction.finiteNumerators",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "881d847e91466f3a5e9d02b59051247374f1ba923f2b2a731d861488931a6110",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:776",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:776"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantContradiction.logWeights_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "86280277df16a765215db899b2b5267226bf95649172edb122e6fe610a474646",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:1147",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:1147"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantContradiction.lowIndexCount",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eb03d7e80ca2a1823b7b96c2950a8bd2f905759f858124a87c92c25c762e329b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:2593",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:2593"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantContradiction.no_fixed_data_of_interpolation_and_analytic_aggregate",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e5917fbdb3b63e103dd36e1857d43be3775d87bba2540869454405d3b56d3f64",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:5882",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:5882"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantContradiction.piEventualLowerBound_of_interpolation_and_analytic_aggregate",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "071b2762d25f6606437267981abc9ee7f506c7669b0d545066abff460371606b",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:8308",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:8308"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_009.jsonl"
