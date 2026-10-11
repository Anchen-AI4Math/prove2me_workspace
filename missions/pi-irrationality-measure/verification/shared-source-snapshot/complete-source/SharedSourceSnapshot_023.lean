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
      sourceName := "OAI.PiExponent.ProjectiveMonomialCechHigher.differential_sub",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5851342b9a026fa4bf27b2620b6e3b133782b867adcc855f185657172a1ec9ca",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher:1394",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher:1394"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialCechHigher.exact_of_pivot",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "69a2c160c2404354b717237b48b07f6390ba026fb706c02ac862f33455347f00",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher:5898",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher:5898"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialCechHigher.insertionSupport",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cbcc950e7442dcc238645f8b60d5bf05c0fda93cb4a55493a512bde7214feb92",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher:2944",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher:2944"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialCechHigher.nonnegative_twist_cech_exact_all_positive",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3927f177b0acabeb9192d1b59af3f1de35e3e9e0d2fcd7e0decc76c7c5e2893e",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher:6519",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher:6519"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialCohomology.boundaryMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ace748a398185cde511a85bd28b308871a9b4fe4bbd40524d99ed7d1f8d99dfe",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology:4370",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology:4370"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialCohomology.cycles",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2f2e9a9fef9c4ca98d6d81b3eaf4d9adc1dbc4719e65b8ccf4b00f42fdd7e4a2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology:1298",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology:1298"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialCohomology.degreeZeroCoefficients",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2acbf0b73f5cbd81009162cd823b4c593df82a96a54d10dc26e5ea757ec63ee3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology:2770",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology:2770"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialCohomology.degreeZeroCoefficients_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e18067c9e5028b1955978f0f4fd758f9ec6a34e4f679efb5b80ee60d22690f98",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology:3020",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology:3020"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_coeff_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f2d2e97c6b4dc4edc0229f82fd7048fcd29741a26b2dcefdbb45101f53652d84",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology:1437",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology:1437"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "22c20d626a55ad2ebf111d581534ee8773b507e8bbde9df604e6ce2eabb2cc9c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology:3975",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology:3975"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_nonnegative",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b6d8aac50999722a7acd5a77299d7a066a2e6f48aa795aa2e0558527f312e1a0",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology:2177",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology:2177"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialCohomology.differentialLinear",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dc64fbd27770670531ead028246f4ad22587944005b9ddad100d16c28e5d63e4",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology:327",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology:327"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialCohomology.exists_negative_representative",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3e43f2ebe1c28439003754118a50bf3c8c7bec9fe1e64c45b3924fbffba4d9ad",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology:6018",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology:6018"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialCohomology.finite_of_boundary_annihilating_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4571570e659edcaa3fc8335c853d60bba4cd1f3fe264eca070eda2823dfb8252",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology:6773",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology:6773"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialCohomology.negativeCoefficients",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "74f995f83847bc6e76fc9a2e01f58d6592a41c2d6b6a6d50d67a7d476af28ec9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology:5164",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology:5164"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialCohomology.negativeCoefficients_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5e2ef254c1ff03c6c45c0a188382eeaa82c5ee31199b4a85d78834f0f8a9afbc",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology:5436",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology:5436"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2ec3c16de9c3a3dde50a4be4e4061f06d27ca065296daa609b7eb31cdf6ce027",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology:4717",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology:4717"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dcd74b17c9247b20d17231db0af534254d93b9676d87a37da2160d50ad28462d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology:5782",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology:5782"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialCohomology.regularCochains",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "28350f83af474919b67d7669bfaa7f715c18648dcc6c627c3c3f2a35394f75ed",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology:792",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCohomology:792"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialFinite.AllNegative",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveMonomialFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "521eca145fa70e83d516811fc791fdad6449ae2447746da491d6284e3dc0e2bb",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveMonomialFinite:394",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveMonomialFinite:394"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialFinite.allNegative_coordinate_bounds",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveMonomialFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9a809f46610faab8828272e92439a73446fe0429eaa314b29e8e5eadbb6135ef",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveMonomialFinite:472",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveMonomialFinite:472"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialFinite.allNegative_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveMonomialFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b48695719609d31fd2b9656f78dd3153419a7d2a7b3893af54d66141d1a9591d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveMonomialFinite:958",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveMonomialFinite:958"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialFinite.allNonnegative_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveMonomialFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "db71a8ca59b0b597ffff454f1ae67e8009e5bec95cef314c062a68a7ee9ff1a8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveMonomialFinite:1365",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveMonomialFinite:1365"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialFinite.cocycle_eq_boundary_add_negative",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveMonomialFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4a4c27147922831b1358512b929886d38c01ad222bad2fb9f5e13f2e8a3a27b0",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveMonomialFinite:5713",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveMonomialFinite:5713"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialFinite.differential_filterCochain",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveMonomialFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b47fac0bb6d93a74af3de920f4f3ee658a403eb01b98a56b0cb048c97650edcf",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveMonomialFinite:3316",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveMonomialFinite:3316"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialFinite.exact_of_obstruction_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveMonomialFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "91c4aaf516df1a2e107bea905d141b93147c769c66b1cf4dcc1a97c175acc55b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveMonomialFinite:3959",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveMonomialFinite:3959"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialFinite.filterCochain",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveMonomialFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b679bcc1e21cc27833c1f870ba30a5771521d6067e1c88b99377e053b80a805a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveMonomialFinite:2539",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveMonomialFinite:2539"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialFinite.filterCochain_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveMonomialFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "168a05b313a3f6e49f7ca1eadc7bc8f3b768838d8ea51eaa3507197508878b06",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveMonomialFinite:2734",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveMonomialFinite:2734"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialFinite.filterCochain_closed",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveMonomialFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3bfca7cf896bd4acf99ae2077de9fbd5e19c8587cdfa238350b9947288ea647e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveMonomialFinite:3693",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveMonomialFinite:3693"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialFinite.filterCochain_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveMonomialFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4269d15bbb5fcd13f177b48ca0d474234f43d980b9667af94cc225f41b991390",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveMonomialFinite:2990",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveMonomialFinite:2990"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialFinite.monomial_subsingleton",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveMonomialFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "08b6891aca9693a6759dccaa5411256a77bdd43d3d599726717533afecbdee76",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveMonomialFinite:2043",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveMonomialFinite:2043"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.awayToSection_coordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1ChartMap",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "45e85233ab280f712169616912f754510cdaf05f5780860a6ea45b62bfcfe0ef",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1ChartMap:1692",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1ChartMap:1692"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.away_projection",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1ChartMap",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d16a085672927df68fd931e791f579404c85b44bbb6124d293e401b059f5a51f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1ChartMap:766",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1ChartMap:766"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.chartRatios",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1ChartMap",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "07e6841ffecaf8f23a907b519c5be726e10856b02ead8bda9ff1df5f9ebf8318",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1ChartMap:3905",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1ChartMap:3905"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.chartRatios_self",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1ChartMap",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "57bed8f656aac28922c759896877bf7064b841b69c65f762f20f832f02294ff1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1ChartMap:4083",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1ChartMap:4083"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.coordinateCocycle",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveRatioCocycle",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c7c43caf7c1524ced4854a45d3adf5c2a416bb99fbcd27a071ace4ecffa0a634",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveRatioCocycle:3982",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveRatioCocycle:3982"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.coordinateCoefficients",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Sections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e324547e790c5143347b315b55495218dcdab89ec48d38e3e6118cf0dce1a406",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Sections:460",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Sections:460"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.coordinateOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveRatioCocycle",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9caa855015641a20dabaab261434dd9867c6c461c9d88a7a740af1166ece1278",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveRatioCocycle:559",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveRatioCocycle:559"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.coordinateOpenFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Morphism",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "347bb573a7f0f5409e64ba7719fe5cd7b991e8aafd5644d4f3453e24c6160006",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Morphism:419",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Morphism:419"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.coordinateOpenFrame_localMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Morphism",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dd0aa0410efedb0eab84570119b7153636222aa65aecee00ed61beccf139abf8",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Morphism:903",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Morphism:903"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.coordinateOpenFrame_normalized",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Morphism",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eb0f042a57155627e61e0b9db34189c5fcdb4df7e697bdc11a72341468dbaab4",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Morphism:666",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Morphism:666"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.coordinateOpen_le_isoOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Sections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7c02b2c0e31ef730e563c519d190b34e75e6468160402e11a750a5688b6736f9",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Sections:2169",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Sections:2169"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.coordinateOpen_projection",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1ChartMap",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cc22a1c9e7a77e58255f016974044e979afe4df65a372a6e048a0676bda34058",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1ChartMap:1175",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1ChartMap:1175"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.coordinateOpen_pullback",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1ChartMap",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "270930a42c66ea9cc222b3b958dea65a8ea33a04430ec4cef0291fb1b0ebed4a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1ChartMap:2894",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1ChartMap:2894"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.coordinateOpen_scalars",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1ChartMap",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b23cb55391cf86c2cb3451627c573de7bae787fbdcc02f4ff9fad75c27b6b5b7",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1ChartMap:3336",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1ChartMap:3336"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.coordinateRatio",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveRatioCocycle",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "53a352003435671d48facf72368590a4b45c0ed29c52686f78b7843b53da4197",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveRatioCocycle:668",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveRatioCocycle:668"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.coordinateRatio_mul",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveRatioCocycle",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c336fb84f6ac009d52b112483f425d6e0a3666a210e3121692690767880bead4",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveRatioCocycle:2016",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveRatioCocycle:2016"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.coordinateRatio_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveRatioCocycle",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3f039aac762bbabb1e2178c65b4f85516a525c0572ed8421f8ef49e45207ab2e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveRatioCocycle:1050",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveRatioCocycle:1050"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.coordinateRatio_self",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveRatioCocycle",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "29463a36efb8cfcd109112a0c89771405b54d21f8d6da74838b7be8cadf71cb5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveRatioCocycle:1358",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveRatioCocycle:1358"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.coordinateSection",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Sections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bcde2f2f9951d7418a6c8f6f04e27793b3473e371df7599082c4f95cde40e3f2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Sections:791",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Sections:791"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.coordinateSection_coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Sections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8e8c70f126c8f8460e2602ac621a2358f795525008ce65ae0a9c726a4c29c7a8",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Sections:969",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Sections:969"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.coordinateSection_coefficient_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Sections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "29104beee69e2bacfe27898ca0aeb45aefe823be45ecf27bcc7e07b2b4d6b828",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Sections:1338",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Sections:1338"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.coordinateSection_cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Sections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c4c710d37bdcda0f02c86900acac6d997144f3ba4c00cba5970666e1d7083d16",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Sections:2916",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Sections:2916"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.coordinateSection_isAffineOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Identity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "850a23e117f5a5c87a328c6c5799eb0bba8adae6577752f08eb22e7ff7cbf513",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Identity:841",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Identity:841"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.coordinateSection_isoOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Identity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2753bcbce8ea49d080efe68f18df390fcf618eecb02ee6be87d83d015038149a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Identity:429",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Identity:429"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.coordinateSection_localMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1LocalIdentity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5045d05fb06d23d97fc445f314194b5c31e9041f10c4fdbf582ca7301482d543",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1LocalIdentity:469",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1LocalIdentity:469"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.coordinateSection_normalized",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Sections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "83825a1301a84447cc0940ac88edf44c42660b3bc038cc796613edc0d2c971a3",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Sections:1801",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Sections:1801"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.coordinate_sectionsMorphism_identity",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Morphism",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ffef423d6fedf230ea63aab92287c2bb135153042e8e0f94748249110f7575cd",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Morphism:1489",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Morphism:1489"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.coordinatesMap_chartRatios",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1ChartMap",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "08abb26a294dc02415b71f8bd1b4cd21e90bccc5df423f4cb8a36d16395a30c5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1ChartMap:6045",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1ChartMap:6045"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.evalAway_chartRatios",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1ChartMap",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d2f0f5d91ad4961dad693ffd81b90a34d77c237b3bcf2ff1bff8ee192d6542aa",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1ChartMap:4209",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1ChartMap:4209"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.globalSectionChartPolynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomials",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "49e05db45a2a01f146ee7c8c7620f67b2613bc447a560359606dbfcb1b8b0252",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomials:10006",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomials:10006"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.globalSection_homogeneous_polynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomials",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7280112f5bcd5c36a48d5ce20cd2387314535804a848522ae99f468eb3309358",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomials:10590",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomials:10590"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.lineBundle",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveRatioCocycle",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4477a17801db6c343c31a9308efc3f7cacbf3a508156978f625b308688847184",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveRatioCocycle:4301",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveRatioCocycle:4301"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.lineBundle_ample",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ProjectiveO1Ample",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "be061d6ca42ba60c843a09088e8fdc04014abf62a97aaa388a8d3dace45c251c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ProjectiveO1Ample:430",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ProjectiveO1Ample:430"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.projectiveSpace",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveRatioCocycle",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4bfc4d13bed0a451ce3ed4701f1cf0c912cc9ff63001b9004ded1cc1ed0deef8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveRatioCocycle:483",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveRatioCocycle:483"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.projectiveSpace_diagonal_affine",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceBasics",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ef0c4e8248028c7c3581f057579bd8fe280fb9fde986533a8ae002123a33080c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceBasics:1037",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceBasics:1037"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.projectiveSpace_integral",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceIntegral",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "79c9f666cb14823b68f4f7c1dff46f0e5679b53246672b17860228bdca0e5f4f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceIntegral:1685",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceIntegral:1685"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.projectiveSpace_irreducible",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceIntegral",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cc405b9058c87fcb7511151f1d319abd0c24e01c484a2afcaebc9d201bc60cca",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceIntegral:927",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceIntegral:927"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.projectiveSpace_noetherian",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceBasics",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ca63dd217267459495339cdd775620d39e76d40472e06a084bafc0dedab82054",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceBasics:352",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceBasics:352"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.projectiveSpace_reduced",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceIntegral",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ac4e8dde532f24c8a79b6e8b082fd10cd4b50316ceba706dd9c707bb40300ed0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceIntegral:459",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceIntegral:459"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.projectiveSpace_separated",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceBasics",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "edfcc6884c68f6117f3967bd58988675b8987174ddc20257be30ac156ea75154",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceBasics:756",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceBasics:756"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.ratioUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveRatioCocycle",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "34104af2f21edf7262360a5e3072cded90e97cda1e87bdd0904b34b9b64fb8a1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveRatioCocycle:3574",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveRatioCocycle:3574"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.scalarPullback_factorization",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1ChartMap",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9b4ed583c4ca8b7c25d48b6e574aef2139164a75a873b243d44c1d959e641735",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1ChartMap:2210",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1ChartMap:2210"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.scalars",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1ChartMap",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "823bb0053fea23c21626f5e1daf245ab9383771f23b93d3092d6c22fc37d5962",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1ChartMap:603",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1ChartMap:603"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.serre_vanishing",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceSerre",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cafd52edee27abc1980f91243c050fb129517c0b315e3664ff576a32566cbbe6",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceSerre:1394",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceSerre:1394"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveO1.standardPower_ext_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceSerre",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9677a646cffa10f161116358ddf916508af323b548c7b1f59194b0831cc1fd43",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceSerre:710",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceSerre:710"
    },
    {
      sourceName := "OAI.PiExponent.ProjectivePencil.H0_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFinitePencil",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "080367a9e901b5bb0b0d60c5cbfe5acb9dbb6156b1b26f982e5c4efac7eda530",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFinitePencil:2181",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFinitePencil:2181"
    },
    {
      sourceName := "OAI.PiExponent.ProjectivePencil.H0_finite_complex",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFinitePencil",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e40f3f0eb87c9cfc57c08358fdfa4bce983665d533eeef0d554563cbaf0c4ac6",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFinitePencil:3182",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFinitePencil:3182"
    },
    {
      sourceName := "OAI.PiExponent.ProjectivePencil.H1_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFinitePencil",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "be52259d0689d725f0c0c7ce2decc35b0e17724df57aa3915ab8fc8b91f9d03d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFinitePencil:2525",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFinitePencil:2525"
    },
    {
      sourceName := "OAI.PiExponent.ProjectivePencil.H1_finite_complex",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFinitePencil",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0d24a1ee18293a093d3fbaf227566c85ed9671c93f0b43fdd3d80c9e6e589bc0",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFinitePencil:3564",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFinitePencil:3564"
    },
    {
      sourceName := "OAI.PiExponent.ProjectivePencil.coordinateSection",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFinitePencil",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2585b1d862aa2ad0e9c6116c2334d47fbefbd8b2b7fd8aba93dd85cc423006fe",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFinitePencil:711",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFinitePencil:711"
    },
    {
      sourceName := "OAI.PiExponent.ProjectivePencil.lineBundle",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFinitePencil",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "38be0a1a3f2fb94d15809f8f29722527c22571c2c634bb5d066fdd481fd733a9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFinitePencil:569",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFinitePencil:569"
    },
    {
      sourceName := "OAI.PiExponent.ProjectivePencil.scalars",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFinitePencil",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eee49882523d554989f768b8bd0658ba2926354e680545f3c0f52f8635eca098",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFinitePencil:895",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFinitePencil:895"
    },
    {
      sourceName := "OAI.PiExponent.ProjectivePencil.scalars_eq_baseScalars",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFinitePencil",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "69f6a64842ddf850002f8a6650cf981d8a2ef5cac40c8499d94e6ad8555d4944",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFinitePencil:2966",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFinitePencil:2966"
    },
    {
      sourceName := "OAI.PiExponent.ProjectivePencil.sectionsMorphism_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFinitePencil",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aa62fb5feb66b6e1a02256dcdeacd19151820e3c0238898de99fde0d91c3947a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFinitePencil:1301",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFinitePencil:1301"
    },
    {
      sourceName := "OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFinitePencil",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "32b594d47228d1fe7ee7186082cd992273637745c91ce74beddd5548277126d3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFinitePencil:1788",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFinitePencil:1788"
    },
    {
      sourceName := "OAI.PiExponent.ProjectivePencil.sections_cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFinitePencil",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6d276997ffe3d1c381b31f09256dfe92ec60ebf2864b058ff45260f1654de74d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFinitePencil:1043",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFinitePencil:1043"
    },
    {
      sourceName := "OAI.PiExponent.ProjectivePencilScalars.projection_eq_structureMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectivePencilScalars",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fe503a214ed6d97b79bad53ac7da134e542de16129b3f755af805ad8c0af8934",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectivePencilScalars:319",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectivePencilScalars:319"
    },
    {
      sourceName := "OAI.PiExponent.ProjectivePencilScalars.scalars_comp_eq_baseScalars",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectivePencilScalars",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "569b3ca898ecfedca8c56576b702a01f74bf98c4d83f7da6c88b35060ad5667f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectivePencilScalars:1089",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectivePencilScalars:1089"
    },
    {
      sourceName := "OAI.PiExponent.ProjectivePencilScalars.scalars_comp_eq_structureScalars",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectivePencilScalars",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2242c90af2e4a1d1fd4e655c9eee1512606e512a0d33d0331b3fad3c4681ffe5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectivePencilScalars:667",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectivePencilScalars:667"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveSectionExtension.eventual_projective_homogeneous_extension",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionPullback",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c48b47b4a03570c53cea46a4ac5db3f6c78a490161fb56d3332abad573b27ead",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionPullback:3206",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionPullback:3206"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveSectionExtension.eventual_projective_pullbackPowerSection_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionPullback",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8257853268b7341a8a55f15410add5fd5624d6abfd10ff9b8512239e817132b9",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionPullback:2564",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionPullback:2564"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveSectionExtension.eventual_projective_quotientPowerRestriction_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionExtension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b7892d59bc3227ec238224487d75fc412ada03ec14e3f5e1fda578b83410b8db",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionExtension:2982",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionExtension:2982"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveSectionExtension.globalPushEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionPullback",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d50b3f655905df3d77ee3345e42f261b938fa2fbd9ed894b11460c1ea62d9d29",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionPullback:374",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionPullback:374"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveSectionExtension.idealModule_isFinitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionExtension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5a71a395cda01faf80848e4d54283f11a85a4a35f7f6aff4bab35bbce5998d1e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionExtension:1051",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionExtension:1051"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveSectionExtension.quotientPowerIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionPullback",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3fa45f1cd20222c51b6766a296c851482e318a5bf0cf52dc404a56fecf77c9ad",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionPullback:705",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionPullback:705"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveSectionExtension.quotientPowerRestriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionExtension",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c1eaa4e1d21bfaa61cce43b3ca45fcf491be81597a2f4b9ba97e33f7dac3f365",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionExtension:679",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionExtension:679"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveSectionExtension.quotientPowerRestriction_surjective_of_h1_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionExtension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4d9495d6bb94893290c33c25194f70b043544be31a72be24381be50198dacbc6",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionExtension:1916",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionExtension:1916"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveSectionExtension.quotientSectionsEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionPullback",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a6f0440958f7777fa6edace26ae8eaeff3d40334de9b3fbdc5108faf786bf9aa",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionPullback:1100",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionPullback:1100"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveSectionExtension.quotientSectionsEquiv_restriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionPullback",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b550c4ca057e8f0ff7ec7d14174acc3851e08ff502802e608a6f99826da98abe",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionPullback:1467",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionPullback:1467"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveSectionInterface.eventual_homogeneous_extension",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionInterface",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a7bbc282fe7871d98de7f7e2dbe38f3de31e4827907d7591ccf775ab469f5d03",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionInterface:1623",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionInterface:1623"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveSectionInterface.ofSectionHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionInterface",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e7665bf1df0558030491b6d7b43a9e93f9e2729db918e533e8d62f06d6a9f2cc",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionInterface:512",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionInterface:512"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveSectionInterface.pullback",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionInterface",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "954daa942e777b8080ede8a370c5849c55390f5a5f52b5076684a6edbe761de2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionInterface:1087",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionInterface:1087"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveSectionInterface.sectionHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionInterface",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b185da88842c046d61b03d3b7e22d05b5c217e42c04c9b9cee0970126fccb6c6",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionInterface:386",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionInterface:386"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveSectionInterface.sectionHom_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionInterface",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8a3cb11b98526daffdf808765993591f65f8f299f76be2a0d724a4266cc08cd5",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionInterface:965",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionInterface:965"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveSectionInterface.sectionHom_ofSectionHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionInterface",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0a33e8e89640392a9c8347d177b0234752eef09d3a9c87be5edeff8e11d70a2c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionInterface:640",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionInterface:640"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveSectionInterface.sectionHom_pullback",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionInterface",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "68ddec1d8f4223bb29e80f396d101d0447fddc66cdeb88fc362d072a3fe0f520",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionInterface:1289",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionInterface:1289"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveSpaceFinite.projectiveEmbedding_cohomology_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7e164c9d03e89daa845c407157bd4adb00525591636836773aa4a9dd8fde4fb6",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceFinite:2113",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceFinite:2113"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveSpaceFinite.projectiveOver_cohomology_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "02976f99e64db4c965c081b0d6da154bbd63086abd63c1d7380be283d475a8d6",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceFinite:2731",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceFinite:2731"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveSpaceFinite.projectiveSpace_cohomology_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b12ea0d3da4d4b215b38c3d5c87ed8f49e59332de4f294ae793e9a3fa5c7acb6",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceFinite:731",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceFinite:731"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveTwistAcyclicity.ext_succ_eq_zero_of_laurent_cech_charts",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistAcyclicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eb6a65a477142a87cb810b8ac4d1b800691dc074dd610d2afb55733b5de23973",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistAcyclicity:3992",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistAcyclicity:3992"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveTwistCech.LaurentCechPresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech",
      graphKind := "inductive",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d07c8612ed8a114604e1e2979a0adf4266b1762e4bb9083f58f0bd5ef6648b46",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech:458",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech:458"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveTwistCech.LaurentCechPresentation.casesOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "24f36a9b192b48254a98755ae9e237b784fa8d2688a4ff81918093acd6ad51e4",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech:458",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech:458"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveTwistCech.LaurentCechPresentation.coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9793163bfe8244cf9b8b739e2ccb7e97f9936f5ab347847d82aa1224fe7bfc84",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech:458",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech:458"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveTwistCech.LaurentCechPresentation.hasPrimitives",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d36aadead47447f979cd349f982935d3e7799d9f2a397de12127e34386d0d08e",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech:1993",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech:1993"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveTwistCech.LaurentCechPresentation.injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e6ef7e39d2b141d60c41eddd0792a3ff014d10701f5f4d32542334aebefad705",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech:458",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech:458"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveTwistCech.LaurentCechPresentation.mk",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech",
      graphKind := "ctor",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3fdb4e364a6b03d5d799f18a5d3a65d0b1c04ab140950db0d747b9c69b22625d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech:458",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech:458"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveTwistCech.LaurentCechPresentation.mk.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b0081bce2547831a56d5864dea8bf0242161c5e2c7fff399f62591e967ee96f2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech:458",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech:458"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveTwistCech.LaurentCechPresentation.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5b734329153d12efefd0e39558687852a59290116d1cec59a574c373e83672fc",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech:458",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech:458"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveTwistCech.LaurentCechPresentation.rec",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech",
      graphKind := "rec",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3a65e58e282273efea46582e8c3955841a85dabc8ce6ae37f01ea96e6c3221a9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech:458",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech:458"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveTwistCech.LaurentCechPresentation.recOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "535ac7c8fe845f22de2de3f2a6bc2c3ac345306a64faa7c2b84b4454699f75f9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech:458",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech:458"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveTwistCech.LaurentCechPresentation.regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2d8b86184b6ae5684facd993104ce8dbc83f08094e9bddac6505cc2bf5581288",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech:458",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech:458"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveTwistCech.LaurentCechPresentation.restriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7ca10b912f64de2c5109aec8ddc561d11aba2da71058fe5445cf6e6bdfb7a785",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech:458",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech:458"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveTwistCech.LaurentCechPresentation.surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "36b9b04a9972c2e7995782b1a636c26b110915b484051aa32579d2911f1a8eff",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech:458",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech:458"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveTwistCech.LaurentCechPresentation.toLaurent",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e8363622d703f497b98c307ea39dfa3eafd1f0b74a4633fcbdbec2301821cf73",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech:1313",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech:1313"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveTwistCech.LaurentCechPresentation.toLaurent_differential",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "671537c6211c3dfc5b772bc994fd654a755ac48e71d82f60cc82971207c3a580",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech:1507",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech:1507"
    },
    {
      sourceName := "OAI.PiExponent.ProperAmpleFiniteDimension.closedImmersion_dimension_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ProperAmpleFiniteDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6344bce205bc2f541dd8e3983761b5c61a3b696aa2ef76be9fe40e4ffafd7988",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ProperAmpleFiniteDimension:1879",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ProperAmpleFiniteDimension:1879"
    },
    {
      sourceName := "OAI.PiExponent.ProperAmpleFiniteDimension.exists_dimension_bound_of_proper_ample",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ProperAmpleFiniteDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "90439dc6fafcc34851c9378d131004d9766c29aaf00bf05d6adf3a3278d29aad",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ProperAmpleFiniteDimension:2079",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ProperAmpleFiniteDimension:2079"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_023.jsonl"
