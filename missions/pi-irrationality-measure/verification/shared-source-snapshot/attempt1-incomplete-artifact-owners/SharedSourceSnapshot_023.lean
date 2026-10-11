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
      sourceName := "OAI.PiExponentJets.W64.iteratedColon_eq_colon_power",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousHilbertExistence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8a2ef325e9645462686059cfa2249cceda56273033f624cae89a926571c7d480",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousHilbertExistence",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousHilbertExistence:483"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.iteratedColon_homogeneous",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.ColonSeriesTelescope",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "70f1ba1a8126b705813d8795910eaffd8dd68a96ec7f851b63642c680b1dcdf7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.ColonSeriesTelescope",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.ColonSeriesTelescope:920"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.iteratedColon_series_telescope",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.ColonSeriesTelescope",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e27e23d655bde05e823a1c649aaba5735e74a532fbb167dec352ad6175609fe8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.ColonSeriesTelescope",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.ColonSeriesTelescope:1367"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.iteratedColon_succ",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.ColonSeriesTelescope",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2cc90b825ca2b1ea80779f98f1313421e40c2bf7fc3588890c39cd87fde60688",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.ColonSeriesTelescope",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.ColonSeriesTelescope:744"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.map_int_invOneSubPow",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PositiveDimensionalHilbert",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bedd5c5d7148e4e98e3f8dbf5384ae15e2b179b6b5820d92b12423f382942cdc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PositiveDimensionalHilbert",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PositiveDimensionalHilbert:3435"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.quotientSection",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c0877d7d7e43f449d7ead5fb0a4f46bd229ce3fdee38fba7da2d9e06dc35af7d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientSections",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientSections:258"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.quotientSectionFactor",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularHilbertStep",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8f1fd09c1ee557734975cf61a2f5284e2abcf191861172bd3e378a26c2c9dc5f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularHilbertStep",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularHilbertStep:257"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.quotientSectionFactor_colon_ker",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ColonHilbertStep",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b56c8ba7c3a6ab68bf6428756765a88d28b398880eea6d8265e4e85cfb246ba8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ColonHilbertStep",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ColonHilbertStep:595"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.quotientSectionFactor_ker_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularHilbertStep",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f8bb1d1ac76b7488d8bb415b3ac7985948d1b4b2be9828c67572e72732b3843f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularHilbertStep",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularHilbertStep:1192"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.quotientSectionFactor_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularHilbertStep",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "94ed857b5f804a599f8fee4943e5293f2330223e7c48943b260cd471b15d3e93",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularHilbertStep",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularHilbertStep:828"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.quotientSectionMultiply",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "34f159c4a8f7c04a93310d87d5f6b16e544aa9c52047f9fd293030fded439418",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientSections",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientSections:660"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.quotientSectionMultiply_range_finrank_colon",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ColonHilbertStep",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a0b3aaeaaa1b51eab3309e4906c62cf1b10b9e14cdb6f8a16fc19e752528abb6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ColonHilbertStep",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ColonHilbertStep:1433"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.quotientSection_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0fc7f761c8a879fbfabb3bb4377abeae6bcdc75f66c759413974ec79a9e716e1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientSections",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientSections:474"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.quotientSection_finrank_zero_of_no_variables",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertZeroVariables",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c9590f91a91014abb75b51d4a4826d551279f87deb5e58a9bced99bb70e4f110",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertZeroVariables",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertZeroVariables:171"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.rationalDegreePolynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PositiveDimensionalHilbert",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ee203a5872b98344b957e21071ef5d6275c55de4daf7abb98169fe23631d4c93",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PositiveDimensionalHilbert",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PositiveDimensionalHilbert:3025"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.rationalSectionHilbertSeries",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PositiveDimensionalHilbert",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ee0bb9293c032767f678bd5de9391b0d24ad49e6b15bebacf48d63d1a3516cf2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PositiveDimensionalHilbert",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PositiveDimensionalHilbert:2547"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.rational_hilbert_numerator",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousHilbertPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7df27f2e1f11295ba8a0818cff371596019dec00253431532a74ad214c4fcbaf",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousHilbertPolynomial",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousHilbertPolynomial:307"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.regularSequenceHilbertPolynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PositiveDimensionalHilbert",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ed43c909f192bf080b0878e91ecc269132a54c2598dbc5cd93d157173eb65b6d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PositiveDimensionalHilbert",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PositiveDimensionalHilbert:4606"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.regular_prefix_series",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.RegularSequenceSeries",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9f5da9942e17d3d678bc24a59fd1b747a8ea63a869547bd56b530f912ff0fee4",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.RegularSequenceSeries:489",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.RegularSequenceSeries:489"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.sectionHilbertSeries",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.HilbertSeries",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9ec7bdd21cd0fe7fbb6b2b56711ce66c3f1623e5c3cb5b3bf53198ab170b7f10",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.HilbertSeries",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.HilbertSeries:301"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.sectionHilbertSeries_colon_step",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ColonHilbertStep",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0ee7b1d520ff31464fd9b406bd8a3e6c10f378af034fdf278827dd8e41fbe68d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ColonHilbertStep",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ColonHilbertStep:3214"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.sectionHilbertSeries_coordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousHilbertExistence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5485d096809143cdcc8ff1559c3f5950221210b6d2c1975d3549d3f5b111e9bb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousHilbertExistence",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousHilbertExistence:1204"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.sectionHilbertSeries_no_variables",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertZeroVariables",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "53ce609f4e90b2db7d7801d6b8741c79c1022c559683a71e4c3c2f4526d6bdf9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertZeroVariables",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertZeroVariables:625"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.sectionHilbertSeries_regular_step",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.HilbertSeries",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "74f4bddab3cf588b093bee0a29614d971e7b30fd828f51241bc4632708f862ee",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.HilbertSeries:720",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.HilbertSeries:720"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.sectionHilbertSeries_rename",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousHilbertExistence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dc18e9f62314a9416c26fc18d3343fa12e61d953cf94192fa8df83d6c13c32ab",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousHilbertExistence",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousHilbertExistence:849"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.shiftHilbertPolynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.ColonHilbertPolynomial",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9395458646bd3beeb9aaaadeaf1529b4937fe0f55ebe67eb35d65860a7546f35",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.ColonHilbertPolynomial",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.ColonHilbertPolynomial:297"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.shiftHilbertPolynomial_top_coeff",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.ColonHilbertPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d45c4ff223939f71a0666439621a2d47db7a49fffefe07cd8c30925cb3be7545",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.ColonHilbertPolynomial:1296",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.ColonHilbertPolynomial:1296"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.stabilized_colon_polynomial_numerator",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertDenominatorReduction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1d0e01f3762fe12c18503b3db8edee25710ef9b03441317b7f517f919d5eb38e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertDenominatorReduction",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertDenominatorReduction:454"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.stabilized_iteratedColon_series",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.ColonSeriesTelescope",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "657d162888ce06520c47f987f034510781995af747d4fd98ca24d8085a1e057a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.ColonSeriesTelescope",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.ColonSeriesTelescope:3171"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.stableColon_series",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.ColonSeriesTelescope",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4ebd6b60d61e11de82e48ef4704ee914e6d17270d443428b5a462562c271f72e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.ColonSeriesTelescope",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.ColonSeriesTelescope:2103"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.AdicInjective.adicTorsion",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e0a639c0a4cf4c652bc0c8dbe0f9da9bec59f7dce11a0943da2d772f95d4ee0c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:981"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.AdicInjective.adicTorsion_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f77ad1036c2e8d5538bcd5ac7456840038092155428f6791c4932fc87a5a8a15",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:2482"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.AdicInjective.exists_power_inf_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "36210e2d417ef39c536f082cd5762699166c68599b3631acda8815a0ec9bb3ad",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:2090"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.AdicInjective.fg_uniform_exponent",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "921514b3a10dfdab63efde53abe3ab0fbb26d1e84e6b1520a36bf81810251b05",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:1547"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.AdicInjective.mem_adicTorsion",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e04b5ae5221fb9429ec87097b60b7e305974c8710f7e0a02521d505b0f9694b0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:1269"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.AdicInjective.torsion_mono",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "93bceb94e9259599f2c12772e56f71b599c82e36f855d43cd0a79ad30b2f76d5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:1090"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.AffineBlowup.isBlowup",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cbb0fe8b2cf5ecc8444c23d9f4a32baf706eeec9d1b10ff92bc852ea42567c4d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing:1924"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.AffineBlowup.projection",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b445b35a95fdc2bd62df344f8fed372c65fac723ad69c042cf10a042f6864efb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing:1802"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.AffineBlowup.projection_proper",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2cbc2ab5c57d7c34f4d3d5088a20121ffe2b240decec699f50a2b51a1560a8b4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:337"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.AffineBlowup.scheme",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "93be7b329e41d9f063341643046a9f61485f542c97b479e13bb1be610b3a1d2c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing:1708"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.AffineBlowup.scheme_isIntegral",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7bc5e8aaeb3868ab6b83db8cab5e712e6c463d333bd14c8fe6befeb7cc7953df",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:6691"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.AffineBlowup.scheme_isReduced",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b0d1795f7bbc81a9c7e6370ec13ccbe8aed039c955053590be0a77a646b67591",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:6578"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.AffineCohomology.affineHasExt",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a434d8e9c0e7292d11977f6e7a81d96af3874b52195846e1dd99cf2883b0878b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:37154"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.AffineCohomology.globalHom_tilde_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2cf398725942870a8d9d094db8336ce1840cb7d726e6b547211313b7a9660dc0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:36279"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.AffineCohomology.quasicoherent_ext_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "75cef60b88ca859b383b08d1f77868569464ab2631062fdf5e6e0cae411cb96d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:39055"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.AffineCohomology.tilde_ext_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "60f653cae4102bbf2e16cbf2bc3760837ce1635a1d2690f9c76981abc156b244",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:37238"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.AffineDenominators.Aux",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "inductive",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "635fee3ac571358f87cb5e18105ea27be99e7394285116231da2c96cbf4c2370",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:8322"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.AffineDenominators.Aux.casesOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "82e8535567dcd406334a7ffa0cc6e7aa0ae6cccaafc913056c5ea56747794179",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:8322"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.AffineDenominators.Aux.existence",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b13fa2f856fa1889ff9312e86bc6dddd77f1957aef48d4c0bd76c9411cfc6133",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:8322"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.AffineDenominators.Aux.mk",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "ctor",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1ffed619053de8fca38d7ce463b78dc8dee129bb9c641e04aeea8aa6ba4d3738",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:8322"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.AffineDenominators.Aux.of_eq_iSup_basicOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7d8c42e40056f73322043ef5a051718b50b28f78a485f03a16ce910cf684cc25",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:9493"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.AffineDenominators.Aux.of_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ddbb5e982819e2b859657e250d84ec9bfcd5bb3478c09d008a6de0cf12bcf51c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:8718"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.AffineDenominators.Aux.rec",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "rec",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f1fe7b80762a159bccb33e2f6a569d952b047754a5ad6a52cd9d302283dda305",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:8322"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.AffineDenominators.Aux.recOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f472fe49e083223d143176775ce349a4cec9bcec376b15cb26c761be7ab4a26d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:8322"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.AffineDenominators.Aux.uniqueness",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "11d2b00ca0f2bdf06d5a5388732d457173c9fad8a76d280b9042f9ca2bad53dd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:8322"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.AffineDenominators.aux_of_isCompact",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bb801e3c9ad4cf70b8b17510079cad0b9ea4ee11da27e8ecedf082fad9c8adb9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:17182"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.AffineDenominators.cokernel_is_torsion",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cb482f5f6518f2d2a1edc56a3b7153cdce5473d1ad94448d7edd4a620218d731",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:20595"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.AffineDenominators.eq_zero_of_cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "abef9c45eb09b7ac844f051bb2783c95fc5ed6ea68b0de741c2d303842ffd200",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:17944"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.AffineDenominators.isLocalizing_iff_aux",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8376acd04533873807472c653d141378a4f7974aa1720e2525d7f241ae54c17c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:16321"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.AffineDenominators.kernel_is_torsion",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "518b2b89ef22bd906c307b6f8b6319750e38c4f2762657d9f5760f3dfd8d0684",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:18837"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.AffineDenominators.power_in_ideal_of_generator_powers",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ac3c98db29ac1c4a877efc0672cb62ad44fcd729b8f0087f7d039b7432abb33a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:18462"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.AffineDenominators.res",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "78c81ec595192b7f2417f509159093ca521f65e7ef95e78787be7a8cbb8633c8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:17577"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.AffineDenominators.res_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9148cd964f0f4719c60acc4562b804340288d41eaf3dadfab0be89478ebc48ae",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:17715"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.AffineDenominators.torsion_free",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "62add3afd864798f7728ac44d618d5dc1c488a4cb29b35e88e8ba6dcabc88b21",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:19597"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.AffineDenominators.torsion_in_kernel",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "70c97d809592961677ba13632a20a75b1a36e5133cf78c254b829fa4ab148519",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:20216"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.AffineSchemeCohomology.affine_ext_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7e49a2875ae2ebc0650d95300f9b17ef6976371bbfb1e328aa260f29a6db68a4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:41952"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.AffineSchemeCohomology.hasExtScheme",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "551f6c1e1e2b7acb1900ee76529dfda5b7c4a75e67950c28dde4a7ed383fd27f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:41858"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.AffineSchemeCohomology.restrictionEquivalence",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d846e3d745c2f787a15475159b0a6410cafa77ba1edc89fc2a43fd0cf34b9cef",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:41422"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.affineCenterIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalExceptionalComparison",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7b41b12bc3290508149e4541781f88a259f3555368bcec5bfab891d531105139",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalExceptionalComparison",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalExceptionalComparison:446"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.affineRestrictionIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "20d563de5a44449963bca248669969373f6658ef97d627025a036cabccf84493",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupRestriction:1109"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.baseChart",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupAffineSquare",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a51072c2a28b686c897d6f807c3679002f60bb2f3cc4096c0fe1ed1d3e1fc731",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupAffineSquare",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupAffineSquare:287"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.baseChart_isOpenImmersion",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupAffineSquare",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9579c7159b61c1f65d5686c408544b76cfe2d629021b69d9a74c60580f79aa81",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupAffineSquare",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupAffineSquare:554"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.baseCover",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c5dd54779b3a3ee153802c3b3d00f499d5bfd123cdecc99e6c53f0ac053fc9bf",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing:2340"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.centre_transition",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ac78ec6abfe81b3f99b97900eeaa973e6660b81a51f0cf091fb21f2b9a8593c8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing:3037"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.complement_dense",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1c90ff952b4f46df76fc03788f36c2e947f270fd85e87f6192da810dd93b6073",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:8994"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5ed69ab76fef0b9826625543fcdc74a035844fea73d7c9f62ffafa8575ebb673",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing:5846"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.cover_projection",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3a3a1fbe4f6b17d51fa901774a215bc2c1f0908f80462a95575a5199dcfe22ab",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing:5905"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.cover_projection_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6b814c1f4100af51a2fe408e9b6b1d8bf65a3ea019d593f54d4ca54a3028c9f8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing:5905"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.cover_range",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9326e000b93623fa15f95c3d9d92d5bbe60cd16951a3696c7451b504aac38e31",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:8649"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.diagram",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3c1eeae4477bf51e0b799738432593696c035dff2c81380a5aeab7b8512de58e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing:4863"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.diagramMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4620e4ec5a57c4adc2d1db197db562bde95e33cc5db55ea6937c82150e18d9bd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing:5026"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.diagramMap_equifibered",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b86063963ac2af4ee96f65e0f579eb9601b05b4149e430a64a57c50b8b522b42",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing:5182"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.exceptionalInclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6de9c6c9b1a36fb1fed472ccf5fce497ed14159231271b0b87c9580732b38dc7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupRestriction:358"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.exceptionalLineBundle",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1c50ccd50d651847b06488dd31635a246db3d6275aaba6fd4745d71e7ef62f9d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupRestriction:269"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.exceptional_presents",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c6e08b21f9cbdcdabe7b0bb849186c0260c4e425cda6c1a10e0454a7eb203285",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupRestriction:501"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.exists_ample_exceptional_power_gt_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupAmpleTwist",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "af9fdca7b271b48fa78a606c19f45098ed708d6f40058e1333c48a04123c6b37",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupAmpleTwist",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupAmpleTwist:3505"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.gluing",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "821e4e9821debe61b764a3e6ad56e2561c5e7d459290449d31fa92b931302afb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing:5595"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.hom_ext",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7dbb5b8d00f68a1297da59adc492e975893b4378243b9b7fdf159206b8ffc28f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing:7326"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.isBlowup",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d13f442a6208cafb4408413b203e605cf3c9bc1802193b45a4c83033d5eeaf6d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing:10334"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.localAffine",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "39246f8ce0b634c72c520c031fd18577614a53ab4ea7dbe3103869f6e6fe7973",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing:2442"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.localCentre",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "54f999bfcd84b503aa39afbd6199c00d0e2c4373f7ccb2c7036c6b3b9c494100",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing:2535"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.localProjection",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d848487bda2bc349449773929ba5267af36178e68aeb492c53b4bc602e35d218",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing:2744"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.localScheme",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e3192469169dde34ff25427a9eba87f041b151038a0482c3d8f4670ef47867bf",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing:2643"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.localScheme_isIntegral",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "18078b129fe2387f226dfc370c88d02b2ed52a24b269c50a9d628e464d164126",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:8250"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.local_invertible",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "636ef64cbe3011a8a6eb67cc3d87b1de7bddce31360520b6ff3b28773f95165f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing:3342"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.local_isBlowup",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ce30cf06b3680c1dbffcb2c8b13f7f71639b7804be3d97583c666f0835ca7ff4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing:2885"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.local_pullback",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9a803bbc5ec6192e885f51842e961cf8b9e7ab7d0a2b6291a422c516b9b5ed16",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing:6090"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.projection",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "39ac6d328405d7894d15b7c51d108f8af3a4af7d266894cbecb5993ea7d2f3a8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing:5789"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.projection_invertible",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1330002caf7605c89d78d2f951744e5903a13a65c6bf5fc8cc37995c2cb72c0c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing:6427"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.projection_proper",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6cf236299c4062881eed7df5fef00fa6636b8d4cda10cfea1a36919b45ca4ae9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:668"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.scheme",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "40ffe4cd7c90747d641d9a2ec5156d7df1c61393192ba3fb35e8650530161224",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing:5745"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.scheme_isIntegral",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "758941313ffb6ce8d490c114473b40dad0524264c0891437ad2c3e5c6000304e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:10599"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.scheme_isReduced",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4dab3219177c3847e7964ebf22b37f758419dc6befd4f1fcd8ee1c846c8712f1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:6987"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.test_invertible",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cd34200cb1bbc9b4543723c3814efa7df733a794d5a218ee634fef7631d0ea86",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing:6773"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.totalChart",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupAffineSquare",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bf1c7690610f663313d5a93825fb3e635b77e1875761fb7dca9f65740535f0e0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupAffineSquare",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupAffineSquare:398"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.totalChart_isOpenImmersion",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupAffineSquare",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5c4c2a7d6915b8c277de2ed934ac0ade28b1ba774085be2a2f8d9f5d6cc062a4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupAffineSquare",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupAffineSquare:678"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.transition",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "38ae1ef20f53efea406c3d99364dbf7c07f4e338d71e0fb8448c2d6feaa9bffd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing:3711"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.transition_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "444c7fddebfb9cb0a026ad73b1e213a666ce90f97892aeefe3082b5667d2d70f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing:4433"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.transition_id",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "929c7b46440b50f4fa54f273109a0ff4bdf10ca0a268eb9c6066c51e24190bad",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing:4145"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.transition_projection",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a8193e8e3f859d926d0f506798274f6ee1962e2a893050d2f30cf1d3a2fec54d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing:3879"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.transition_projection_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b488dc80918bd3f2cea9ebcbc2fa228b6f4b35f28fa59b19a175721040060796",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing:3879"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupGluing.universal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "819047e93ef6cc2ecb4d06dead843a347cdcddce2cbdd52fbc30653057bbd40d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing:8515"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupLift.coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "595d44d8b2b51d574dcffd4797f6d173a6d7ebccc61c600c348e312ca189e7b7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:338"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupLift.coefficients_span",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e8ff95dc1e8f2b94b0c8051a475477285525221ae853b673ae55f2015c42fa22",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:742"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.BlowupLift.mul_coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a4ff18e1415b62d262c9d53f0d91a51349d307461a3880f7d1f2c0067eeb5d56",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:509"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.CartierSequence.chart_topIso_naturality",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CartierSequence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "74d24de51a39577be75c45f4a4f2dfeaa4fac7061eeafba9884f1f5a6ba36d40",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CartierSequence",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CartierSequence:401"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.CartierSequence.exact",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CartierSequence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1d93f972f909305b0da3797efbfe9eae1cf593dfefb57953190c9aa2cf87ea43",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CartierSequence",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CartierSequence:2278"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.CartierSequence.restriction_principal",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CartierSequence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "21a15d8b34f07d220233c663d2e5898157b5fdb3bb77dca444eda634de604688",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CartierSequence",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CartierSequence:973"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.LocallyAnnihilated",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalClosedAnnihilatedDescent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8be4d4824bd84c166f229621343490eda7c8809273f77708da3971f425ba5243",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalClosedAnnihilatedDescent",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalClosedAnnihilatedDescent:514"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.affineDescent",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedAnnihilatedDescent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "323d92b480ec6a1c40961fee57b032be773e2697494eb86dc830aeafa8e8efc5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedAnnihilatedDescent",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedAnnihilatedDescent:1742"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.affineDescentAlong",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d5ec85d50e6e3242d4e30feb4140ce9e0d89a7b00efa32757d35e32b4c6c54e1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent:3632"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.affineDescentAlongPushforwardIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eb6da879c250cc3661e604c055dbc93d5623db7da9b82f1d3d49e895690e1b77",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent:4052"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.affineDescent_isQuasicoherent",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedAnnihilatedDescent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "552dd7f50a9f9c8b426f1b661a66aa73d28287c80c828d3cd80487dd7248823c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedAnnihilatedDescent",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedAnnihilatedDescent:1976"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.affineSpecTopSections",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "83497b55a9a59bfc6f10b8f9e8c01142ba46dbc4450750bdec342012091002d4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent:2062"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.affineSpecTopSections_annihilator",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "22edb8897b9adcda0487d24986dc8f305c41de5a68def459cd184ab4a7d294a3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent:3168"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.closedDescentPushforwardIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalClosedAnnihilatedDescent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8627fa2ea0c45f955bc53c7e3d69cba4412bc47ef27b44ec0d3261b55be97697",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalClosedAnnihilatedDescent",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalClosedAnnihilatedDescent:1216"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.exists_affine_closed_descent",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1a9bacd09b3e9a0cd7899e73ad4d4c273ac2fd94cec39990e3e9dd4e4d93ec7e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent:5211"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.quotientModule",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedAnnihilatedDescent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6e096d7ae7aa2c19124a4d61b7e49433c12c06c487dd8ad37f6b087cd2a3d6f7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedAnnihilatedDescent",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedAnnihilatedDescent:1238"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_023.jsonl"
