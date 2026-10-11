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
      sourceName := "OAI.PiExponent.MatrixArithmetic.truncationOrders",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e5ddcff4addb67930e5989ac8fb20bebee5ecd43f111be1b5e2837717f82121f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:6617"
    },
    {
      sourceName := "OAI.PiExponent.MatrixCounting.lowIndexCount",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f312d71befd7a7f4af25b7bee7c322982c9d29571b79938719c728e38fb5f5b1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting:447"
    },
    {
      sourceName := "OAI.PiExponent.MatrixCounting.rationalLogWeights",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "38d3ed072c371bb871c1c1986d06d5b6b48af53449243541d8080eff05ba3991",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting:619"
    },
    {
      sourceName := "OAI.PiExponent.MatrixCounting.rowCount",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7954110a276ead7f2a49e5073418ba4ecfc17e7f9a33de9bd482fa89f88e602e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting:239"
    },
    {
      sourceName := "OAI.PiExponent.MatrixCounting.tendsto_rowCount_normalized",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b576bf07ee19920a3f2068920da62e9a6795bbb59bbbaa7bd3169410f3f3319a",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting:1212",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixCounting:1212"
    },
    {
      sourceName := "OAI.PiExponent.MatrixTranslation.det_matrix_translation",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a367e96e29e6f34fed3c2816c4667f8c73a7769c14341e0b0b4685b8e7749ead",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:10656",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:10656"
    },
    {
      sourceName := "OAI.PiExponent.MatrixTranslation.formalMonomialImage",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5dea6349ff9c233c42675df66c6cebce9ab70403328b1b1c95bc13fadb69ca3f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:5652"
    },
    {
      sourceName := "OAI.PiExponent.MatrixTranslation.periodCoordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "25cf7e497f7a9c8bd12da4dad7c421acf2fdc2ff3617a728a93ef1e7a8ce9325",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:264"
    },
    {
      sourceName := "OAI.PiExponent.MatrixTranslation.periodMonomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "00f510252ddb80f83f5274bf860cdd2cab858352b1ba8b60d63131111a111d39",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:400"
    },
    {
      sourceName := "OAI.PiExponent.MatrixTranslation.transverseIndices",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c6cfe56913921e51b061d1b65d25f7fb23a4d9fd4e04b5a47b355592b769ef8f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation:2572"
    },
    {
      sourceName := "OAI.PiExponent.MatrixTranslationBounds.truncationOrder",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d133ee60a9ee3ade334642d185071cca63fd3ec5b49e5a0961f00b9758f5b32a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds:8029"
    },
    {
      sourceName := "OAI.PiExponent.MatrixTranslationBounds.weight",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bb82124642a4b1d3a2c91747b2d4afc1e30c257bc433bb99e07766057dcde619",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds:316"
    },
    {
      sourceName := "OAI.PiExponent.NatToIntGrading.component",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "00448309d126f4a4a83e761f33ddb6135bcaf315625f7567c5f4d6efa5426c92",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading:394"
    },
    {
      sourceName := "OAI.PiExponent.NatToIntGrading.component_eq_zero_of_not_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b78f38c82486266f6874b4f195837b90a87b1d1901da63fd48273b4775435910",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading:689"
    },
    {
      sourceName := "OAI.PiExponent.NatToIntGrading.decomposition",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "db9568c19e6c3a6a32d15a1accde7864004986694a66573264266c1b6ac19219",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading:3367"
    },
    {
      sourceName := "OAI.PiExponent.NatToIntGrading.decompositionMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f7d87d27736ab3058af89631171f4703c07a4ca75034a98b86c1ecb593a3bef4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading:1155"
    },
    {
      sourceName := "OAI.PiExponent.NatToIntGrading.decompositionMap_homogeneous",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6e9437b54de295dee05765cdc760daa227c0493ee22d3431c5e4693c43b9b90c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading:2459"
    },
    {
      sourceName := "OAI.PiExponent.NatToIntGrading.decompositionMap_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9c230fc700efc4143834b32c87732b82b3320db5b74179210e087673c1769bec",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading:2229"
    },
    {
      sourceName := "OAI.PiExponent.NatToIntGrading.gradedMonoid",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2a45ce24a0235a5bde191dc8198291dc130748ffd83cd28fb9045a54551c8c40",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading:5122"
    },
    {
      sourceName := "OAI.PiExponent.NatToIntGrading.gradedSMul",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bf33bc6e3e20d642e0fbbe138e56e99b7a1218805469685661cf4cd19fe114ca",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading:4388"
    },
    {
      sourceName := "OAI.PiExponent.NatToIntGrading.piece",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5e4a7183e1ae1a9ac8f7214393e4bc28e14f5a9ddf01259f7fceff42f9157234",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading:288"
    },
    {
      sourceName := "OAI.PiExponent.NatToIntGrading.support",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0cc2e46a5e5101c3e78acc699fa6c007dce9c492b9deabed106ff685833347be",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading:555"
    },
    {
      sourceName := "OAI.PiExponent.NegativeTwistPresentations.cancelIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "74f6742762e04504cbc27ab43680d297405a8c62358512dd2bbb3e63b05a12dc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations:561"
    },
    {
      sourceName := "OAI.PiExponent.NegativeTwistPresentations.coherentFinitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "793382546ac6f1dad3562b9f69211d4b47193a96648d870c23b31cc3a3711383",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations:4310"
    },
    {
      sourceName := "OAI.PiExponent.NegativeTwistPresentations.kernel_isFinitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "05fc240db5eaaaac9ba2811b5db764a29ec9d42bb3a3fff3a26f60eb0bed9a19",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations:2446"
    },
    {
      sourceName := "OAI.PiExponent.NegativeTwistPresentations.middleIsoBiproduct",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c1eec1dd50d75683960cba4da94cf6fe5e56ef96870a74db6e1445edf261281f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations:1802"
    },
    {
      sourceName := "OAI.PiExponent.NegativeTwistPresentations.middle_cohomology_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c0de8c761203f4dd171bf9aba82556a848abc9c99698ac085c61bc688134f43a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations:3145"
    },
    {
      sourceName := "OAI.PiExponent.NegativeTwistPresentations.middle_isFinitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3cd63dad18b32322cfc57f4e395568a0328563e89fc61c07774b8bfbcec0c6a8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations:2075"
    },
    {
      sourceName := "OAI.PiExponent.NegativeTwistPresentations.presentationMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "27223233c95bf12ad228c59e977c6523bced38205ad2ef2be07f63c765e2aeec",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations:1037"
    },
    {
      sourceName := "OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bb9d6858012ffee272408f3e8959361bd44a182336c6014097ac77f04d7ffbe5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations:1238"
    },
    {
      sourceName := "OAI.PiExponent.NegativeTwistPresentations.presentation_shortExact",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "05129f99517a209949f949ecb6e6f644c97acc5c7277ceadb3929722fd0dac8e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations:2887"
    },
    {
      sourceName := "OAI.PiExponent.NormalBasisProducts.enumeration",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.NormalBasisProducts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e3c79f0a1708b4a95c9f02b66f18df2ba99b2559bcf2e7fb3f4da5a47d90465a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.NormalBasisProducts",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.NormalBasisProducts:373"
    },
    {
      sourceName := "OAI.PiExponent.NormalBasisProducts.eventually_uniform_cutoff",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.NormalBasisProducts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2f1c7db2fcb3ab1f4f614aff1a5dbd862547dd0e9c85cc6a9b25b1c87f76d0f0",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.NormalBasisProducts:1557",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.NormalBasisProducts:1557"
    },
    {
      sourceName := "OAI.PiExponent.NormalBasisProducts.rectangular_factor_le_constant",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.NormalBasisProducts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ce7cb670dd5f82e8ff5f5578e73f483362a9c29915366b70ec6c333084ea7861",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.NormalBasisProducts:2513",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.NormalBasisProducts:2513"
    },
    {
      sourceName := "OAI.PiExponent.NormalBasisRigidity.IsNormalBasis",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e90fb3d2fe058ee243dbff7d003979d594988cb6513dfd8412fcf0fc13ca9626",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity:237"
    },
    {
      sourceName := "OAI.PiExponent.NormalBasisRigidity.frameBasis",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ae6007467e5f1880f254283240c98619a69e3550e22dc843961116db9d795fa1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis:1087"
    },
    {
      sourceName := "OAI.PiExponent.NormalBasisRigidity.frameEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "27ec45cec336e96266aa786509fe9d597d64389b0c1f218edd708bf69b6e6483",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis:278"
    },
    {
      sourceName := "OAI.PiExponent.NormalBasisRigidity.largest_nontangent_mandatory",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "294a2429974e55315a3a51e8dab317b38f720656b86410b0f4e7ee26f19aacc6",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity:4406",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity:4406"
    },
    {
      sourceName := "OAI.PiExponent.NormalBasisRigidity.mandatory_coordinate_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e17e229a6cd44ef1c9bc53ff72a5222b590e7b67fab92cdd0bc5235bd3f0f7f7",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity:3213",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity:3213"
    },
    {
      sourceName := "OAI.PiExponent.NormalBasisRigidity.normalBasis_unique_of_discrepancy_excluded",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fbe5122c5355c9ea392225ef1297f5c2bd5d6eacc4de04ad83a054c8a9ef0f73",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity:6255",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity:6255"
    },
    {
      sourceName := "OAI.PiExponent.NormalBasisRigidity.normal_basis_differential_dichotomy",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "529e0c82ab8e09e83ebc18336600892c2bb1d04b8fd80de507efaa15e16d08ca",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis:3221",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis:3221"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.CartierEulerPair.FiniteThrough",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e66b5af56f000a712a38808352ac690aaf3d155bbdbd7796ed7accc907b4d2b2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair:4777"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.CartierEulerPair.euler_difference",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8f4fa653d7759e3ebbe9964115b8b1ce65fba047955775a0670426ed68998583",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair:5624",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair:5624"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.CartierEulerPair.leftComplex",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f9dfc6709506f88d6f88083fd9c8231b997b9706af71111ffa807d49752a1ced",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair:2669"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.CartierEulerPair.middle",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3b7658a4082385515928e8e0769a8d515f075f6184bfd09fa79ea457c0397f53",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair:2226"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.CartierEulerPair.middleIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5a2b2a88e633e120c99cc17f6e7b9c8fa0b08b1775a092ed3c9b081d22942b22",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair:2329"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.CartierEulerPair.rightComplex",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "917865fc66726dc3014198663c2815305339798d5c180a6eaeb27ca09fbe6640",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair:2899"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.CartierEulerPair.rightComplexIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ada2dff2cf729d0e6cee5c17b423215e88070a7f41a3e65b90f96e3316220b25",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair:3593"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.CartierEulerPair.source",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ced97e14025f59f4632168b1fcfb974e47f2263f8d496ae608dde92a673b6a3a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair:2144"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.IntegralCurve",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness",
      graphKind := "inductive",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0c8d81e0291c5d7e6e3555634c8ab993b1373eab4397ca24b580e5a51c330f51",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness:2677"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.IntegralCurve.casesOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "301fbd16d5596b9f9fa69fa2b5ae1010ac7da4b47ead9f99eb121035b033b562",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness:2677"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.IntegralCurve.closedImmersion",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f0a983f7c6f96c415bb3346a31d61d6c73ef8a82c07168a79d55fad764d90653",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness:2677"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.IntegralCurve.dimension",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0a58ea7003ac689b437852e4a805e9b9392020cb53c0a3daae43ad53baea38a8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness:2677"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.IntegralCurve.embedding",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "26fb3a5595e6f4c9f7169ea1e4bd4f88e4b4615bc2562f5a178ab503d1ae1ac7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness:2677"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.IntegralCurve.integral",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9345cb2f2e278bb2c8e1224b6a7c64ebea4afb058446a431a761e7b2a6f27ec1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness:2677"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.IntegralCurve.mapClosed",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.NumericalMarginRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5b37d98258ca10007a8d56deb2b42a11e7ef8a499c14bedc17a4a716c7117988",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.NumericalMarginRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.NumericalMarginRestriction:668"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.IntegralCurve.mk",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness",
      graphKind := "ctor",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "43135b4cb2380b8894c3b3e9188ea779299a176e8f06174936a7d7e1362e3e3d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness:2677"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.IntegralCurve.mk.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d213484ecd57b28254e44acf801b62ea99e8ffbbb76c1622b78be13be3444ce2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness:2677"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.IntegralCurve.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2375eda44ae43c6be370f7de6d5ec1c3822e910847e5a45c1bbb43e646028cdf",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness:2677"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.IntegralCurve.rec",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness",
      graphKind := "rec",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "775c4095b67a7f68ffe07ca7de2fff5b5b6198c68f77a9fee2fcd28e37bc7bdf",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness:2677"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.IntegralCurve.recOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7254d1c2d28463e6314de6cf69c997bf40a167d3bc8b9d111959370f8cb24b2a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness:2677"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.IntegralCurve.scheme",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9fd122c4825cfba2a8b748ca557b2e3da6fba6353cb13798f6b731a42dc18b78",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness:2677"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.LineIsoInvariant",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9a496a876a21a27a7ae2dd4450e2c384b5f7c33d53590c9cc5693510039ec36a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra:381"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.LowerClosedNumericalCriterion",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.NumericalSlopeInduction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "78e2c7ef942185895b9a012964506981590e49032967771153bf66c825bbdd63",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.NumericalSlopeInduction",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.NumericalSlopeInduction:331"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.MixedDegreeLE",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "22b80d0233725cc5b6136286937c02c11d9b9606ba4d7ff241803fdf56b48aea",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:449"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.affine_scalar_regular_on_open",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionMono",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c02f72c7991cea9e80d1bef9c632a51a7b85560567ac974c5e88f29a2236845f",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionMono:367",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionMono:367"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.ampleSlopes",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeTopology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9bab48ae42f453f29e882ebb8fe6f3981a3f7f39fac8aabcdaa47a1adc5737b9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeTopology",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeTopology:253"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.ampleThreshold",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeTopology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d6d407dab462ef10283e46eb9cfa90fd62cd9790baae0b79bf827c9832e6bc46",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeTopology",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeTopology:390"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.ample_finite_projective_embedding",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleFiniteProjectiveEmbedding",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "71da1bfa652fdd50bade50f727f4dc47a48298d585619801bcd47e665e96eabd",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleFiniteProjectiveEmbedding:481",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleFiniteProjectiveEmbedding:481"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.ample_section_has_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleDivisorDimensionBase",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ed8b64e10fb295936043eae852da83a19f4a95814e60065901e942e65fb24457",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleDivisorDimensionBase:2145",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleDivisorDimensionBase:2145"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.cartierMiddlePowerIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerTwistTransport",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0b0e0a72f605866686c79ecdd7eddc00d7d364da6df4e3f4335ef4f85e081988",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerTwistTransport",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerTwistTransport:740"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.cartierPowerMultiply",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NakaiCartier",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "98bcaf9e7555d4c87c4c2456888e47e1bc815b398737e1d55b040ff4fcacbdbb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NakaiCartier",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NakaiCartier:696"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.cartier_euler_difference",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerDifference",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6f1702fc8f97bb8226fb1289d463ea74292c959ae8c9cb85978aaa3be929a6de",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerDifference:1070",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerDifference:1070"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.cohomologyMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.NakaiCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c2dbd0b0231cba86350f62209c112d363a54a097502e1b06173ba93ea76d8317",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.NakaiCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.NakaiCohomology:291"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.curveDegree",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.NumericalMarginRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "adfb027373c3d7840945eef5f02a7446df3bd05f2befbebc43086e12673a29ca",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.NumericalMarginRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.NumericalMarginRestriction:364"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.dimension_le_of_local_bound",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerSupportDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "be081442630aa1a43855e8a360dce60ab90fb0991bcb435478610b753c591aa8",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerSupportDimension:400",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerSupportDimension:400"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.eulerSlopeCoefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerSlope",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "06d67be61241cccaa8714a75bb7b9f7c5b25e3c40cac1067a4370ca5d9a62864",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerSlope",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerSlope:396"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.eulerSlopePolynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerSlope",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8e254eb72ecea3cf35336e3fd26a5091e017df00093afac720847eff792abbc8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerSlope",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerSlope:583"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.eulerSlopePolynomial_derivative_eval_nat_div",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerSlope",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "870e20172fbac9c947690516b051fa7a7af5d7946d39f4d14334dc754fd6cdc7",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerSlope:4765",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerSlope:4765"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.euler_tensor_power_difference_aux",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerPolynomialDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9ba4e36e74c284349d45840b683aacd1cff5ca00da0bebde369993493a147e90",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerPolynomialDegree:2356",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerPolynomialDegree:2356"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.eventual_cartier_restriction_section_lifting",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NakaiSectionLifting",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b7937af9d521535f1c0e7875fe282a1b945865f825b7a9370c9476a40541df6e",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NakaiSectionLifting:1479",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NakaiSectionLifting:1479"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.eventual_globalSections_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.NakaiCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2ddc54383968274c6f2c8d8cbab87b0f84ad72a874c7722870d9fef489fb2ea2",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.NakaiCohomology:2993",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.NakaiCohomology:2993"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.eventual_power_section_cover_of_ample_zeroDivisor",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NakaiDivisorAmple",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6f56057e7568305da242e2c64c1b003f6d0bf3423693792a0b71852f5e379817",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NakaiDivisorAmple:2335",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NakaiDivisorAmple:2335"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.exists_integral_closed_full_dimension",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleDivisorDimensionBase",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4c71d6c77d7f394261e49938c6ac36b83e7e0f4ea31ec347b8321a70526a8fcc",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleDivisorDimensionBase:1154",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleDivisorDimensionBase:1154"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.exists_irreducibleClosed_dimension_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.IntegralCurveExistence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "51441406eb59a503d7c9818668fe808c8d2380130a1cc4d415098cf3395ffc92",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.IntegralCurveExistence:2696",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.IntegralCurveExistence:2696"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.exists_mono_linearCombination_of_finite_cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e6c492dde672041e9540a327a3d1b8fc2052e82036c7ae8333c7d18656c372b6",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice:5324",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice:5324"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.exists_power_section_cover_of_euler_growth",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NakaiEffectivity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "567d71188f1885d7063540153ee5c6ff0bcfab8c77a06765792a7f9fbaa0a1f6",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NakaiEffectivity:2987",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NakaiEffectivity:2987"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.exists_smaller_ample_slope",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "08366faab44158fb840d7ddbb0b36b75f9be70e89a9cf38a07a9f32cff521932",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra:3340",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra:3340"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.finite_affine_frame_cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "680676e37f05f2d7e35dcde2ae4c4cde850c10470a4ee0791fcfe275dfe545b5",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice:563",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice:563"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.integralCurveFromClosedFiber",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FiniteOfNoContractedCurves",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b3bf3558fe32e2f9e6de01a0cd87d477533023d4b474d9b95a2545c7288e7010",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FiniteOfNoContractedCurves",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FiniteOfNoContractedCurves:806"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.integralCurveOfIrreducibleClosed",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.IntegralCurveExistence",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dbd507984da18ac0d70395f10d44be984120f0242b0e363b5bc9b50bfb4eeb92",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.IntegralCurveExistence",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.IntegralCurveExistence:4271"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.irreducibleClosedRestrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.IntegralCurveExistence",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d60e3dd0f9833b71e90cc1ce67dc8ee62c7eefdb4ba312c7616b9fefa4ed7894",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.IntegralCurveExistence",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.IntegralCurveExistence:276"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.irreducibleClosedsBelowEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.IntegralCurveExistence",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "218634d13025012c3dc91424ad599538d52422270e77d472fe78a39e99951764",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.IntegralCurveExistence",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.IntegralCurveExistence:1057"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.isAmple_of_integral_closed_restrictions",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.IntegralComponentAmple",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7f74169527dacc8832c1ed1592d3bedae5f6fd057f5a8c853301b3ff4ab2ad64",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.IntegralComponentAmple:338",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.IntegralComponentAmple:338"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.isAmple_of_lower_criterion_of_euler_slope_polynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.NumericalThresholdStep",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f28a4aa56a95a232d840f644e3c699e15a01f3ada268f5e7ea9a7c0aa49d0d37",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.NumericalThresholdStep:412",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.NumericalThresholdStep:412"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.isAmple_of_section_cover_of_curveDegree_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NakaiAmpleFromSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "96107b2e9a97acf4c6d882f75c0c30463a4914383ac08cb5a4407d818ac397ee",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NakaiAmpleFromSections:2605",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NakaiAmpleFromSections:2605"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.isFinite_of_proper_finite_closed_fibers",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFromClosedFibers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "76d6198b42ca5b5605745d7df952913f5c9e974b396f1510ebf01bd7b34fa804",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFromClosedFibers:260",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFromClosedFibers:260"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.isIso_of_locally_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1295953e5ebb94efc9f0c296a136166b067fb8e98b527c2d1019f43c08f83b08",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws:216"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.isReduced_vanishingIdeal_subscheme",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.IntegralCurveExistence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4acb45b3ce5926b96f594aaba76673e3fa41c85b09583c58867de3dc8b66ccd4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.IntegralCurveExistence",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.IntegralCurveExistence:3561"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.lineBundle_cohomology_zero_of_dimension_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LineCohomologyDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "516422e811ebdac1eb6f06a4b536daeb685b22a2b11f78fae12fa67815860a45",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LineCohomologyDimension:856",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LineCohomologyDimension:856"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.lineEuler",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerDimension",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "52c5a52f4c47bd0b58825f52bbcc26f5eb324d185eadfb4c84516cbde7b571b8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerDimension",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerDimension:393"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.linePowerTensorInverseIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "de61fd40752d0556cd95ce2367b0b50432899d72a2a5e17b9ff1703db0a62418",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra:2617"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.line_cohomology_finite_of_ample_all",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.AmpleLineCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4c8abb83a6f7272a153e768481e8a16bdb910c18b644025cb4411a7ac9bdb116",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.AmpleLineCohomology:379",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.AmpleLineCohomology:379"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.localCoefficientAddHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "80bc108116c8073ae9e63d2198e994720ef2f5a574755bd7077c194ebe82859a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice:2652"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.localCoefficient_scalar",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "23b4bf1cd64e39da5a8d9251fa694ee0261cb82aef6263eaa0f5f9cc1c7be473",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice:3522",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice:3522"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedCartierPowerMultiply",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CartierMixedEuler",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "62c7fe69b7ffeb5d746ede835a75188d83104c792dc57aadc571ba8f87428634",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CartierMixedEuler",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CartierMixedEuler:3011"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedCartierPower_zeroIdeal_frames",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CartierMixedEuler",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8d71d44ab93102afadba3506d9c3df2b7a4a716fbe2e217379ec0d0b3f3ffa0e",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CartierMixedEuler:3529",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CartierMixedEuler:3529"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedDifference",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c470ba23ba26ca910afaafb68ccf6e042c220248b71fe59f3cd255b2503da871",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra:619"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedDifference_lineEuler_of_ample_aux",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAmpleDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c521eb02e43b39b686025c8d06c549fbfbeca280a298f9a7aa38cd31567ad644",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAmpleDimension:400",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAmpleDimension:400"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedDifference_replicate_pow_append",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0780abef888ad551840e8fe8ba3f520b753e4706cc31b6bd4489131b8173919b",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:8223",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:8223"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedDifference_replicate_tensor_append",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "15233f33a118f755c29586b67c3daa4effdc7ef11913080ee61dd077fd2bbeeb",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:5575",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:5575"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedEuler",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerTop",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "61a9748539af73aca907a0b346e5e45b047898d4de27010ab322b88e2d678a8b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerTop",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerTop:516"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedSlopePolynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.MixedSlopePolynomial",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "721d83c7fcdb5aa642fd26566f3bd1b891fa7f793b908a9ecc41d1041235bbad",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.MixedSlopePolynomial",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.MixedSlopePolynomial:160"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedTop",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c013946cdd197838b88ba9b046faf50d322062face846c1c1025c514137bd528",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:5090"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedTop_cartier_restriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4b4c1bc76ac01c1c5d113f8def6fc7e0926296501452add182a0d228e00463f1",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerRestriction:3436",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerRestriction:3436"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedTop_curve_margin_aux",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerCurveMargin",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fe4be736d8a0229ff9a5521aefe5aedc70cb404f379f2fe6b5b5897751fa03ee",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerCurveMargin:342",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerCurveMargin:342"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedTop_pos_of_ample_aux",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPositivity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4b78de17f0f66a587b73bd406999295ea76d3fd8a40cce52a143512e428de1ec",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPositivity:845",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPositivity:845"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedTop_tensor_powers_binomial_append",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2a9e6ac480536929b4ae8f4b55a16475977677beee1bafa0cab05e8ceeb0d657",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:11934",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:11934"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.polynomial_pos_at_boundary_of_rational_margin",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleThresholdPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "528a322904985708300b2c549d476ad01e872fbdecaf665b77ec310391b34d4d",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleThresholdPolynomial:3082",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleThresholdPolynomial:3082"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.polynomial_pos_at_left_of_margin",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleThresholdPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a6063fc1cf907a3912012e157841889de7748a4cb7e2601455cd3c111f69e560",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleThresholdPolynomial:194",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleThresholdPolynomial:194"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.pullbackCartierMiddleIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerTwistTransport",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5bac1cf33f28e5a79aab76ed70f0ae1899bcf2fdffb27669adeb96eaa4bb0f1e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerTwistTransport",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerTwistTransport:1073"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.pullbackMixedPowerIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerTwistTransport",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3cf05518b509059006b09ba4fa333a9e3260582c9a480a890b62dc86f1d8bdfd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerTwistTransport",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerTwistTransport:388"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.pullbackSection_surjective_of_unit_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NakaiSectionLifting",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d7962baf89dc81a39d1f88e0b637d47e5c32fc6c23af388ce47621f8fd00860f",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NakaiSectionLifting:310",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NakaiSectionLifting:310"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.regular_ample_sectionZero_dimension",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleDivisorDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e812b6dafe7eaf6e5c106c639e6ccca0ee5379c2ae3ddcb93677fe06ded4e7e5",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleDivisorDimension:3257",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleDivisorDimension:3257"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.regular_sectionZero_dimension_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerSupportDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "315f246baa6a08c3ee54f1895112f633a6fae1156a1b4de88122bf18c2060ac8",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerSupportDimension:3422",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerSupportDimension:3422"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.regular_tensorSection_restriction_shortExact",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "082120728ac29366ca294306b30cda457838e94b4a8f547fedfd9ecf2bd180ad",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair:443"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.sectionLinearCombination",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "75f9fb383075b6d3f8ff24a7093b8a84b46c3547a49ef4bda82a692997d0c29d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice:4518"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.slopeBundle",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "40c87339a3dbb6f7f4c6db57df9ba1b04529e46e4cf4f5478996a14b4a10557c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra:445"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_013.jsonl"
