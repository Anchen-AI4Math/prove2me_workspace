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
      sourceName := "OAI.PiExponent.MatrixTranslationBounds.truncationOrder",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d133ee60a9ee3ade334642d185071cca63fd3ec5b49e5a0961f00b9758f5b32a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds:8029",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds:8029"
    },
    {
      sourceName := "OAI.PiExponent.MatrixTranslationBounds.truncationOrder_budget",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "12afc49d4c6f8a7ad555525d2ce5ad0bbcf9a42a4cce4100ff8cfd6969c028e3",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds:8288",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds:8288"
    },
    {
      sourceName := "OAI.PiExponent.MatrixTranslationBounds.truncationOrder_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e0bca68ea80bc8c361cc74792cd93a43e2b2e434713c84e98bcd36adf89948eb",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds:8108",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds:8108"
    },
    {
      sourceName := "OAI.PiExponent.MatrixTranslationBounds.weight",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bb82124642a4b1d3a2c91747b2d4afc1e30c257bc433bb99e07766057dcde619",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds:316",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds:316"
    },
    {
      sourceName := "OAI.PiExponent.MatrixTranslationBounds.weight_sub_le_weight_tsub",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3b1aa74f8477ff9995671d9b6509901f2e1695d7525c0f0b27cfd75e7ff17d4f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds:5688",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds:5688"
    },
    {
      sourceName := "OAI.PiExponent.NatToIntGrading.component",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "00448309d126f4a4a83e761f33ddb6135bcaf315625f7567c5f4d6efa5426c92",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading:394",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading:394"
    },
    {
      sourceName := "OAI.PiExponent.NatToIntGrading.component_eq_zero_of_not_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b78f38c82486266f6874b4f195837b90a87b1d1901da63fd48273b4775435910",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading:689",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading:689"
    },
    {
      sourceName := "OAI.PiExponent.NatToIntGrading.decomposition",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "db9568c19e6c3a6a32d15a1accde7864004986694a66573264266c1b6ac19219",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading:3367",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading:3367"
    },
    {
      sourceName := "OAI.PiExponent.NatToIntGrading.decompositionMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f7d87d27736ab3058af89631171f4703c07a4ca75034a98b86c1ecb593a3bef4",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading:1155",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading:1155"
    },
    {
      sourceName := "OAI.PiExponent.NatToIntGrading.decompositionMap_homogeneous",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6e9437b54de295dee05765cdc760daa227c0493ee22d3431c5e4693c43b9b90c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading:2459",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading:2459"
    },
    {
      sourceName := "OAI.PiExponent.NatToIntGrading.decompositionMap_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9c230fc700efc4143834b32c87732b82b3320db5b74179210e087673c1769bec",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading:2229",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading:2229"
    },
    {
      sourceName := "OAI.PiExponent.NatToIntGrading.gradedMonoid",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2a45ce24a0235a5bde191dc8198291dc130748ffd83cd28fb9045a54551c8c40",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading:5122",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading:5122"
    },
    {
      sourceName := "OAI.PiExponent.NatToIntGrading.gradedSMul",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bf33bc6e3e20d642e0fbbe138e56e99b7a1218805469685661cf4cd19fe114ca",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading:4388",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading:4388"
    },
    {
      sourceName := "OAI.PiExponent.NatToIntGrading.piece",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5e4a7183e1ae1a9ac8f7214393e4bc28e14f5a9ddf01259f7fceff42f9157234",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading:288",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading:288"
    },
    {
      sourceName := "OAI.PiExponent.NatToIntGrading.support",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0cc2e46a5e5101c3e78acc699fa6c007dce9c492b9deabed106ff685833347be",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading:555",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.NatToIntGrading:555"
    },
    {
      sourceName := "OAI.PiExponent.NefAmple.combination_denominator_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NefAmple",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "42f02c64fb504c3960b3b510d639957fefbd5bca6621b1776d9b6051d82d98c0",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NefAmple:2466",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NefAmple:2466"
    },
    {
      sourceName := "OAI.PiExponent.NegativeTwistPresentations.cancelIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "74f6742762e04504cbc27ab43680d297405a8c62358512dd2bbb3e63b05a12dc",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations:561",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations:561"
    },
    {
      sourceName := "OAI.PiExponent.NegativeTwistPresentations.coherentFinitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "793382546ac6f1dad3562b9f69211d4b47193a96648d870c23b31cc3a3711383",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations:4310",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations:4310"
    },
    {
      sourceName := "OAI.PiExponent.NegativeTwistPresentations.kernel_isFinitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "05fc240db5eaaaac9ba2811b5db764a29ec9d42bb3a3fff3a26f60eb0bed9a19",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations:2446",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations:2446"
    },
    {
      sourceName := "OAI.PiExponent.NegativeTwistPresentations.middleIsoBiproduct",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c1eec1dd50d75683960cba4da94cf6fe5e56ef96870a74db6e1445edf261281f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations:1802",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations:1802"
    },
    {
      sourceName := "OAI.PiExponent.NegativeTwistPresentations.middle_cohomology_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c0de8c761203f4dd171bf9aba82556a848abc9c99698ac085c61bc688134f43a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations:3145",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations:3145"
    },
    {
      sourceName := "OAI.PiExponent.NegativeTwistPresentations.middle_isFinitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3cd63dad18b32322cfc57f4e395568a0328563e89fc61c07774b8bfbcec0c6a8",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations:2075",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations:2075"
    },
    {
      sourceName := "OAI.PiExponent.NegativeTwistPresentations.presentationMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "27223233c95bf12ad228c59e977c6523bced38205ad2ef2be07f63c765e2aeec",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations:1037",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations:1037"
    },
    {
      sourceName := "OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bb9d6858012ffee272408f3e8959361bd44a182336c6014097ac77f04d7ffbe5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations:1238",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations:1238"
    },
    {
      sourceName := "OAI.PiExponent.NegativeTwistPresentations.presentation_shortExact",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "05129f99517a209949f949ecb6e6f644c97acc5c7277ceadb3929722fd0dac8e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations:2887",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.NegativeTwistPresentations:2887"
    },
    {
      sourceName := "OAI.PiExponent.NormalBasisProducts.enumeration",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.NormalBasisProducts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e3c79f0a1708b4a95c9f02b66f18df2ba99b2559bcf2e7fb3f4da5a47d90465a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.NormalBasisProducts:373",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.NormalBasisProducts:373"
    },
    {
      sourceName := "OAI.PiExponent.NormalBasisProducts.enumeration_linearIndependent",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.NormalBasisProducts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d1078c188136648a1020ce1c648134bbfb93df4345ebb8aded0aa1a02d76ed1b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.NormalBasisProducts:512",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.NormalBasisProducts:512"
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
      sourceName := "OAI.PiExponent.NormalBasisProducts.prod_enumeration",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.NormalBasisProducts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "60785f7bb20f4483e1f987604b8d9ab2f380403fb936c2f757fe96bb9f2d4128",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.NormalBasisProducts:1200",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.NormalBasisProducts:1200"
    },
    {
      sourceName := "OAI.PiExponent.NormalBasisProducts.prod_equivFin",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.NormalBasisProducts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "84759e6b3ead4897d6d2da66e392e952a66fd4df0e6f49c81f3339acdb95e5c1",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.NormalBasisProducts:913",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.NormalBasisProducts:913"
    },
    {
      sourceName := "OAI.PiExponent.NormalBasisProducts.rectangular_comparison_le_constant",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.NormalBasisProducts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c69b5c61fb151c556e24b805dd537201cdfbc95e2110bb66acb6b3ac315dbaaa",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.NormalBasisProducts:3704",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.NormalBasisProducts:3704"
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
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity:237",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity:237"
    },
    {
      sourceName := "OAI.PiExponent.NormalBasisRigidity.IsNormalBasis.card_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aadd7fddf94f88fda8025be814e769b1b533686edc5d913ecde127f44439a116",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity:2736",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity:2736"
    },
    {
      sourceName := "OAI.PiExponent.NormalBasisRigidity.IsNormalBasis.ne_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8609122b5c677ff3fa0d2587e2ac1f7fda9109af8c6006535cfdbdb54153953b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity:1688",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity:1688"
    },
    {
      sourceName := "OAI.PiExponent.NormalBasisRigidity.exists_normalBasis_containing",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0e105247a8b314f5448f995a95d7d1fc1b61835b21731d97b573c385ac3c52e1",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity:975",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity:975"
    },
    {
      sourceName := "OAI.PiExponent.NormalBasisRigidity.exists_normalBasis_omitting",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f0ff8ce4538930505781d34a124a585471096413faedda6f1f3920acbbe8adc7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity:1864",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity:1864"
    },
    {
      sourceName := "OAI.PiExponent.NormalBasisRigidity.exists_normalBasis_subset",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bbdb2aec3407ed6de47b95f043bc89fb3ac62665f6c2726ea6bedd1b3ea9d0f2",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity:370",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity:370"
    },
    {
      sourceName := "OAI.PiExponent.NormalBasisRigidity.frameBasis",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ae6007467e5f1880f254283240c98619a69e3550e22dc843961116db9d795fa1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis:1087",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis:1087"
    },
    {
      sourceName := "OAI.PiExponent.NormalBasisRigidity.frameBasis_repr_succ",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "75ad2d48cb23c4847b2ad100be109ea84367f5606bba3424111d29b7e82c16db",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis:1411",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis:1411"
    },
    {
      sourceName := "OAI.PiExponent.NormalBasisRigidity.frameBasis_succ",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "924a783a85344951874dcd36c8c37c7b4619a2d618b5aacb04eaa0f96e8fca27",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis:1658",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis:1658"
    },
    {
      sourceName := "OAI.PiExponent.NormalBasisRigidity.frameBasis_zero_succ",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ed0d91768f1d289b3120c445d57bb6fe9c46402438c86f8c1d863ccc70fb3c79",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis:2065",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis:2065"
    },
    {
      sourceName := "OAI.PiExponent.NormalBasisRigidity.frameBasis_zero_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9b18d0aecf866a8e797b0a65f3612920ee93aab3d39b37db86aa13569278fac6",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis:1941",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis:1941"
    },
    {
      sourceName := "OAI.PiExponent.NormalBasisRigidity.frameEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "27ec45cec336e96266aa786509fe9d597d64389b0c1f218edd708bf69b6e6483",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis:278",
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
      sourceName := "OAI.PiExponent.NormalBasisRigidity.mandatory_logarithmic_differential",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0deff2ea11bd62f222a7fb6c3a7a457cd06fb94956a3aae0d1e1b8ef62d75b7b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis:2260",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis:2260"
    },
    {
      sourceName := "OAI.PiExponent.NormalBasisRigidity.mandatory_not_mem_span",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b55eb44f5a8059db938081c4eb5e23b61c1ea34f0172e6943ba129b24fc9cacb",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity:2169",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity:2169"
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
      sourceName := "OAI.PiExponent.NormalBasisRigidity.span_mapped_basis_eq_top",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "83f06362b86b895cd7c78137c5ebde0ad1a86f07372cf6527725fd79d5b55c62",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis:2750",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis:2750"
    },
    {
      sourceName := "OAI.PiExponent.NormalBasisRigidity.weighted_normalBasis_exclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bd744d4ac68e4536c7fc35ea6047bbad12065cfa1cce217e18c706b57c5e5c3b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity:5388",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity:5388"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.CartierEulerPair.FiniteThrough",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e66b5af56f000a712a38808352ac690aaf3d155bbdbd7796ed7accc907b4d2b2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair:4777",
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
      sourceName := "OAI.PiExponent.NumericalAmpleness.CartierEulerPair.finiteThrough_closedPushforward",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0876ae4c1f2c2e113110a1e76f3556359c1f3eec3924db85c25dd9ceaba58875",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair:4991",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair:4991"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.CartierEulerPair.leftComplex",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f9dfc6709506f88d6f88083fd9c8231b997b9706af71111ffa807d49752a1ced",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair:2669",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair:2669"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.CartierEulerPair.left_shortExact",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c403b4b32f1b15c52ad721adcc885cc5ac596b6bdf40b53a6146e49239a9971b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair:4184",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair:4184"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.CartierEulerPair.middle",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3b7658a4082385515928e8e0769a8d515f075f6184bfd09fa79ea457c0397f53",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair:2226",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair:2226"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.CartierEulerPair.middleIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5a2b2a88e633e120c99cc17f6e7b9c8fa0b08b1775a092ed3c9b081d22942b22",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair:2329",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair:2329"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.CartierEulerPair.rightComplex",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "917865fc66726dc3014198663c2815305339798d5c180a6eaeb27ca09fbe6640",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair:2899",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair:2899"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.CartierEulerPair.rightComplexIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ada2dff2cf729d0e6cee5c17b423215e88070a7f41a3e65b90f96e3316220b25",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair:3593",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair:3593"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.CartierEulerPair.right_shortExact",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1c9b9507bf6c10b146971c9490f99e7e39c517364f6bd3fe0cc44a75ed123112",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair:4452",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair:4452"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.CartierEulerPair.source",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ced97e14025f59f4632168b1fcfb974e47f2263f8d496ae608dde92a673b6a3a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair:2144",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair:2144"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.IntegralCurve",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness",
      graphKind := "inductive",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0c8d81e0291c5d7e6e3555634c8ab993b1373eab4397ca24b580e5a51c330f51",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness:2677",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness:2677"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.IntegralCurve.casesOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "301fbd16d5596b9f9fa69fa2b5ae1010ac7da4b47ead9f99eb121035b033b562",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness:2677",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness:2677"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.IntegralCurve.closedImmersion",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f0a983f7c6f96c415bb3346a31d61d6c73ef8a82c07168a79d55fad764d90653",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness:2677",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness:2677"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.IntegralCurve.dimension",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0a58ea7003ac689b437852e4a805e9b9392020cb53c0a3daae43ad53baea38a8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness:2677",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness:2677"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.IntegralCurve.embedding",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "26fb3a5595e6f4c9f7169ea1e4bd4f88e4b4615bc2562f5a178ab503d1ae1ac7",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness:2677",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness:2677"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.IntegralCurve.integral",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9345cb2f2e278bb2c8e1224b6a7c64ebea4afb058446a431a761e7b2a6f27ec1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness:2677",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness:2677"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.IntegralCurve.mapClosed",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.NumericalMarginRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5b37d98258ca10007a8d56deb2b42a11e7ef8a499c14bedc17a4a716c7117988",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.NumericalMarginRestriction:668",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.NumericalMarginRestriction:668"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.IntegralCurve.mk",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness",
      graphKind := "ctor",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "43135b4cb2380b8894c3b3e9188ea779299a176e8f06174936a7d7e1362e3e3d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness:2677",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness:2677"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.IntegralCurve.mk.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d213484ecd57b28254e44acf801b62ea99e8ffbbb76c1622b78be13be3444ce2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness:2677",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness:2677"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.IntegralCurve.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2375eda44ae43c6be370f7de6d5ec1c3822e910847e5a45c1bbb43e646028cdf",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness:2677",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness:2677"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.IntegralCurve.rec",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness",
      graphKind := "rec",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "775c4095b67a7f68ffe07ca7de2fff5b5b6198c68f77a9fee2fcd28e37bc7bdf",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness:2677",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness:2677"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.IntegralCurve.recOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7254d1c2d28463e6314de6cf69c997bf40a167d3bc8b9d111959370f8cb24b2a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness:2677",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness:2677"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.IntegralCurve.scheme",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9fd122c4825cfba2a8b748ca557b2e3da6fba6353cb13798f6b731a42dc18b78",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness:2677",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness:2677"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.LineIsoInvariant",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9a496a876a21a27a7ae2dd4450e2c384b5f7c33d53590c9cc5693510039ec36a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra:381",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra:381"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.LineIsoInvariant.mixedDifference",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5ab6e87ebd1ecaabb0f599eb008b8df1cd4434184dc9b4a02c21fcfd73b3a9b3",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra:3000",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra:3000"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.LineIsoInvariant.tensorDifference",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "58ca563468dc150868cf6c835206b10f42df8cb9a3b7f58d4a66d557fabf74dc",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra:2675",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra:2675"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.LineIsoInvariant.tensorShift",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e21fdf45d220732db00a231562b620b64818a1cee4861b403eac9872a7d84be3",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra:3268",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra:3268"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.LowerClosedNumericalCriterion",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.NumericalSlopeInduction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "78e2c7ef942185895b9a012964506981590e49032967771153bf66c825bbdd63",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.NumericalSlopeInduction:331",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.NumericalSlopeInduction:331"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.MixedDegreeLE",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "22b80d0233725cc5b6136286937c02c11d9b9606ba4d7ff241803fdf56b48aea",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerPolarization:449",
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
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeTopology:253",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeTopology:253"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.ampleSlopes_bddBelow",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeTopology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6cd7de91576181cd8688cec915041290043543f02aab23cae8f1f1c8eeaca59f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeTopology:465",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeTopology:465"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.ampleSlopes_nonempty",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeTopology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2d22e5b3805587bf05476b530d0abc2b7420807b543826988d1f1d28411e82db",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeTopology:665",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeTopology:665"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.ampleThreshold",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeTopology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d6d407dab462ef10283e46eb9cfa90fd62cd9790baae0b79bf827c9832e6bc46",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeTopology:390",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeTopology:390"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.ampleThreshold_nonneg",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeTopology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "46d2b138b23fcac0bf9a43ac85cec28b404c7d13460336d974e2f26366bf5d5c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeTopology:912",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeTopology:912"
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
      sourceName := "OAI.PiExponent.NumericalAmpleness.ample_of_threshold_lt",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeTopology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "162b8276f08ea8b3336fb2e4fc13faa22ac6121e5b58f084ac8e4cb43583ff41",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeTopology:1191",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeTopology:1191"
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
      sourceName := "OAI.PiExponent.NumericalAmpleness.ample_section_zero_nonempty",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleDivisorDimensionBase",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "101588c81bd0cc7e0dce99ee158b33f190d0583bb84f035545b448186c2c7a8f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleDivisorDimensionBase:3210",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleDivisorDimensionBase:3210"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.ample_slope_of_cross_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "18aa5cd2b087307d5b4804befcc5a729284d567b14c52dfd7c27fb55061cd07e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra:2127",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra:2127"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.ample_slope_of_polynomial_pos_of_lower_criterion",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.NumericalSlopeInduction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "80a29203fc62be0d7dc37ff230a77b631fb7051d337a12641f6526684f08e07a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.NumericalSlopeInduction:2863",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.NumericalSlopeInduction:2863"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.ample_slope_of_topEuler_pos_of_lower_criterion",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.NumericalSlopeInduction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8f31d43d41fe2338e85ce67da1e8d782725a8142007eae3992ad09f46d7c0623",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.NumericalSlopeInduction:1685",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.NumericalSlopeInduction:1685"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.ample_tensor_nonnegative_power",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b21ebdf3d02a993ddc7297d2c9ef94594ead6caf5568667acdcd0807b6d3a490",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra:1770",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra:1770"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.cartierMiddlePowerIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerTwistTransport",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0b0e0a72f605866686c79ecdd7eddc00d7d364da6df4e3f4335ef4f85e081988",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerTwistTransport:740",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerTwistTransport:740"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.cartierPowerMultiply",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NakaiCartier",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "98bcaf9e7555d4c87c4c2456888e47e1bc815b398737e1d55b040ff4fcacbdbb",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NakaiCartier:696",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NakaiCartier:696"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.cartierPowerMultiply_mono_of_mono",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SectionCartierRegular",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "065e441b33d99cfd502922a3098159585a6daa714fe476472240a142fa118620",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SectionCartierRegular:458",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SectionCartierRegular:458"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.cartierPower_zeroIdeal_frames",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SectionCartierPower",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ee27c4fb69029a4f6d6ba344fc553a6e3ef46dadd0fe54c62b419f61d34cb68b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SectionCartierPower:957",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SectionCartierPower:957"
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
      sourceName := "OAI.PiExponent.NumericalAmpleness.coefficients_span_top_of_section_cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c61c729ecb5932e0bfbcbf6c928237d597d3ec0982114dbc827da8dfb84ccb44",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice:1717",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice:1717"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.cohomologyDimension_eq_of_quotient_vanishing",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.NakaiCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1390b06b681512bcfc7e2e2ac712cf4b92b049d332d6f1c9153eea4f5521b60d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.NakaiCohomology:5839",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.NakaiCohomology:5839"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.cohomologyMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.NakaiCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c2dbd0b0231cba86350f62209c112d363a54a097502e1b06173ba93ea76d8317",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.NakaiCohomology:291",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.NakaiCohomology:291"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.cohomologyMap_bijective_of_quotient_vanishing",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.NakaiCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8809356a8343273e7bab1c88467d42adf37554f867a03cef6c29bf6588996b06",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.NakaiCohomology:5041",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.NakaiCohomology:5041"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.cohomology_eq_zero_of_projective_embedding",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveEmbeddingCohomologyBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dd3304caae91393947ebccf8ab71553cee69d8d29a5aa6d514f2fd9d4ce10f7b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveEmbeddingCohomologyBound:891",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveEmbeddingCohomologyBound:891"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.curveDegree",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.NumericalMarginRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "adfb027373c3d7840945eef5f02a7446df3bd05f2befbebc43086e12673a29ca",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.NumericalMarginRestriction:364",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.NumericalMarginRestriction:364"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.curveDegree_eq_zero_of_sectionsMorphism_contracted",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NakaiAmpleFromSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b5c7c5a78394568de937121aa00e5b4fdf3a87dd193d7d2bef39e6b62f135f61",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NakaiAmpleFromSections:729",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NakaiAmpleFromSections:729"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.curveDegree_mapClosed",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.NumericalMarginRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4403dd836148cdd278cabfe0c3ef1490707a8a84664a98019d4303607a585f79",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.NumericalMarginRestriction:951",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.NumericalMarginRestriction:951"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.curveDegree_pos_of_ample",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleCurveDegreePositive",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "377ec10d8536c6f8a1e0491ed0a04bd3aedbc6803b81fcc8095672e0e6620181",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleCurveDegreePositive:6729",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleCurveDegreePositive:6729"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.curveDegree_pos_of_uniform_margin",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveDegreeLaws",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9d8090765b592e7c841a574bf1a2f8d5a950c7708f973f77c47f0a6d36eb0032",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveDegreeLaws:2171",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveDegreeLaws:2171"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.curveDegree_pow",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveDegreeAdditivity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "18a2edba6a5cbac5b1591f97eec766eb25f298c29a7e776f4f5dbc7b5c19bf5b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveDegreeAdditivity:7299",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveDegreeAdditivity:7299"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.curveDegree_pow_of_ample",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveDegreeLaws",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a98bbedde0030d56db8019cd06b1b53a8bcd554e0c1400d163441c8d8c25c542",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveDegreeLaws:728",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveDegreeLaws:728"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.curveDegree_tensor",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveDegreeAdditivity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f492c408f46f7e1b18745c83ec9e06ba771fddb31312610f16bacdfac39a7596",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveDegreeAdditivity:6424",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveDegreeAdditivity:6424"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.curveDegree_tensor_of_ample",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveDegreeLaws",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "701bcae6d137b451b16d7bbb0cb157e45969b24fa72454de377646a421f791fe",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveDegreeLaws:1211",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveDegreeLaws:1211"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.curveLineCohomologyTwoZero_of_ample",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveDegreeLaws",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5a335053f3c8b334520af9d31d376bf375dc82eb60a28a0b34fde6d6798118c1",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveDegreeLaws:256",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveDegreeLaws:256"
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
      sourceName := "OAI.PiExponent.NumericalAmpleness.discreteTopology_of_dim_le_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerZeroDimensional",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5744e9bfb958083b02d74026b711154a06723e6cc61405f494bcf349bea93604",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerZeroDimensional:350",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerZeroDimensional:350"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.eulerCharacteristic_eq_of_le_of_cohomology_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerCutoff",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1ce57c2afc935ea8c9c4df672b440068ac1aabc4aeee7c292a4bc2ab5896fd59",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerCutoff:468",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerCutoff:468"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.eulerCharacteristic_eq_pred_of_cohomology_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerDifference",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0bc237ebb39eccd417d84f965b4c4f6fe7e95c274ac6420699f974bdcc7986a7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerDifference:397",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerDifference:397"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.eulerCharacteristic_eq_zero_sub_one_add_tail",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.NakaiEulerGrowth",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eed719bdda40ccd3ccfea8f162b4c31819904d6680a2754f46fbe12b639696d5",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.NakaiEulerGrowth:923",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.NakaiEulerGrowth:923"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.eulerCharacteristic_projective_eq_dimension",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerCutoff",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a83d4b7295eeab943be91eb8fd239ffd43c2356532639dc305c9e687298ce5b4",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerCutoff:1113",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerCutoff:1113"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.eulerCharacteristic_pullback_cartierMiddle",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerTwistTransport",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "10ec87d09406f2f37132e811a286c5f8b6818c3c2ed173ec0db593caf1336fef",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerTwistTransport:1542",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerTwistTransport:1542"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.eulerSlopeCoefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerSlope",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "06d67be61241cccaa8714a75bb7b9f7c5b25e3c40cac1067a4370ca5d9a62864",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerSlope:396",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerSlope:396"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.eulerSlopeCoefficient_succ",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerSlope",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d6b9c3632add3d1ec236ca6364659fc66c16f331b7c01ccf1aeb98fc0916ffe1",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerSlope:4208",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerSlope:4208"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.eulerSlopePolynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerSlope",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8e254eb72ecea3cf35336e3fd26a5091e017df00093afac720847eff792abbc8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.MixedEulerSlope:583",
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
      sourceName := "OAI.PiExponent.NumericalAmpleness.eulerSlopePolynomial_derivative_margin",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.NumericalEulerSlopeInputs",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "81b627dc2ec6557941aa23651d3e05d31c4d3b59d0a4d588d83148d81ba9effa",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.NumericalEulerSlopeInputs:1067",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.NumericalEulerSlopeInputs:1067"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_018.jsonl"
