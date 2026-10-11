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
      sourceName := "OAI.PiExponent.WeightedCompactification.coordinateSection_isoOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.WeightedProjectiveEmbedding",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8671d307e562f679c3dea31ce408d030b0215350c647dc3839f8e5ad847ceb70",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.WeightedProjectiveEmbedding:1030",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.WeightedProjectiveEmbedding:1030"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.coordinate_sectionsMorphism_embedding",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.WeightedProjectiveEmbedding",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d805c21d14144b4b99d5b8e7c252df7cfca85790f5bf072965c936a3297427d8",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.WeightedProjectiveEmbedding:1750",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.WeightedProjectiveEmbedding:1750"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.coordinate_sectionsMorphism_isClosedImmersion",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.WeightedProjectiveEmbedding",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "78a49f1a5765afc8dd6055c843a0e7c9e675c7896e33740e7be3f93feec5f66f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.WeightedProjectiveEmbedding:2311",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.WeightedProjectiveEmbedding:2311"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.gradedImageMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b9f3f7bdd18eb8ad5447aaced6677bb94c88bd303137b6c25aee34ba15fa5fb9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage:1470",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage:1470"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.gradedImageMap_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b3acce3c158cd9168e5b20518b161e5043b2dbab512361778acc895cf0a8373c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage:1690",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage:1690"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.gradedMonomialMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialMap",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "64a8c6dca7599467ef1c8b61736302b5033a6d7b8fbc0b2b24955f03c2f6e6cb",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialMap:1369",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialMap:1369"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.gradedMonomialMapInt",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ed087a4d71054571fb7ad685e0610d264a303bcf55ff485aaaed021e807b664c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage:587",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage:587"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.homogeneousMonomialMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialMap",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c1490339d7dfeb3911939a0cabab8609f40d0b87c7e7bcd80f5efb9c1ba06d55",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialMap:477",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialMap:477"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.homogeneousMonomialMap_homogeneous",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialMap",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "247091604f536817335796561b76fd51d01252029ee301ac4569f7ca23720f39",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialMap:867",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialMap:867"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.imageConstant",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactification",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4d8ae0c732a395067a48fdf40c9a5807e891b3998b0217ed7e212407bee48828",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactification:2233",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactification:2233"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.imageConstant_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactification",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e31b79e107c7da985d3e8b97a8a432a3d59a9b3294f8bf8657ae01299baab168",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactification:2375",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactification:2375"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.imageCoordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fbca04981f3af43d4b751d1e8f49270b96a69a20edb193fc42701fd7dbe70b11",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage:2298",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage:2298"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.imageCoordinate_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d4adec2010e736b6ee000a1481fe2309771f9e4805dd5492562cbe487f492d6c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage:2446",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage:2446"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.imageEvaluation",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "186ad774c60e0bb7f524bdbdfe882e0b45020cbcdfc35a5cdbbf0baadccda1af",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage:2633",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage:2633"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.imageEvaluation_coordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e9c1ede49248f8eb7ecab9444d7f5e9d46bc364f7004d1626e535518558d28cb",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage:2819",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage:2819"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.imageEvaluation_gradedImageMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedAffineParametrization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d014a0df50f702ee74d3ef8cd71531d86073c30668a965a6618d10df239e54f7",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedAffineParametrization:401",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedAffineParametrization:401"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.imageEvaluation_homogeneous_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0b94072ed00504f896125118f13217c1d268e4119f1681ab0b1c19c00af60e61",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage:3981",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage:3981"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.imageGrade",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f007e448ceb7c5efd3c1bd9af74957cfc6eb8b3a42d648547539e407b07f9a52",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage:1209",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage:1209"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.imageGradedAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ebae17a9ff9af2138aaa0bb60173874921628b996f17da48063a11c501331a89",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage:1311",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage:1311"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.lineBundle",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.WeightedProjectiveLineBundle",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "665352f7a06d509984fd6a1e3fa709eab48d004412785bc62eba8ac1c03abc18",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.WeightedProjectiveLineBundle:493",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.WeightedProjectiveLineBundle:493"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.lineBundle_ample",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.WeightedProjectiveAmple",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "47cb4221d73c0aa9e9d4826b9a7989b85e01f18c5e44137ee56c527a37ad5028",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.WeightedProjectiveAmple:442",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.WeightedProjectiveAmple:442"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.monomialHomogeneousIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialMap",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f1f5e80232817def6cf64388baa8c15edf74851b1478a2e13c472c2e0916aa54",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialMap:1600",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialMap:1600"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.monomialHomogeneousIdeal_isPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "df4a2637b3c89f3cf521399ce30d614bdb50d438a4227b38d0a5f670c41e9ae4",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage:2099",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage:2099"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.monomialImage",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f083005d503636e4530a4140649771da640906a43580b13712b8d00b3cf703b2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage:354",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage:354"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.monomialImage_homogeneous",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "597d66913fd548c300809cf7283c654adac5a9bd9a8ec354509d91c1c29ce91d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage:793",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage:793"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.projection",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.WeightedProjectiveStructure",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "01419df45cf986df73234a6978721ba441569fba295e677a01a82b621b2cf4dd",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.WeightedProjectiveStructure:419",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.WeightedProjectiveStructure:419"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.projection_proper",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.WeightedProjectiveStructure",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5c3a6e320077bde97d7b63d0ae8902ec46e3e108ddeb67848dca605a895b8579",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.WeightedProjectiveStructure:598",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.WeightedProjectiveStructure:598"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.projectiveMonomialMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactificationImmersion",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "63084a41e02031ecdd2c0469b08af9f773ee3f940825ed18d50abc31b7e95d2b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactificationImmersion:558",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactificationImmersion:558"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.projectiveMonomialMap_isClosedImmersion",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactificationImmersion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ee59d13231fae89eb3d1c41d8c23c99179e16a3bc76c625e52c7cbe88a112216",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactificationImmersion:2208",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactificationImmersion:2208"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.projectiveMonomialMap_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactificationImmersion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8512ebc4765961381d2af3477b7439f144905324f146f261524886624795d9cb",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactificationImmersion:1041",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactificationImmersion:1041"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.scalars",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.WeightedProjectiveEmbedding",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "905887e05cebb787cb11102a337e191e4b56bc43021b82d35a1f46520e32c20d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.WeightedProjectiveEmbedding:547",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.WeightedProjectiveEmbedding:547"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.unit_homogeneous_formula",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d8fc81795083df9227298e2ad47bc6799dabc12a378d0f53a08adb0cb27bea99",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage:3050",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage:3050"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCurveDegree.coe_integerOrder",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.WeightedCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ddd8a856b24c9184a45cf82f98b20d9f82ccd46c1634aa7a1b9aec4baec5c071",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.WeightedCurveDegree:323",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.WeightedCurveDegree:323"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCurveDegree.div_le_weightedPole",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.WeightedCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1e1e57f403bb8b2d1755328e35e021f894585cbca55bbac14f8ca77c58ed0cef",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.WeightedCurveDegree:2198",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.WeightedCurveDegree:2198"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCurveDegree.integerOrder",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.WeightedCurveDegree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "549d8a6efa1a3e8ecec37f18e9c8fb94cd389bd40a49b643130b9f2937a787f5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.WeightedCurveDegree:142",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.WeightedCurveDegree:142"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCurveDegree.integerOrder_div",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.WeightedCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2378f042aa83eb6c98460c8f82db9d6fbc44fdd417ad40698bd7830d815762e8",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.WeightedCurveDegree:10590",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.WeightedCurveDegree:10590"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCurveDegree.integerOrder_inv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.WeightedCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9ca79e6902ffce416813a2c1a9227c1d031e78f1c42a0bc9d66a6f6a791a18d4",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.WeightedCurveDegree:10388",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.WeightedCurveDegree:10388"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCurveDegree.integerOrder_mul",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.WeightedCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e4961cfc833ae05416177c08ef465ddda6b1f48a344277be346c6d145eed1e6a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.WeightedCurveDegree:674",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.WeightedCurveDegree:674"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCurveDegree.integerOrder_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.WeightedCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cbef4bbd83df82c17269934413167cf927fbd159f1c32764f182c932c8e67113",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.WeightedCurveDegree:508",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.WeightedCurveDegree:508"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCurveDegree.integerOrder_pow",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.WeightedCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e63eb51bf79b16aac4e7f296af4e153399c44ab31b6c9ebb7a79b868bd3ea707",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.WeightedCurveDegree:897",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.WeightedCurveDegree:897"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCurveDegree.monomial_pole_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.WeightedCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a14f4437dfccdfaa86ce0c259ae00959837fcfd8a757d66c9ac6147a7d8c08aa",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.WeightedCurveDegree:2438",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.WeightedCurveDegree:2438"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCurveDegree.weightedPole",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.WeightedCurveDegree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "35c2cfe9364ee6906d3d79b383c5ebea684e9b607aa8b168f8f947665c603c5c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.WeightedCurveDegree:1762",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.WeightedCurveDegree:1762"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCurveDegree.weightedPole_nonneg",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.WeightedCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5edf0920a6b25442e488f0b0771fd78e532d82d576933caff6b827727e78bff2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.WeightedCurveDegree:1966",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.WeightedCurveDegree:1966"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCurveRigidity.ordinary_coordinate_constant",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.WeightedCurveRigidity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3fdde5263902118b2f8f299816cd623fa48754d179874b6a91f9f1c4b323ed91",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.WeightedCurveRigidity:1924",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.WeightedCurveRigidity:1924"
    },
    {
      sourceName := "OAI.PiExponent.WeightedFrameDegree.coefficient_supportBound",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedFrameDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "989deccc9e3344766d0e54c7245c4428c3a4a750f6bf382be5b6bbde4b04ea94",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedFrameDegree:675",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedFrameDegree:675"
    },
    {
      sourceName := "OAI.PiExponent.WeightedFrameDegree.supportBound_unit_mul",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedFrameDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8ac417ced61642c3000bb608dada09320beb8c091830354f62e5a3d379d1d84f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedFrameDegree:364",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedFrameDegree:364"
    },
    {
      sourceName := "OAI.PiExponent.WeightedGeometryScale.Scale",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale",
      graphKind := "inductive",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ac28b8c610e9e297c82048d111f79ee55b4bc9073a60fa03900de74fd2cfa963",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:3718",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:3718"
    },
    {
      sourceName := "OAI.PiExponent.WeightedGeometryScale.Scale.Index",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "de3d5eae57d04234584cee685ee8bf4a297855f38f7424a7ff9c1bec82c146fc",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:4432",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:4432"
    },
    {
      sourceName := "OAI.PiExponent.WeightedGeometryScale.Scale.budget",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "843a3e9a65691b01c213341b46769888ac0197652844ae92b313fc97955f0f4f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:5458",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:5458"
    },
    {
      sourceName := "OAI.PiExponent.WeightedGeometryScale.Scale.casesOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "37e18561add2265cfce5ff3ae0e6cd7fb4b44272406d2f9e67f12ad5d61ec192",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:3718",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:3718"
    },
    {
      sourceName := "OAI.PiExponent.WeightedGeometryScale.Scale.constantIndex",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aa128af427596cad3af768cfe3a32949c4cee2b0408d0a5ef31005d582bc1726",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:4536",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:4536"
    },
    {
      sourceName := "OAI.PiExponent.WeightedGeometryScale.Scale.coordinateIndex",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "070ded824fe0ddb81aa8f3b2042e6f627bf928fbfa255b6bb15b6d5d120a6a1e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:4672",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:4672"
    },
    {
      sourceName := "OAI.PiExponent.WeightedGeometryScale.Scale.degreePowers",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "487da41fd3db8463f25d7996925d25836dfbd95f8a2d7305011cca066adab117",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:3718",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:3718"
    },
    {
      sourceName := "OAI.PiExponent.WeightedGeometryScale.Scale.degreePowers_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c1f995e71acc63cbea97b8db2fb87ba6e92a9e1aefa453650e5d35b9dd643e84",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:3718",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:3718"
    },
    {
      sourceName := "OAI.PiExponent.WeightedGeometryScale.Scale.degreePowers_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "545d80c82ad068f827b3ff671a81447b7c96bece2cae8dc9cdd97fb4b82d615d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:3718",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:3718"
    },
    {
      sourceName := "OAI.PiExponent.WeightedGeometryScale.Scale.exponents",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cf166a6ecc5701079ec4290920f4a381c066a5745723b5d47fa9f73983441d54",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:4477",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:4477"
    },
    {
      sourceName := "OAI.PiExponent.WeightedGeometryScale.Scale.exponents_constant",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "69d0919b2942cd5a5ead07451ce41ce139460e0adb1abe051664a1ccbab936a2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:5050",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:5050"
    },
    {
      sourceName := "OAI.PiExponent.WeightedGeometryScale.Scale.exponents_coordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8dc9759065f9ee903c83a6bf36f38712233687fc712876123a6d2edbae106855",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:5161",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:5161"
    },
    {
      sourceName := "OAI.PiExponent.WeightedGeometryScale.Scale.exponents_pure",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4713fc6ac0926ceeffe5ba2b7dae8edd1f55e93e25c8a58f13a1bbb17830968d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:5307",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:5307"
    },
    {
      sourceName := "OAI.PiExponent.WeightedGeometryScale.Scale.jetPowers",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8aa20b7765bb4663d563717998e2d81bf12b26651da64b0bd835cfb37e6c0a18",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:3718",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:3718"
    },
    {
      sourceName := "OAI.PiExponent.WeightedGeometryScale.Scale.jetPowers_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2a9b16f940354073e9f53be707fd97655190c4163ec64d0c6da5ccde7f3ef885",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:3718",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:3718"
    },
    {
      sourceName := "OAI.PiExponent.WeightedGeometryScale.Scale.jetPowers_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "789fb43cae3f97839571242c40966811ba1fb1fa0f1e3e8c70e86b5db2a10262",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:3718",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:3718"
    },
    {
      sourceName := "OAI.PiExponent.WeightedGeometryScale.Scale.mk",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale",
      graphKind := "ctor",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "abbef2b95313a7acd565c610994e1d07c45226ed42fbcf304d1d34dfd33ce527",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:3718",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:3718"
    },
    {
      sourceName := "OAI.PiExponent.WeightedGeometryScale.Scale.mk.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "54ce75dd1c45eff1830f5d10c423d1d02b4355c24a17f9fb47bde2b462bcb1a9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:3718",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:3718"
    },
    {
      sourceName := "OAI.PiExponent.WeightedGeometryScale.Scale.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5a1d94d6829e68a9d69d1a66b50452f70211cc7ead823c33d540020f0c104765",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:3718",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:3718"
    },
    {
      sourceName := "OAI.PiExponent.WeightedGeometryScale.Scale.pureIndex",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2c78bdcf99dae939bd2cf809806a6bc98157aab898a03909d77679e1325b6d73",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:4868",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:4868"
    },
    {
      sourceName := "OAI.PiExponent.WeightedGeometryScale.Scale.radius",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eb43ea6d798d25bea69c7981ae3d3adce314eec520e49c9d81fc8657f42ff94e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:3718",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:3718"
    },
    {
      sourceName := "OAI.PiExponent.WeightedGeometryScale.Scale.radius_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ed5d4d27ba2cce9666498709bccfa4531e8ba7d14f6580be1a5c5ebdee8bbbe8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:3718",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:3718"
    },
    {
      sourceName := "OAI.PiExponent.WeightedGeometryScale.Scale.rec",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale",
      graphKind := "rec",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4c26c9fa006e04948150cf414fab8c6b4493b0bac3cf49d51e053b2155e2195e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:3718",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:3718"
    },
    {
      sourceName := "OAI.PiExponent.WeightedGeometryScale.Scale.recOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "532d75da9e90a6776545a5b69284c1e44ec0e8fbba9e2803db1121aea271a704",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:3718",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:3718"
    },
    {
      sourceName := "OAI.PiExponent.WeightedGeometryScale.chooseScale",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7e8fe7fd009eae02241ea463ddeb993023e4594b6e03252193773cdd2d77cad4",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:4095",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:4095"
    },
    {
      sourceName := "OAI.PiExponent.WeightedGeometryScale.coordinate_mem_monomials",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aa4ae1d9d4039671b377a5fc789ab60ccc3ef65f3db797002edb5510e55a2444",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:2911",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:2911"
    },
    {
      sourceName := "OAI.PiExponent.WeightedGeometryScale.exists_common_scale",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "63be6efb85849c495349c0eb66149f5648775d6067003a84e8a5aa70e5346535",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:957",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:957"
    },
    {
      sourceName := "OAI.PiExponent.WeightedGeometryScale.exists_log_cutoff",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "51919f06dfc527fa22af4763b6f3b619e03cd2abdeb646740769bd4fddb5e84f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:3358",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:3358"
    },
    {
      sourceName := "OAI.PiExponent.WeightedGeometryScale.exists_power_scale",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "60aaff2c06faf955e299810741447f51fc13e61cfe5764e418333d28ca0c6187",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:249",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:249"
    },
    {
      sourceName := "OAI.PiExponent.WeightedGeometryScale.mem_monomials",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "275cadb0735ffeb62f2feb5436c4d904db08dade66e66ab13ec894da21e53f3e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:1827",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:1827"
    },
    {
      sourceName := "OAI.PiExponent.WeightedGeometryScale.monomials",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "913b1f02c424fb66f4229437a5fdb7e465f460805b8ad538228f06de37b8f2a0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:1645",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:1645"
    },
    {
      sourceName := "OAI.PiExponent.WeightedGeometryScale.pure_mem_monomials",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eb8f4dca41976906540d281a97521d1b1579ffbfd6faddf4594ceb490df8c88a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:2604",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:2604"
    },
    {
      sourceName := "OAI.PiExponent.WeightedGeometryScale.zero_mem_monomials",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0f446e07004b94d542e05475ecdcbff075e15f4386cf0b1e589248f5bc6332f1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:2398",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale:2398"
    },
    {
      sourceName := "OAI.PiExponent.WeightedGlobalSectionBound.eventual_admissible_supportBound",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedGlobalSectionBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6d84c81cd7ab1f5297ccdabb870cba1b4143142e96a15d9b02e0af0de8f80269",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedGlobalSectionBound:1639",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedGlobalSectionBound:1639"
    },
    {
      sourceName := "OAI.PiExponent.WeightedGlobalSectionBound.eventual_supportBound",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedGlobalSectionBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e26493a182d948cb5889774b2dd00f16e9fdf6a061c6207589b058483e35ba69",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedGlobalSectionBound:867",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedGlobalSectionBound:867"
    },
    {
      sourceName := "OAI.PiExponent.WeightedHomogeneousSubstitution.admissible_exponent_budget",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.WeightedHomogeneousSubstitution",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c384ba68dcac9d6f8a8035ed7502e57b5f25c47bc2f20b3ce760e17398795682",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.WeightedHomogeneousSubstitution:2182",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.WeightedHomogeneousSubstitution:2182"
    },
    {
      sourceName := "OAI.PiExponent.WeightedHomogeneousSubstitution.dehomogenize_substitution",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.WeightedHomogeneousSubstitution",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "10472a1b4c5d358b28859eafe7a358aa76986d2afbae486aa768de0f653c9159",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.WeightedHomogeneousSubstitution:1325",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.WeightedHomogeneousSubstitution:1325"
    },
    {
      sourceName := "OAI.PiExponent.WeightedHomogeneousSubstitution.supportBound_substitution",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.WeightedHomogeneousSubstitution",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "112337963bc34fafaecee2e7e2563ac3ab489f935da19b4de056cfbc70e31187",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.WeightedHomogeneousSubstitution:440",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.WeightedHomogeneousSubstitution:440"
    },
    {
      sourceName := "OAI.PiExponent.WeightedLocalLattice.exists_local_element_iff_nonnegative_order",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedLocalLattice",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "790e7611e4a9b4294877be636a5f941670cadd29d8c821f002b5e4e59d9adc8a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedLocalLattice:307",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedLocalLattice:307"
    },
    {
      sourceName := "OAI.PiExponent.WeightedLocalLattice.generatedLattice",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedLocalLattice",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2a8d349c20b664652892ddecae72c33d29e2e53fe2a4167377e3283b89156bc1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedLocalLattice:2086",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedLocalLattice:2086"
    },
    {
      sourceName := "OAI.PiExponent.WeightedLocalLattice.generatedLattice_eq_span_of_minimum",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedLocalLattice",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f1221498d948bd78de4bb35229006b5becfdae5cd9591e341a6c18f18af59a00",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedLocalLattice:2281",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedLocalLattice:2281"
    },
    {
      sourceName := "OAI.PiExponent.WeightedLocalSheaf.generatedSection",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.WeightedLocalSheaf",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "81756527cbe32de3d15e3828915b1ac4f79d6d3be064d8f01fc226615c3ae675",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.WeightedLocalSheaf:4047",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.WeightedLocalSheaf:4047"
    },
    {
      sourceName := "OAI.PiExponent.WeightedLocalSheaf.generatedSectionMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.WeightedLocalSheaf",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "983f4ff9aa93bed98f665fd21d1432444136eced2bf04a473858389365237ee7",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.WeightedLocalSheaf:2898",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.WeightedLocalSheaf:2898"
    },
    {
      sourceName := "OAI.PiExponent.WeightedLocalSheaf.generatedSectionMap_bijective_of_span",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.WeightedLocalSheaf",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7ee2278747a0888374a5f4c05a5ecc77ca5a447882df1ce7e07655c5eb35a68e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.WeightedLocalSheaf:3284",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.WeightedLocalSheaf:3284"
    },
    {
      sourceName := "OAI.PiExponent.WeightedLocalSheaf.generatedSheaf",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.WeightedLocalSheaf",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5e44af04ca5fbb6508d89368889cfb39701d0e7182b63388545255c42f7abe78",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.WeightedLocalSheaf:2680",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.WeightedLocalSheaf:2680"
    },
    {
      sourceName := "OAI.PiExponent.WeightedMonomialFamilyLattice.exists_generator",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialFamilyLattice",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "69f8aff02157a6fd11553ca5dfbb9c17c609c5673c8794790b93643e56830b5f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialFamilyLattice:412",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialFamilyLattice:412"
    },
    {
      sourceName := "OAI.PiExponent.WeightedMonomialPole.coordinateOrder_le_realValuation",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e4a32f95fd64c884fa0536500e6e8a2e1764d5e75f6c0f1e32155cfe269d0a2a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialPole:305",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialPole:305"
    },
    {
      sourceName := "OAI.PiExponent.WeightedMonomialPole.coordinateOrder_pow",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "13ee56ace2bedfd5c92c8183451578436788d6640c85c70b10e762c3c4a6fec1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialPole:1821",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialPole:1821"
    },
    {
      sourceName := "OAI.PiExponent.WeightedMonomialPole.exists_attaining_monomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1836521a08f658db88df5b1c68da1d8ed4efcb8903072f850ad9933dc10570b3",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialPole:2217",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialPole:2217"
    },
    {
      sourceName := "OAI.PiExponent.WeightedMonomialPole.exists_minimizing_monomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "898cbfeb805d0c4f48e52b49e17ea848147a31c1d580d6b5dc1356ffeb0e3a89",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialPole:3936",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialPole:3936"
    },
    {
      sourceName := "OAI.PiExponent.WeightedMonomialPole.monomial_order_lower",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c15148d6e0fd54f38fa5cf2a03d62864f05e93f22c6705ef92d562e0da3e0e28",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialPole:754",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialPole:754"
    },
    {
      sourceName := "OAI.PiExponent.WeightedMonomialPole.realValuation_le_iff",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "082081830dcb42744182f5b52e73a7b7158b35f494a9d8b2715a3b8a45d3e786",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialPole:553",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialPole:553"
    },
    {
      sourceName := "OAI.PiExponent.WeightedPolynomialPole.coordinateOrder",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.WeightedPolynomialPole",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eda204afc1da69bf384a48869b4a5e3519186ac6dc5db32e2ac8689800bfd34e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.WeightedPolynomialPole:318",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.WeightedPolynomialPole:318"
    },
    {
      sourceName := "OAI.PiExponent.WeightedPolynomialPole.coordinatePole",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.WeightedPolynomialPole",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f60a590e77cda16464418c615a32eb50507ef33f8935748d72c460755847a586",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.WeightedPolynomialPole:474",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.WeightedPolynomialPole:474"
    },
    {
      sourceName := "OAI.PiExponent.WeightedPolynomialPole.coordinate_order_lower",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.WeightedPolynomialPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e487d16ee078ecff8bb326b3ac98ee980be84165d6350cc7b36759744a9baf79",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.WeightedPolynomialPole:1018",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.WeightedPolynomialPole:1018"
    },
    {
      sourceName := "OAI.PiExponent.WeightedPolynomialPole.realValuation_of_ne_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.WeightedPolynomialPole",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "96b3c158270c6d6fc68d27fb17219dfd1e95781d4a83b09ffd7a54d686b38aee",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.WeightedPolynomialPole:633",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.WeightedPolynomialPole:633"
    },
    {
      sourceName := "OAI.PiExponent.WeightedProjectiveCurveDegree.ambient_pullback_degree",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.WeightedProjectiveCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "071893a2d958b79165ea04a7cacb9db37e1fc46306217d5ac07a248928cd66c2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.WeightedProjectiveCurveDegree:871",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.WeightedProjectiveCurveDegree:871"
    },
    {
      sourceName := "OAI.PiExponent.WeightedProjectiveCurveDegree.weighted_pullback_degree",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.WeightedProjectiveCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6b24bc47af1f14748476d21c10275e4d8942fc54f5ba3043e6d07ac2cb2d5177",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.WeightedProjectiveCurveDegree:3947",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.WeightedProjectiveCurveDegree:3947"
    },
    {
      sourceName := "OAI.PiExponent.WeightedPullbackDegree.pullback_supportBound",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedPullbackDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5fdbbcdc82327ff660e8c01a5f86755739df2c47a19be15b6c670c54f0f0dc2f",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedPullbackDegree:1671",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedPullbackDegree:1671"
    },
    {
      sourceName := "OAI.PiExponent.WeightedSectionOrder.coefficient_tilde_end",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSectionOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b7aa863b7e094bb9ad7fde5f83629852bbbeaae5f93f921a113819eec2942135",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSectionOrder:546",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSectionOrder:546"
    },
    {
      sourceName := "OAI.PiExponent.WeightedSectionOrder.coordinateBasis",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSectionOrder",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0edbe75a2bdd275152f97330a95c34d300b0f2e07116b334af1441347f7e1311",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSectionOrder:1448",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSectionOrder:1448"
    },
    {
      sourceName := "OAI.PiExponent.WeightedSectionOrder.coordinateFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSectionOrder",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "529503add698108e6e926c1d9ea56ba9d3efc620822725f9cd60bca5d1f0541f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSectionOrder:1774",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSectionOrder:1774"
    },
    {
      sourceName := "OAI.PiExponent.WeightedSectionOrder.coordinate_coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSectionOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f4c3c7ff43c9eecc64512ad11b60419bea321637a2c8181ba5b4174a21eb61d9",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSectionOrder:2124",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSectionOrder:2124"
    },
    {
      sourceName := "OAI.PiExponent.WeightedSectionOrder.coordinate_coefficient_image",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSectionOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "406778f717ead40f7d67bf8928e5158ba9553db45dd39c684d59c31ce05084d5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSectionOrder:2913",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSectionOrder:2913"
    },
    {
      sourceName := "OAI.PiExponent.WeightedSectionOrder.coordinate_coefficient_ne_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSectionOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cb4a3e9bbca270c15e3694fefd8d656bb2f0a956113c4736720187116d8f4f8b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSectionOrder:3656",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSectionOrder:3656"
    },
    {
      sourceName := "OAI.PiExponent.WeightedSliceDegree.SupportBound",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6214bed6f843cacdf9117a847141081453666ff41e11a73761f369e71917cb1b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:218",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:218"
    },
    {
      sourceName := "OAI.PiExponent.WeightedSliceDegree.SupportBound.add",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "12264e03d7a97585309f8454bb60de1cb4ad76d12a210377c9990606fb7d4fd7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:1211",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:1211"
    },
    {
      sourceName := "OAI.PiExponent.WeightedSliceDegree.SupportBound.mono",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "83ad989a532e2f03f34123bee9ba926ddf25d97fd7d3d0d4f2be1c3851c341d2",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:350",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:350"
    },
    {
      sourceName := "OAI.PiExponent.WeightedSliceDegree.SupportBound.mul",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9eb83a1842149e2279d017be1fe850b96d1e554ae1e029c8ff5507429d752251",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:1522",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:1522"
    },
    {
      sourceName := "OAI.PiExponent.WeightedSliceDegree.SupportBound.pow",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fac29544e4ccdb74d1a3d9c6894026eae8f50cb74258f5ee5a735ae2e007c951",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:1882",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:1882"
    },
    {
      sourceName := "OAI.PiExponent.WeightedSliceDegree.enumeratedSliceMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3ff12dc9ca0b977a5200e3434b009b70e1710b00d2893d88c4da20528dd94220",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:7687",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:7687"
    },
    {
      sourceName := "OAI.PiExponent.WeightedSliceDegree.sliceMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f7c34deff4197e19a4dc504251cb8c7e18198281c161a8c1c2c13726e5dc91d2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:4618",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:4618"
    },
    {
      sourceName := "OAI.PiExponent.WeightedSliceDegree.sliceMap_X_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0f3a937e1cd885ffa5f4d9de806979e3dd82c04798f559b6eddf4411db45f36b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:4861",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:4861"
    },
    {
      sourceName := "OAI.PiExponent.WeightedSliceDegree.sliceMap_X_notMem",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2d8ebdf40e91daac00478f89afe5a331541dba13923ce23635c9c871b8405a95",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:5069",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:5069"
    },
    {
      sourceName := "OAI.PiExponent.WeightedSliceDegree.supportBound_C",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fa34c21af3357b4f45ec908a088d1f69bfa72532546a75ec3fbda4e4cd622bd9",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:681",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:681"
    },
    {
      sourceName := "OAI.PiExponent.WeightedSliceDegree.supportBound_X",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2699342205e057af34d3335b2de8e35a9af01d1632b928dfe0c7928f60d2445c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:904",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:904"
    },
    {
      sourceName := "OAI.PiExponent.WeightedSliceDegree.supportBound_aeval",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c69ecfcabf3011e35eec8d7aa451b14971d4f7c23938c0a689fab48ef4e3f6f6",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:4123",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:4123"
    },
    {
      sourceName := "OAI.PiExponent.WeightedSliceDegree.supportBound_aeval_monomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "116b2949783f6e85b7835c933588a5557eecfeaff570ed29ca9bb4af1653be1a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:3416",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:3416"
    },
    {
      sourceName := "OAI.PiExponent.WeightedSliceDegree.supportBound_enumeratedSliceMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c3718555c93b6b1b95dec74f8d9d4bda664fdd71d0be52737a68a957950b050d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:7909",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:7909"
    },
    {
      sourceName := "OAI.PiExponent.WeightedSliceDegree.supportBound_enumeratedSliceMap_sum",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7334528612a9ff627a994d45721dea1df129a190a337ed3885c14832f1035c0d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:8356",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:8356"
    },
    {
      sourceName := "OAI.PiExponent.WeightedSliceDegree.supportBound_prod",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a3c68dfda46fad9a86de3ae9a672a4aff8c5573ae3f72c5bc9b691b82c1b1f5f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:2289",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:2289"
    },
    {
      sourceName := "OAI.PiExponent.WeightedSliceDegree.supportBound_renameEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8c5c3df180a503045d3126b61a37a677adaea911202207753b8620b657531546",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:7205",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:7205"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_027.jsonl"
