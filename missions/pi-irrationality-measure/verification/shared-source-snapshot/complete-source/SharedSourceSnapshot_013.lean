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
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechSections.sectionValuesEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7369fd03078031e698ffe59e31f618eb785ebc42120f3d944b99637de9aaf77b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:2226",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:2226"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechSections.sectionsEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ec8bfe7b9216e27c1e916e4ff376217562156addd9e07a3ef736ca019fe1fede",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:2493",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:2493"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechSections.sectionsEquiv_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "11fc3a756f062bb1198ed26f0c689742a85307d54713f56eda9e251da874704d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:3109",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:3109"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechSections.sectionsEquiv_boundary",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a09e0fa19ba1197fb9b9cb6b63fc9a84bc92edd106dd3e14f2db435ac21c826f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:6518",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:6518"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechSections.termShortComplex",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b03450ab92cc110a4e1feb29f254b59b07f03cf86bba434204fe91826c7eea6c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:6359",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:6359"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechSections.tupleEmbedding",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "470da9405388c0990edd4ca23c52536e050ed245bd4efe613ce3856e787008b1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:2689",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:2689"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechSections.tupleEmbedding_face",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "82fc860353c53b708f9f1cb7f13afbc33b0066d547417a00e96df5770368e55b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:4180",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:4180"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechSections.tupleNatEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "270f9678135b76e28837ddfe67b06a8eed65e723d899a9153ffd9aa440598065",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:699",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:699"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.IdealPullbackMap.comap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackMap",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fa09f21114974fe39b6028c801b82b5f7292f65c982121fc3aa2a009dabfae4d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackMap:2244",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackMap:2244"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.IdealPullbackMap.comap_inclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackMap",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0de7040f3f0358a811fc8b13b81d611c00475e46442f468057d43affdc86df10",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackMap:2385",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackMap:2385"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.IdealPullbackMap.comap_inclusion_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackMap",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "43d034240852d1a65117a17ecad1685a131ffc21b06cda6fa53649de3faa390f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackMap:2385",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackMap:2385"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.IdealPullbackMap.comp_quotient_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackMap",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "36a4fc345e7a05cb3e15313cb445407145c1400c582cef7b219970cf63277bf2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackMap:513",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackMap:513"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.IdealPullbackMap.map",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackMap",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0a763170ae02973b6314102547855c2e73787f213e204fc8c2751f68d69f4115",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackMap:1109",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackMap:1109"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.IdealPullbackMap.map_inclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackMap",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f3f341e9c267ce08e840830d43ffeb3f84ecf3c030f33afa25194e396292e94a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackMap:1449",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackMap:1449"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.IdealPullbackMap.map_inclusion_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackMap",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a66ca95f2071935e0365d2df97e881c105045de24d382accec3198f247ce5f28",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackMap:1449",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackMap:1449"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.LaurentCechFinite.cochainEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b9e32f5ffc0ec3e87baef58d3faaa2be19f9d07df924514a612369b27ccc29b4",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:2142",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:2142"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.LaurentCechFinite.cochainMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "42ceb1f075b1001971f3eacfea7654cebfb94c0570640483b7f40e36ed505087",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:1301",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:1301"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.LaurentCechFinite.cochainMap_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8cdc6b20c8929c5afa38d49473929e52a9d2b12738f3609ebbd17ffb7567f72f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:1714",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:1714"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.LaurentCechFinite.cochainMap_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "62e7632ffb8ee213456c0f3ca1d6931d8badfd31b25e1c3aaaa0d4e1b846e47f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:1913",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:1913"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.LaurentCechFinite.cyclesEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3ca2bc5cfb5a31fdd49d9cedbc74aff54248ceff252e22ed3b52597235c80cc6",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:4016",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:4016"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.LaurentCechFinite.cyclesEquiv_boundary",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e2ffdb68cbe4caba7577974502316c5ea4653080e9155d70212118bb35c2b29e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:4289",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:4289"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.LaurentCechFinite.cyclesEquiv_symm_boundary",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8bf996f7804b1ec32ad2dbe81cf29846bd095eb45c7197b16106fe8cba20e1de",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:4595",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:4595"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.LaurentCechFinite.cyclesMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8ef2b52c5af8d0fe035f5e8ff76b2a8f096256addc9450ab28b20dea48a0f33b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:2429",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:2429"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.LaurentCechFinite.cyclesMap_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c415e6258cf2885cc2f52c2dd99f4dcce2ec84478039f5b789dd158282450aee",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:3188",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:3188"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.LaurentCechFinite.cyclesMap_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "516ec99c8bbaf34995561475e4f76fbbb43f777343cb0eda7a42e4b5dc0c15ef",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:3406",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:3406"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.LaurentCechFinite.degreeZero_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3ea54ab1afbebda3902787bd69720c778e9140541adb37831411baa908e3b9d7",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:5047",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:5047"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.LaurentCechFinite.finite_of_comparison",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4c24c1c05f617e088fdd7eb0bede94aff25a61c21635c61a6c08cb764fe3966e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:5430",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:5430"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.LaurentCechFinite.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomSheafOfModulesRingCatSheafFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "be76d71592ea24d5de981714951cd662ca3af3d332e2bf67406ca3c4289b216e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:951",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:951"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleCoherent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "40425e21324a77b4d31e4c33b8f538bd056bd401e3d60e2aa1619c8f777fbc2c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleCoherent:690",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleCoherent:690"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.LineBundleCoherent.modulePow_isFinitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleCoherent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6998c9e26b689e6ba3b44e4b9ddb5642084999a8fd810b151b11e97f79f8fe4c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleCoherent:1134",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleCoherent:1134"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.LineBundleCoherent.modulePow_isQuasicoherent",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleCoherent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ea2cf500f6d6c6c4c9f8bd76a31f18ab78c1d1e286052ee3127ad5b0864718b6",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleCoherent:1305",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleCoherent:1305"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.LineBundleCoherent.structureSheaf_isFinitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleCoherent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e96d8e30c80ac85a5f5eccb402626a88f51ea2b9c14e0568697729c8b879386a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleCoherent:299",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleCoherent:299"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.NoetherianAmpleSerreVanishing.ample_power_cohomology_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.NoetherianAmpleSerreVanishing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fa2f2d612dd51799b0c603ae3ed7a35f93aa395621fd449256c9451a0319962c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.NoetherianAmpleSerreVanishing:3457",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.NoetherianAmpleSerreVanishing:3457"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.NoetherianAmpleSerreVanishing.ample_serre_tensor_vanishing",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.NoetherianAmpleSerreVanishing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c8b4c1610ca67753be21464b953dac4dc011edea8c0e9f8e1944d3e0ae60f2a9",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.NoetherianAmpleSerreVanishing:2946",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.NoetherianAmpleSerreVanishing:2946"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.NoetherianAmpleSerreVanishing.ample_serre_vanishing",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.NoetherianAmpleSerreVanishing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "80af1c68d7e8e2d0f89d5516c03d9f4c65bdcfd99a7967f05f71fe7343577367",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.NoetherianAmpleSerreVanishing:661",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.NoetherianAmpleSerreVanishing:661"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.PrincipalQuotientDimension.le_quotient_succ",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrincipalQuotientDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ba2f57a180ff99d1c36110ffa8ac2980dc908d212604498680eac856a79bd78d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrincipalQuotientDimension:389",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrincipalQuotientDimension:389"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveCoordinateAcyclicity.coordinateLaurentCechPresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveCoordinateAcyclicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fe1ce3902f2452ce8a19e5c8e6d3741d1a2682f8d5a7e746801f98474687622e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveCoordinateAcyclicity:2494",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveCoordinateAcyclicity:2494"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveCoordinateAcyclicity.coordinateLineBundle",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveCoordinateAcyclicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "355bfac3f8bcb1ca654a14b5d630f58b8a1406fb4e8bac01867666cb7b8a4b84",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveCoordinateAcyclicity:3078",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveCoordinateAcyclicity:3078"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveCoordinateAcyclicity.coordinatePower_ext_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveCoordinateAcyclicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "09b3be8ab1f6dcd65633b9542e255358b67c444dc1373b51d00bdfd4c05277e0",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveCoordinateAcyclicity:4195",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveCoordinateAcyclicity:4195"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveCoordinateAcyclicity.coordinatePower_ext_succ_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveCoordinateAcyclicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a2f5afe0e1840e552f09db100dfffe875624e59a66a0ef1c44af5477cf5fce74",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveCoordinateAcyclicity:3636",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveCoordinateAcyclicity:3636"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveCoordinateAcyclicity.coordinatePower_isQuasicoherent",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveCoordinateAcyclicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "71b3ee19549dfa04aeb5ee914c828137b5e6d96b9b09ec2b56263c63d2946201",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveCoordinateAcyclicity:3420",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveCoordinateAcyclicity:3420"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveCoordinateAcyclicity.coordinateTupleCoefficient_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveCoordinateAcyclicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4455b877a983b41b69000a325c4fdae1ac6db8aa38aafa11387e5eadee3c81dc",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveCoordinateAcyclicity:1279",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveCoordinateAcyclicity:1279"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveCoordinateFinite.coordinateBundle_cohomology_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f97c7bfbfd2d1c6e7d3c73e6b37e45b6bba569d612e38abf708238a0508507b0",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFinite:1922",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFinite:1922"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveCoordinateFinite.inversePower_cohomology_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ccfc22023b6a44e8b2605d816e332a28a5bac8601bd48384f89c5f5c15fa79e9",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFinite:764",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFinite:764"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveGlobalPolynomialAlgebra.chartExponent",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomialAlgebra",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9bbfb241b121f360105e1fb2b761a7b64fcc9ed03ac76bcd7b1a80897c167d55",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomialAlgebra:538",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomialAlgebra:538"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveGlobalPolynomialAlgebra.dehomogenize_monomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomialAlgebra",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b44d0e1cf4272c88c5b1d603246e86ca16cd34e6ead622d7651d6a75bf16072f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomialAlgebra:796",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomialAlgebra:796"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveGlobalPolynomialAlgebra.encode_chartExponent",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomialAlgebra",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1f6d8565186dba1b756c0ceef2d9a2a07d22ea57287ed0681c807ec0b4f454ae",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomialAlgebra:1311",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomialAlgebra:1311"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveGlobalPolynomialAlgebra.polynomialLaurent_monomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomialAlgebra",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1837e415225442953e0f7fe01fa070e1e837d9f8ab2d4e7b1ddcb9128cf35658",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomialAlgebra:2187",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomialAlgebra:2187"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveGlobalPolynomialAlgebra.vertexLaurent_dehomogenize",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomialAlgebra",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6e9dcb7aa32d623af32e724dbbac89594b0cc7d579748d2dcbca7d01f976eaf1",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomialAlgebra:3447",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomialAlgebra:3447"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.FullGroupAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f1d91f4f2595179b199cd2f366a1b1fb32a6e5e623aab36e1224c852e1c71bab",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:3012",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:3012"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.chartToFull",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4f398cd506560cb902447561a2cfce755c0269ab914706cad63bdc6f4531c600",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:3074",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:3074"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.fullEncode_eq_standard_add",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2e02aa05c6c350216b61bb6cbeadf9cc87a7b54d3be1ac049197c95810740d42",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:1888",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:1888"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.fullMonomialUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "21024acf2ec217274041f8519c79ad8f66da8c822c680ce99cd765d0270b677c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:9187",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:9187"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.laurentToFull",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9aa1fb0a46099b04b089cfee2495ed21b4c1b4dcbcf1562887677032006863cd",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:3405",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:3405"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.laurentToFull_groupAlgebraToLaurent",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0ff5955431ea7df766eebf69971281c1c888dbd892f0f74c86c492656468b7fc",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:4032",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:4032"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.laurentToFull_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c7e94c998d60e27fc68f19c68225d5e65b9330fa2eed213d85eb6e34667f15f5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:3628",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:3628"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.laurentToFull_overlapLaurent",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "64514ca26aa920f9a47b2d7ac5df149f1a8df088cb1afc962005eca7debc0057",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:5179",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:5179"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.laurentToFull_single",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ac48f2637d3f2fe3e58a3dc1a9143b9b0c70b9416a38772852c1bea2b3dd2f4b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:3846",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:3846"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.overlapLaurent_change_pivot",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9836b8121962e9e57f6be9b8c99cc0c432ce0f4ac64cd57ada1ace2ed4032afa",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:7346",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:7346"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.overlapLaurent_change_pivot_pow",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8a8a7e8ba7487bf52e6065f5375178cb1ff3533ab023c588e1e6e9b8579661c5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:8372",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:8372"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.overlapToFull",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8919f5244a792cab54752550bcaeb132c98310a7ca2aeeb6f007ddbf7b3cd2b0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:4758",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:4758"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.overlapToFull_C",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3d4adf0b6ac9b2c24adc0a198cb2349101acaca057c3f63d44205217ffb1ca13",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:5858",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:5858"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.overlapToFull_X",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "81d4e50a038c8911c3ae890c6270eb051aaa9017abea2b5106c9161cde5692bf",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:5512",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:5512"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.overlapToFull_natural_of_generators",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3045327c1e5a658cf46d19702245b593b51f2475f2f13b042b2191d218574fca",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:6409",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:6409"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.overlapToFull_ratio",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f64dd36f4d7c49cac552211656a001c93ad5e92df489272bd8ece73820ca5bba",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:12099",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:12099"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.standardExponent",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e69d7fc37a3d62d75fa7efc9bee7234c2a22a754fc911b258ff32ae8dba68ba9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:408",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:408"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.standardExponent_other",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cae8225a80f682d07fb9983d7d8dbc3fef613b1bb604858ce8e5d44aa9f3ac12",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:643",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:643"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.standardExponent_self",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "66cbb466df718972add4675e9ead761b7be723e397dc39df3df8ee0bb0bcc390",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:499",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:499"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.zeroDegreeExponent",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4d2aa955ffcf54593632e28df40bbc8e630b0c4c1c7098f6d9f50058d2313ac7",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:811",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:811"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.zeroDegreeExponent_coordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "38871c95a512780cc9cf92dcb0fe26356532c84743fae37edf2c4840a20de12e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:2334",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:2334"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.ChartExponent",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4332e5ef21de03b52b26cfa1f0f80dd7afcca70e1160bdb90f881ec3483314cb",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:398",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:398"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.VertexMonomialSet",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ee2b0ad8f87f775c338a2d5ed9b3ce310b39177b3ff06b1eff5721290c5b46db",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:465",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:465"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.chartGroupAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "072bed5274ce90e6c2f95497b11524b24f935f195dc8f269ecf920817be1a8df",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:7271",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:7271"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.chartProduct",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "edb87342158aa775f8cdc7a08134d05e484767d89455939426bd63c1a9b84404",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:8172",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:8172"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.decode",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e922a6b27603f6951ee31a1c51ca71d6d56959dbfdad0111a481528031b082b6",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:1668",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:1668"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.decode_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "39f7de9e08432568d8a39811cc955fd1f1d238520ebfcaba7ffbbefbdd5c45bb",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:1814",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:1814"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.decode_encode",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cf8a6a2951a5b96fa73fa28c4267b82a8dda24a17dbdcb9f3479e7c6b86ec41a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:1970",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:1970"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.encode",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7645f375b2ff30f33681c595f222371ee0fb06e5fba46a8d534e18d70232ef46",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:576",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:576"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.encode_decode",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3fcc37fe4e9022d027e7207869e177a29323eb9117fd55eab9d32a2bb381206f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:2130",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:2130"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.encode_other",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "597c8f3706fee758fe6aec8fd5df686d282a97793b11456160711fce987a45a1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:1258",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:1258"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.encode_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6f6fbfff09ee41d47b84fee96e1db5df0fad50b182e499751d0d1540c7741c71",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:1447",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:1447"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.encode_self",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8817d2cfd97300ba7490909b5d8216847570232a188c8eafce29f0d2dad8ee75",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:1075",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:1075"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.exists_cleared_exponent",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a866ea011a0a27e977d0df7ff477d1b35d05331fb11d3cce6698a26c5b47256a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:16879",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:16879"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.exponentEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "50afe35acf502cc5a0b819c192a4d396e0fe6e74782a2e58ab95d03be4a9edd3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:2876",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:2876"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.fullEncode",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b3a811c0141a40b590f1e57b25cb8815be0d0b731d5a0207d3c62c2de81aa4f2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:5858",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:5858"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.fullEncode_other",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1350488f0dea1bd2b15f6471144247bd71066db013f44302d227019ffc4eb5b4",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:6540",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:6540"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.fullEncode_self",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a4758f4b2f55676ea08275050a0a46b89f15a960ca796d4b459bc241ea5432f0",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:6341",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:6341"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.fullExponentEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2625bc6a222d27a0840e9edc14bbd48b1770090125d3395f9e718ab1c89627da",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:6745",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:6745"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.groupAlgebraToLaurent",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f57e5dabcd73cb4d505db8770052445c4cfb1629f617f27f6dd19487d384d18b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:7985",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:7985"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.groupAlgebraToLaurent_coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "44092829a94f9de895d8eeb726cd45d20e63b01a738aef063c6b27f59b342ffe",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:13493",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:13493"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.groupAlgebraToLaurent_polynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "76ead19efaaa2eace574c05aa4a74957ae421e46f6fa1be3e0e3e54f03a8f13b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:14601",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:14601"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.groupAlgebraToLaurent_smul",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0cc4687fd5b7b6ae0c14bbdce4d2fcfde470058e64e78c0c40471bd599683699",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars:1573",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars:1573"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.groupAlgebra_product_isUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ea1dbb1ffcaabddab9cac7762ed2e1f2a746f45f91bafad1ba38792dacead653",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:9034",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:9034"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.groupAlgebra_single_in_overlap_range",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1bd8c49e5396d83b12124ce702e6516e511a61fe2eb4db3a92b2f0c3f8f74316",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:17978",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:17978"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.groupAlgebra_single_isUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "78dfb9a334121a06a4bca4495ac5136c44bac7eb6f2237568d1f8c30fff7799f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:8307",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:8307"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.laurent_single_in_overlap_range",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0e9d449b8f65e18b18416980250770a717f7b013e41424ae56e4c387cbd1bb07",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:19230",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:19230"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.natExponentHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1a93b983a378c191dbeefafb057367817638ca67e93a4927eb1eca00708110aa",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:7360",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:7360"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.overlapLaurent",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "51ccf4d9373e30e31484dbebd30ba43dd5530649936034a91db870cc1734ea54",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:10494",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:10494"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.overlapLaurent_base",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4fa0120ea019fae462dae64f5dd493eb9c17c83760d138a5ea8b9fe7fa6efb9c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:15181",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:15181"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.overlapLaurent_constant_mul",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cdfc8face43a6e691743f7395a67a4aabce16981972ef6dd7f70e15cd487e1cf",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars:1777",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars:1777"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.overlapLaurent_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "38e86d3db1d3dd9776100189b486ed7956b67d5b80c5e0d53caa3acf8996be0c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:10738",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:10738"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.overlapLaurent_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c131ce91a0fabe2156606941a3a35b892a9893143f8749a53f13cfc920bd6f95",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:13755",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:13755"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.overlapLaurent_surjective_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "07ecb1c45a94dd4a7d78fc666006fbb59940dd6ee70fc8143659102d5a8db240",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:19859",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:19859"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.overlapToGroupAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7c2c70e803a521f9dc8fea810eccaa7693a9d20b37c72730e33616ca48736857",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:9367",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:9367"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.overlapToGroupAlgebra_base",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e6a65e31e95e13f9f7bdc25cf6f5ec44169a75bd6d9ec4c31f3f27ecab47199c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:9641",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:9641"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.overlapToGroupAlgebra_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "96eeeaeef27b38b951e3062d0bc2e8351e59af79ce7535d8b080813b60b3fb94",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:9978",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:9978"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.overlapToGroupAlgebra_nonnegative",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1c2c75eaead812adf7a8001e107f7529c8f7dd463fe2c2896f9b56266b8f9106",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:12496",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:12496"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.polynomialToGroupAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f9d398b77fb734d06e02627f491fae5c65a62405ab4d232ec5c96cfd9e02bcc0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:7542",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:7542"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.polynomialToGroupAlgebra_X",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "89f462db35077fa482c773ec90a08429a17c5c365bb8982e553021aa0459b774",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:8672",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:8672"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.polynomialToGroupAlgebra_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dba14e6d0ba57d4614644eb11ef73a173cca245185b2897c4b7236e40f64db99",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:7721",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:7721"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.polynomialToGroupAlgebra_nonnegative",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cc67d5fd51b08faae6373f1738840e55ec185f65ea22b441dbed84820f16234a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:12133",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:12133"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.polynomialToGroupAlgebra_product",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8c21e50d6f8c99ece4ecbc71614e0d410953c5f8ace2bac15ffd8f83da5b488c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:11123",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:11123"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.productExponent",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6b68ddcb3fd5b369ef57f4a80acacfa9eda6c90ed4c0e0c749f0772bbd6beae2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:10971",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:10971"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.productExponent_inside",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8a0d6ceeec89a0b5012710906242609b7c972ae661d54d0258384022589e8bef",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:16594",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:16594"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.productExponent_outside",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fdb21118b2fa07e4a0f20839fe70d77d59808718165a3e7aa43cec843656bf8f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:11756",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:11756"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.vertexLaurent",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8cc6e24f426b8968070226436ba53ffd6954a1d06bf98bcd9d0eeae3e98f4f08",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:3492",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:3492"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.vertexLaurent_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1da88c3157f959d5e9af037a67a417c85a26e94c63cc15412726c8efd923c41a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:5006",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:5006"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.vertexLaurent_monomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "40c30aeb83de67d7b0926868d03b6e0c65f5bb7ed2f6aeccc4bcb413ba86cb95",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:3711",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:3711"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.vertexPolynomialEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5f265d6dec152fb13d80edddd0f04f5da9a972fc12125961d9a4c4778662d821",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:3167",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:3167"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveTupleCharts.coordinateFiniteOpen_tuple",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "59547eade5b7057764b36fb94b90d90bd3babe1dcfa076b7758ce86253913ed6",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts:2516",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts:2516"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveTupleCharts.coordinateOpen_isAffine",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e50b3e22d30b2f1ed556ec9dc9fcabec25ea6745e64e19a6bf8033168f801cbb",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts:4743",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts:4743"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveTupleCharts.coordinateTupleCoefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8c05fe9c91829aa98bd814b290cf1d5dfb04d15c420eff0e9275708741ea3db5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts:5082",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts:5082"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveTupleCharts.coordinateTupleCoefficient_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a5aa4af8591b6cca152d6cf539b4f8114e3b1edd41409433f173d5c6564e60a8",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts:5493",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts:5493"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveTupleCharts.coordinateTupleCoefficient_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "652ecf046a5b20359f4c8a5d6bf1009f3ee4f5651cf0cfdd6c7d385c883f6025",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts:5831",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts:5831"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveTupleCharts.coordinateTupleCoefficient_surjective_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6d8654828f8aa778b0e2c9fe3d4f5767da5ffcb4b9354cf1d871c326b494f987",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts:6590",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts:6590"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveTupleCharts.freeOpenHomCongr",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8885d99908ace79502f31501e1efaf170870c86807067e7c24839c3d7e96db35",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts:3354",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts:3354"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveTupleCharts.freeOpenHomCongr_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7f809207df440639b9c8dd8b1a1fd852597e3fca13159e60c8acf7c27cc4e0be",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts:3907",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts:3907"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveTupleCharts.mem_tupleVariables",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0d1b776871cda3c33805842e316288eaa53b0732602184befa912ce8bdf6484d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts:608",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts:608"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_013.jsonl"
