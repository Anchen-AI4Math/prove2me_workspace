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
      sourceName := "OAI.PiExponent.GradedSerre.shiftedFreeGradedSMul",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedSerre",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fe44600a7bb7aac81f7e5cbcac65faf4aced75d6d013c37a8895f7139ba8fefa",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedSerre",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedSerre:6770"
    },
    {
      sourceName := "OAI.PiExponent.GradedSerreStep.HasPrimitive",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedSerreStep",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "465c502d34bb40b95f27a44eac9bcc2b4b6959d642214aa56fbb0aa3b5e435d9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedSerreStep",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedSerreStep:672"
    },
    {
      sourceName := "OAI.PiExponent.GradedSerreStep.HasRecovery",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedSerreStep",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7bf44969d7aeb8fefce34e71ad8919ca6bab9f28f5dd8c1b40b2aadb4c6d3993",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedSerreStep",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedSerreStep:1080"
    },
    {
      sourceName := "OAI.PiExponent.GradedSerreStep.exists_syzygy_eventual_step",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedSerreStep",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e1a75fede60ff5a419c2261c27177b2865cdb8351bfdaad2e5948063608067e6",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedSerreStep:1398",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedSerreStep:1398"
    },
    {
      sourceName := "OAI.PiExponent.GradedSerreVanishing.eventually_all_positive",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedSerreVanishing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cb21d18354f8bc219aa67829d187ace1ab9542f6e8f4d360aaea9d2b48f35916",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedSerreVanishing:2264",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedSerreVanishing:2264"
    },
    {
      sourceName := "OAI.PiExponent.GradedSerreVanishing.eventually_hasPrimitive_aux",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedSerreVanishing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b966542529838417cd7c745dad911f7e35492b81e24d9cfaaf71b8ec8fa2f6cd",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedSerreVanishing:466",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedSerreVanishing:466"
    },
    {
      sourceName := "OAI.PiExponent.HomogeneousSubmoduleGrading.component",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "33b026b44a462047a93fdf93e1f6cb2e9520f18895359c29a85b9c3941949be7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading:596"
    },
    {
      sourceName := "OAI.PiExponent.HomogeneousSubmoduleGrading.decomposition",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c9abebd066efbfe175ab2b59d91f24ce6d60bc465971b6d9e10eedd43d9ece07",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading:2526"
    },
    {
      sourceName := "OAI.PiExponent.HomogeneousSubmoduleGrading.decompositionMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "788e11dd8d9cfa5ba9025b15438814588595a6b92beba68c18d7e2b3848823cd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading:773"
    },
    {
      sourceName := "OAI.PiExponent.HomogeneousSubmoduleGrading.decompositionMap_homogeneous",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "160d9a683efa86a287e7fd3e9393ddcf646ca95d1e2c908423c26bca8a22c3a7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading:2097"
    },
    {
      sourceName := "OAI.PiExponent.HomogeneousSubmoduleGrading.decompositionMap_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "83d2f61ff0198c67ef8608adbc4f90e6b94667557a5dcec3eda76ac9bc2c6c5a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading:1838"
    },
    {
      sourceName := "OAI.PiExponent.HomogeneousSubmoduleGrading.gradedSMul",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7bb97b5e9893936adda45e7e9a21ab1170fdc07eb46219d9337bfbbeab8bb637",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading:3464"
    },
    {
      sourceName := "OAI.PiExponent.HomogeneousSubmoduleGrading.piece",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9f4878c8940780f9297525e1cdd87373ac4a80adf99fa8f86ee865c4fba038f5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading:378"
    },
    {
      sourceName := "OAI.PiExponent.IdealSectionRestriction.idealCongr",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealSectionRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7db170a18a9161311e0e1127da7c1e183d8502e499879c5a6c84f7fe276a4a6f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealSectionRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealSectionRestriction:3059"
    },
    {
      sourceName := "OAI.PiExponent.IdealSectionRestriction.pullback",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealSectionRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8ba9283a8763929699e376a355d1ebc1f379c6c598c27e6f8bde03515ea6e7af",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealSectionRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealSectionRestriction:1405"
    },
    {
      sourceName := "OAI.PiExponent.IdealSectionRestriction.sectionsEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealSectionRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7029cfde6764041761c48660e6097d4846f88b8f70128b3549ed5f93545774e0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealSectionRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealSectionRestriction:359"
    },
    {
      sourceName := "OAI.PiExponent.IntegralAffineOpenDimension.affine_open_dimension_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IntegralAffineOpenDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5501c2bc76d5bb92da978262a7639c111319768bc07d80409e0f78dd7f045451",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IntegralAffineOpenDimension:3620",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IntegralAffineOpenDimension:3620"
    },
    {
      sourceName := "OAI.PiExponent.IntegralAffineOpenDimension.chartAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IntegralAffineOpenDimension",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8183c0ebc497413a66087be6813d9a9eb83f57372d7730cb393c6a9087ba7692",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IntegralAffineOpenDimension",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IntegralAffineOpenDimension:662"
    },
    {
      sourceName := "OAI.PiExponent.IntegralAffineOpenDimension.chartConstants",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IntegralAffineOpenDimension",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bd1603c2214fe74048b04b43518c61b89ab695728c154647d222fb28defa0b1e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IntegralAffineOpenDimension",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IntegralAffineOpenDimension:552"
    },
    {
      sourceName := "OAI.PiExponent.IntegralAffineOpenDimension.functionFieldAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IntegralAffineOpenDimension",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "08de8e6df002b3fdd5ef5251e00b02e3f872b7758bd87b9ca43a3432e497932d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IntegralAffineOpenDimension",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IntegralAffineOpenDimension:784"
    },
    {
      sourceName := "OAI.PiExponent.InterpolationMatrix.Column",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "99b51bbf41b6927c6d942783d855f6e3bbf8b609c48e178bcd56401871815ded",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:2516"
    },
    {
      sourceName := "OAI.PiExponent.InterpolationMatrix.Row",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "44b01340fc31199b300735d46af8dadce845823150f853e579c7bf52583089b0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:2649"
    },
    {
      sourceName := "OAI.PiExponent.InterpolationMatrix.columnWeights",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b4649aa17c94b147a971a0103ddfb8b742cc7bc83d77a08bcd002eec5559b7ce",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:2274"
    },
    {
      sourceName := "OAI.PiExponent.InterpolationMatrix.entry",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "adea7557d1f4e6389410cf84be65cbae9c83b0114511afbd483e6286cfd1bd12",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:1150"
    },
    {
      sourceName := "OAI.PiExponent.InterpolationMatrix.entry_truncatedLog_cleared_gaussian",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bf0aedc8e698fd428f72fc79b5bb873c7ca1541ba1b647bbe7139a8b044d1c98",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:3245",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:3245"
    },
    {
      sourceName := "OAI.PiExponent.InterpolationMatrix.exists_full_row_minor_of_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "57394b8555e6b7d2f8d88ecd4ca0895d0fe0e1bb64b5655c4be15433a6698c84",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:6080",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:6080"
    },
    {
      sourceName := "OAI.PiExponent.InterpolationMatrix.exponentVector",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cf73aa2a3c3ad37e62dc10f6092e4eecdc28de76cce9db43600d1f7fb67b807e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:198"
    },
    {
      sourceName := "OAI.PiExponent.InterpolationMatrix.exponentVector_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "85555e75c5c508b567c70404e7b24342b90556571f99ca292d367110857c89db",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:321"
    },
    {
      sourceName := "OAI.PiExponent.InterpolationMatrix.linearEvaluation",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eba74696307a5b9b0330df20dbca4b2ace0dfb5f82293a76f2670c919be3714d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:4674"
    },
    {
      sourceName := "OAI.PiExponent.InterpolationMatrix.matrix",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b50e45de51ce7fc5e347128e0cba975d3b0165b6d5a6b77008223dcf68e21dec",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:4363"
    },
    {
      sourceName := "OAI.PiExponent.InterpolationMatrix.monomialImage",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7974bc06efb855731b00686cac46d3db49616b6cfb9aaab5612ed3e30ba687b0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:824"
    },
    {
      sourceName := "OAI.PiExponent.InterpolationMatrix.rowWeights",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3086f7e37df893e7b9548134e9ac8bf191310cf5f25cd4e96f932d98b32bbcb8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:2379"
    },
    {
      sourceName := "OAI.PiExponent.InterpolationMatrix.sectionImage",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ef80ea28a0ade0b92b7aa795990c084764ce0e8e6b3e6f245544b0a764f48951",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:1383"
    },
    {
      sourceName := "OAI.PiExponent.InterpolationMatrix.truncatedLog",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7ef7357df66b51deafd170fc419e02859efa431bf58989c475c879d6f8d96f33",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:466"
    },
    {
      sourceName := "OAI.PiExponent.InterpolationMatrix.truncatedLogMatrix",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "546fb3e82c50f72d1d42a0345147cb72db3d31fbbd42f000b5ae5e6ee1ae5eb5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:8124"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.dualMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b04701d0f9549dac25d67dab4cb0c5989b7804b46922ca50c6c1b06ce27d74aa",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:6304"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.dualMap_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "431d259ef9bd8e35aadf99f3e1b25d0d7c05170a3e20a6b6645955ef1acc6a72",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:6452"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.dualMap_coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "63ae0960a2ed7f548f957a55e49015d139222da85dc919bfeb27ffe5ab0728e3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:6927"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.dualMap_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseDualRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c73ea1221ee9eec527c215999cc0398d153c07108592d19a6e641db4e605cdcc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseDualRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseDualRestriction:407"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.dualMap_restrict_coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseDualRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "43abff16da5d7f04f3ba928550ff6c6bc8d280ed0e64245136ff6e0e72ee68da",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseDualRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseDualRestriction:2012"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.dualSection_restrict_coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseDualRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ed308cc28b70ebd144f32f5b57c62b58c4a82024348b06915d94960d97254573",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseDualRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseDualRestriction:2480"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.frame_generator_change",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c8f7e794411a0349c8d597dd609298e5ffd887abc749f227121bae8e6f1bc496",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:2125"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.inverseOpenFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8d5bf7f27dea86c5068fd49466af31f26ccc460ad9ca9d0c7fd2d6deb67c2434",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:7685"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.inverseOpenFrame_frameChange",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8dc5765cd94e840f34c5d633fd04b2f3cfa8603b834a3c5bfaa0c7cbac0db729",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:7878"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.inverseOpenFrame_pairing",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrameRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ed6900afb827075c0945846332ae7fd8d9288033bf16de6442ad2e71cb41a4a1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrameRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrameRestriction:1407"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.inverseOpenFrame_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrameRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "69edaf764105f0d8b6470f8e28544615dbe62c194e2bea151dbe46ed30184008",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrameRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrameRestriction:4627"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.inverseOpenFrame_restrict_pairing",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrameRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e9f9d7499d42412467e325dff04fe8522eeca529171aacea01a4c920f67b42a0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrameRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrameRestriction:3069"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.pairingFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5f042187732cadb03bb4f1ceb0c3a467eb2ddc6581d44eff79978a3f53637dd7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:522"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.pairingFrame_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e4f81e5ac35e0b13603d0e806c3a71d3f7ddf2281d5b416d67f8408ee693c279",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:1617"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.pairingFrame_change_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "84b06c779078e44b8ed3fc17256d959cf4262a901bc9b1f634f6d613c9bfd01a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:2702"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.pairingFrame_frameChange",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8ae798caa17ccbfe2dda7ab33d5c95456f8f261004773effd1e54e6777de9b37",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:3645"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.pairing_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "acd5238ee238b3b2eda7bc17781d6802fbbcd4b6a20c63c65e7c17d5125111ab",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:4407"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.pairing_inverse_generator",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4deea2dc47541f8b0cacbe8bad8a3b71d68ab3dd0be3922707bed2530ae2eda7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:5644"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.pairing_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrameRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "07818bae385c922e4edca419521396aef13854c1513dc254f15c0f73358baa23",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrameRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrameRestriction:1880"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.regularValue",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "29b5bdccc72df8574c18d1ec69cce65e8b4d20ea59a55cbdcad52ed70d08f3dd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:405"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.restrictPairing",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6cc54c8a9440a209d6ab772d7fd749782f6272a55bdfa2ea6b5f94981b404690",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:7389"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.restrictPairing_pure",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrameRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "50738baa7a9b5ed4edacd5fdae63072f8289fee83f60acfec06c89d56f964449",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrameRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrameRestriction:417"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.unit_inv_pure",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4da4316bd6869d4585450ee4dbd132d9293ca359337c704819dceedde53174dd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:687"
    },
    {
      sourceName := "OAI.PiExponent.InvertibleIdealAway.inclusion_isIso_of_comap_top",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealAway",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9be3628bbbd4651e0d5993b3470ecb3dece3f84b2c6f3ca55cc44fa1714a2752",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealAway",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealAway:1845"
    },
    {
      sourceName := "OAI.PiExponent.InvertibleIdealAway.pullbackIsoOfAvoids",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealAway",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c1cfb251145cd26d78c7c74dbcf7a53e454b7d0d44aed9fc9e5395f76a30a677",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealAway",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealAway:4938"
    },
    {
      sourceName := "OAI.PiExponent.InvertibleIdealAway.pullback_inclusion_isIso_of_avoids",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealAway",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "92375909eb874bc4faa3ee6c4acc6f355526d03385d919618e63f2c20198784b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealAway",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealAway:3455"
    },
    {
      sourceName := "OAI.PiExponent.InvertibleIdealAway.pullback_map_isIso_of_factors",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealAway",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "92541da5488be0906251d82e59e290bd5187751909583b66c9154dcbda5790df",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealAway",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealAway:2623"
    },
    {
      sourceName := "OAI.PiExponent.InvertibleIdealAway.restrictedInclusion_isIso_of_unit",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealAway",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "34dfe23fe3581bcaefed66e5f3e898602ea226358a69a865df0ebad19934ff63",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealAway",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealAway:699"
    },
    {
      sourceName := "OAI.PiExponent.JetCenterIdentification.centered_of_closedPoint_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetCenterIdentification",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fd1fb589862cec4507c33f02bf2340e34cdc2d90d17944e441ccdbb0603561a3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.JetCenterIdentification",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetCenterIdentification:389"
    },
    {
      sourceName := "OAI.PiExponent.JetGeometry.RationalCoefficientPacket",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetGeometry",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f2f3b033afc8e54fd7366ac8149e75168d90ecc52f2f99aeadf8bba381de2d7a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.JetGeometry",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:8569"
    },
    {
      sourceName := "OAI.PiExponent.JetGeometry.coordinatePowerIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetGeometry",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a575c534cf80c72e21edf89cc1a60779c22fbe299dc74757e16986cb381a2837",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.JetGeometry",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:2101"
    },
    {
      sourceName := "OAI.PiExponent.JetGeometry.ideal_pow_le_rationalWeightedIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetGeometry",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c640e38a19b84b7b3073d3f47da7aa8542cba885f95fceac250dc1233cb68f87",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:7291",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:7291"
    },
    {
      sourceName := "OAI.PiExponent.JetGeometry.rationalCoefficientPacket",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetGeometry",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6b635bdb7ffbabfba37e1000b5b0da03e349af14fddea2ed72f868e90c7ed5f9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.JetGeometry",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:8687"
    },
    {
      sourceName := "OAI.PiExponent.JetGeometry.rationalWeightedIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetGeometry",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "32e325a1c11e414b39019959f83051c27016287422cee716bcace50a5a3535ab",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.JetGeometry",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:5541"
    },
    {
      sourceName := "OAI.PiExponent.JetGeometry.rationalWeightedIdeal_mul_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetGeometry",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c7a70188525fc890c67a077bfec446ceb268773749dff6cd2e91ee7fb209a3cf",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:6508",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:6508"
    },
    {
      sourceName := "OAI.PiExponent.JetGeometry.rational_weight_nonneg",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetGeometry",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "145957c9d66989b99ab728b31a34ee27799f9bb04055753d99285b284d44e7a5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.JetGeometry",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:5300"
    },
    {
      sourceName := "OAI.PiExponent.JetGeometry.weightedIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetGeometry",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8cb1a802cafb0361ff351c30d8a45bdc4f5754650412adba9ab385e0e0c77dfe",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.JetGeometry",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:242"
    },
    {
      sourceName := "OAI.PiExponent.JetProductLocalization.logarithmicIdeal_eq_top_of_residue_ne",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "466b3eab631e9baab5f966ecd24ad7ebff248fad3469a436445cbe5f625db1d9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization:1967"
    },
    {
      sourceName := "OAI.PiExponent.JetProductLocalization.map_polynomialIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0187ec53e7ddcfa3cfe29896cd4cb6f6d65530159d9989f2fe6d2d771d4184c2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization:3866"
    },
    {
      sourceName := "OAI.PiExponent.JetProductLocalization.map_polynomialIdeal_eq_selected",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "913428d6b7d749767a575221e18031bd7970722b0acb61b22ccf67bf8ad68746",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization:4505"
    },
    {
      sourceName := "OAI.PiExponent.JetProductLocalization.map_powerIdeal_eq_top_of_ne",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a7029627236b713cb1a67422066c48a9dad19fea09b99bebbe8cc5958d69e10f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization:3208"
    },
    {
      sourceName := "OAI.PiExponent.JetProductLocalization.residueAlgHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9126324de820e827909e6282113117308de76e01b5adf6817eeabe0209336c12",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization:354"
    },
    {
      sourceName := "OAI.PiExponent.JetProductLocalization.residue_ne_zero_iff_isUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "79c70def9bcf6fd6cb3a0f681de24e8a0502e75303acc81f5d5dccd7e5b3afce",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization:521"
    },
    {
      sourceName := "OAI.PiExponent.JetProductLocalization.residue_polynomial_aeval",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "579c8b336f4ebf87861f70def2ec10b192f88db0771a4fd8fdfcf62382e50089",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization:892"
    },
    {
      sourceName := "OAI.PiExponent.JetProductLocalization.residue_truncatedCoordinates_succ",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f5177cb2021bf97db8382c9edc9121fe565cac2cce8e435fa096bd20d6738445",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization:1229"
    },
    {
      sourceName := "OAI.PiExponent.LiteralAnalytic.ChoiceFamily",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b7b1350437fa43d4ab26e3ed927378f14bc9c91d45704e1b313e594ad3de8b84",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:958"
    },
    {
      sourceName := "OAI.PiExponent.LiteralAnalytic.RowChoice",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f6a1aac4ada433b06f78455a6aac6bade0262fc0e5fa7e7d49b5f923523dd191",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:769"
    },
    {
      sourceName := "OAI.PiExponent.LiteralAnalytic.Transverse",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7aea9a44c618ec4631fe725aef3c4f83d6426ac872d6611cbcb590c9c8d2ee52",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:476"
    },
    {
      sourceName := "OAI.PiExponent.LiteralAnalytic.analyticRemainder",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.AnalyticAggregate",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7963b2560a3c2cc7a10574cc7284e20151bde7c829ea66eac0759ec1a0796f9a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.AnalyticAggregate",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.AnalyticAggregate:2283"
    },
    {
      sourceName := "OAI.PiExponent.LiteralAnalytic.beta",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "608a25b1ec2f80f2ed343b0eb1db098bef35ff22803ddac1f2e05e9d7b294e0c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:603"
    },
    {
      sourceName := "OAI.PiExponent.LiteralAnalytic.choiceMatrix",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c4a7b640b29655532e726da4123b2de64473dc4b6632e1f9ce521b88b818f7f9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:1862"
    },
    {
      sourceName := "OAI.PiExponent.LiteralAnalytic.choiceScalar",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "507a33206cb63d56844c4a38759a210534ae125391cc9bbf7c419fdac9d9316f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:1398"
    },
    {
      sourceName := "OAI.PiExponent.LiteralAnalytic.fixedWeights",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4b29a7f620bcd45892c06cb30f7df96611add4d42f724b410a65cb7b0848218d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:337"
    },
    {
      sourceName := "OAI.PiExponent.LiteralAnalytic.indexWeight",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bb47aeb8669913e86bc7c043796eda1d557392970f58669d029e4ddae37f2a8e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:1060"
    },
    {
      sourceName := "OAI.PiExponent.LiteralAnalytic.norm_actual_summand_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4fd4d50595e18231095b899f4c47d5f8a5699f90654ab2b60ea56faeef4c11d4",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:10546",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:10546"
    },
    {
      sourceName := "OAI.PiExponent.LiteralAnalytic.rowWeight",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0f58ced87748ddf24c170db5e3c3720941ffe7a3c96ad374d10f677490aeae56",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:1231"
    },
    {
      sourceName := "OAI.PiExponent.LocalLengthTransport.localLength",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalLengthTransport",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "673119144f873a983d0b782ee80fe57b3606ab8361a4df2d4e2a39fba2945979",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalLengthTransport",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalLengthTransport:216"
    },
    {
      sourceName := "OAI.PiExponent.LocalPullbackSectionOrder.exists_frame_coefficient_germ",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPullbackSectionOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3a51b89c95710a974e87f6add0c7efee00a59df4d5efe494c60edddca40882f1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPullbackSectionOrder",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPullbackSectionOrder:2320"
    },
    {
      sourceName := "OAI.PiExponent.LocalPullbackSectionOrder.factor_coefficient_image",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPullbackSectionOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eb182b978d4d72fae21c1a016ee02634396ee3bfe70cf9c0ce7a797e7655644b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPullbackSectionOrder",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPullbackSectionOrder:1380"
    },
    {
      sourceName := "OAI.PiExponent.LocalPullbackSectionOrder.sectionOrder_eq_germ_order",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPullbackSectionOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "598fae0b766fee87815451e81b76f7401c951cd2022459c5b360236a0e12e9eb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPullbackSectionOrder",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPullbackSectionOrder:4086"
    },
    {
      sourceName := "OAI.PiExponent.LocalPullbackSectionOrder.topIso_germ_stalkMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPullbackSectionOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4da5c63b320d6449e7b463577ed08d3646c94624c3ad8a876993d5cd9eb1b00e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPullbackSectionOrder",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPullbackSectionOrder:547"
    },
    {
      sourceName := "OAI.PiExponent.LocalSectionOrder.localCoefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalSectionOrder",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d61028d1d55c9a8f29751e842d2243b1bbd88d0395faf12efecd1110d183d4f0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalSectionOrder",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalSectionOrder:398"
    },
    {
      sourceName := "OAI.PiExponent.LocalSectionOrder.localCoefficient_change",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalSectionOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e87851470d5cbcb06a5ee7a721bd5c496cc65add7afe2dd278198c03e4625678",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalSectionOrder",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalSectionOrder:881"
    },
    {
      sourceName := "OAI.PiExponent.LocalSectionOrder.localCoefficient_eq_zero_iff",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalSectionOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d291d0ee255248ab315536113821e909be939647486f1c417657dba9c06b80f0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalSectionOrder",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalSectionOrder:2375"
    },
    {
      sourceName := "OAI.PiExponent.LocalSectionOrder.localFrameChange",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalSectionOrder",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "02d2c243b4003b198c7b3b0287ed9611cecdc94c1930e347d57cb16d28c22ff3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalSectionOrder",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalSectionOrder:653"
    },
    {
      sourceName := "OAI.PiExponent.LocalSectionOrder.sectionOrder",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalSectionOrder",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "da5dd1bf52c85d0f56c0dfad7224fc2c26affea0792d814c8e82bad47774add8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalSectionOrder",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalSectionOrder:1633"
    },
    {
      sourceName := "OAI.PiExponent.LocalSectionOrder.sectionOrder_frame_independent",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalSectionOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "96eb17d80d9258f817d72e3176c77f3d0e626d5a273142de0d8751404d5b77e5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalSectionOrder",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalSectionOrder:1931"
    },
    {
      sourceName := "OAI.PiExponent.LocalizedAlgebraEvaluation.denominatorMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedAlgebraEvaluation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "57e4eb5be67a2012320bff052ce4b81131ff663a838bcc8e47c110b3abf0d502",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedAlgebraEvaluation",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedAlgebraEvaluation:337"
    },
    {
      sourceName := "OAI.PiExponent.LocalizedAlgebraEvaluation.evaluation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedAlgebraEvaluation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "583e2c98993d9907361ddc5b90b460172a4c141214cb773963b50d68541e1662",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedAlgebraEvaluation",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedAlgebraEvaluation:624"
    },
    {
      sourceName := "OAI.PiExponent.LocalizedAlgebraEvaluation.evaluation_mk",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedAlgebraEvaluation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3835831574c76ac86cd481eba9fc67d2a0f071836308bb2ed009cc75383eff34",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedAlgebraEvaluation",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedAlgebraEvaluation:1791"
    },
    {
      sourceName := "OAI.PiExponent.LocalizedAlgebraEvaluation.evaluation_smul",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedAlgebraEvaluation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e3f4de542974a2d4e2041a504d41e0542355f3ed5c8e3e0b4ae6e03c90cd5ec6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedAlgebraEvaluation",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedAlgebraEvaluation:2068"
    },
    {
      sourceName := "OAI.PiExponent.LogTailAnalytic.hasSum_coeff_mul",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "03b3601ddc266711f4b020b29c1bdcb3039c0af40f2806aa8cf4cabd63ec57d9",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:6271",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:6271"
    },
    {
      sourceName := "OAI.PiExponent.LogTailAnalytic.logTail",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "057f36ca0c65568aaf9357a7f5fc3a412fdad1b00fdb2d7e6ddcca6f3a348e97",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:267"
    },
    {
      sourceName := "OAI.PiExponent.LogarithmicContactIdeal.branchContact_congr",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7ea510eaaedaf4d1a7ac1c177d9ef802eff5e27c7e3754bd392b69858a6c1810",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal:3187"
    },
    {
      sourceName := "OAI.PiExponent.LogarithmicContactIdeal.expansion_polynomial_aeval",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "02794436f41ba226499a05c1b9d13c706aa04a247b189ed2bc03db8597ea7051",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal:895"
    },
    {
      sourceName := "OAI.PiExponent.LogarithmicContactIdeal.expansion_truncatedCoordinates",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "12766e37d8616b2b7dc839ada56a01f18dcfdc3da4372593336fb740a36af037",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal:1285"
    },
    {
      sourceName := "OAI.PiExponent.LogarithmicContactIdeal.logarithmicIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "808809816cc5753c6f106a29cf50f523e133d8f8baf9c0888422d87ecc47833d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal:687"
    },
    {
      sourceName := "OAI.PiExponent.LogarithmicContactIdeal.logarithmicIdeal_colength_eq_contact",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "feaed3f9cc04c3a149d05f2532f9da78b261432491561629d2e461f1c774376f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal:4899"
    },
    {
      sourceName := "OAI.PiExponent.LogarithmicContactIdeal.truncatedCoordinates",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "69203cc50c3e5ff6c1ee9b6e3ba81cc6b0990b19acad1c63b13a4f1278debe8d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal:420"
    },
    {
      sourceName := "OAI.PiExponent.LogarithmicContactIdeal.truncatedCoordinates_nonzero",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d1835b72f7c9d8c6e495b5a849c83a3b3a846c88546736878ce3fdafa8a566ba",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal:2216"
    },
    {
      sourceName := "OAI.PiExponent.LogarithmicContactIdeal.truncated_contact_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a62118b3f08fba64e238d35aeb4caf6c2f37ca1193e7de1dbc8e55a6267c2e7d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal:3455"
    },
    {
      sourceName := "OAI.PiExponent.MatrixArithmetic.columnCost",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5bd035755c88d60de1f563583d48f57a3dbabd49556e57b4facbd0646305b4fa",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:9152"
    },
    {
      sourceName := "OAI.PiExponent.MatrixArithmetic.columnScale",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "50b8fdf28699700567042dfc4fbaef4c57be21b41b53362332819893861af63a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:6054"
    },
    {
      sourceName := "OAI.PiExponent.MatrixArithmetic.denominator",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "191ad789555602d4d17f47d1c6b892d3573ec2658b7869a52ef3cdf690dbf21a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:6289"
    },
    {
      sourceName := "OAI.PiExponent.MatrixArithmetic.logWeights",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8ef49fa76d76971c4b1d1506cda093434a6c8c316d6d77e2fd7020145cebce76",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:5936"
    },
    {
      sourceName := "OAI.PiExponent.MatrixArithmetic.meanRowWeight",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "efb39a5322d227e492931b8b83f48ec2652dd83a2775d047acd0cf9558cd377d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:8704"
    },
    {
      sourceName := "OAI.PiExponent.MatrixArithmetic.meanRowWeight_le_theta",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "17434665ee7c690078b1baa04c64e6333c7db5f0ed7aa646752a37ee28b20d78",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:20099",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:20099"
    },
    {
      sourceName := "OAI.PiExponent.MatrixArithmetic.rationalCenters",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "187f1dbb28fc63e6cbff30f58278fcfd19d43fd578647a5d80b85c36d72e2da5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:6457"
    },
    {
      sourceName := "OAI.PiExponent.MatrixArithmetic.rowCost",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "af88da33a3b8c5c31a4f7e2b0923931d89591b41229607bde47c6faadf3c73dc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:8932"
    },
    {
      sourceName := "OAI.PiExponent.MatrixArithmetic.rowScale",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "03a5a484c64b2510306f02abb0456e829fe6d180cb539ee04346442f4e395b35",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:6174"
    },
    {
      sourceName := "OAI.PiExponent.MatrixArithmetic.rowWeightedSum",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cf170101c12b2c81f6a16429540aac06dce1f0799c0e88fed6bea724dda2ee06",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:8477"
    },
    {
      sourceName := "OAI.PiExponent.MatrixArithmetic.selectedMinor",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3cfa08b2c2b8384642ef8093e8a03fae6d66b29634e3e67341b5fe7d80e99625",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:9514"
    },
    {
      sourceName := "OAI.PiExponent.MatrixArithmetic.selectedMinor_arithmetic_lower_bound",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1f76986e1e375b9a157c82b4c1ac4ef7c6d4d13ac64e80c0ebf2c12aa6f5f8b0",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:17647",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:17647"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_012.jsonl"
