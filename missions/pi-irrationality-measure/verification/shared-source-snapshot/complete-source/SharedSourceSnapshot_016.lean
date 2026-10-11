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
      sourceName := "OAI.PiExponent.GradedSerreStep.HasPrimitive",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedSerreStep",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "465c502d34bb40b95f27a44eac9bcc2b4b6959d642214aa56fbb0aa3b5e435d9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedSerreStep:672",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedSerreStep:672"
    },
    {
      sourceName := "OAI.PiExponent.GradedSerreStep.HasRecovery",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedSerreStep",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7bf44969d7aeb8fefce34e71ad8919ca6bab9f28f5dd8c1b40b2aadb4c6d3993",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedSerreStep:1080",
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
      sourceName := "OAI.PiExponent.GradedSerreVanishing.eventually_augmentation_recovery",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedSerreVanishing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3bd572c1d5269ffb0cbba57559ada6eb521bb00500cf6701912e5d3b1b608a79",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedSerreVanishing:3014",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedSerreVanishing:3014"
    },
    {
      sourceName := "OAI.PiExponent.GradedSerreVanishing.eventually_hasPrimitive",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedSerreVanishing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f627b8dccbbab54ed037d516995b6f9df7eb49a75815635405596cab80f0cb49",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedSerreVanishing:2065",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedSerreVanishing:2065"
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
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading:596",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading:596"
    },
    {
      sourceName := "OAI.PiExponent.HomogeneousSubmoduleGrading.decomposition",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c9abebd066efbfe175ab2b59d91f24ce6d60bc465971b6d9e10eedd43d9ece07",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading:2526",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading:2526"
    },
    {
      sourceName := "OAI.PiExponent.HomogeneousSubmoduleGrading.decompositionMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "788e11dd8d9cfa5ba9025b15438814588595a6b92beba68c18d7e2b3848823cd",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading:773",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading:773"
    },
    {
      sourceName := "OAI.PiExponent.HomogeneousSubmoduleGrading.decompositionMap_homogeneous",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "160d9a683efa86a287e7fd3e9393ddcf646ca95d1e2c908423c26bca8a22c3a7",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading:2097",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading:2097"
    },
    {
      sourceName := "OAI.PiExponent.HomogeneousSubmoduleGrading.decompositionMap_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "83d2f61ff0198c67ef8608adbc4f90e6b94667557a5dcec3eda76ac9bc2c6c5a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading:1838",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading:1838"
    },
    {
      sourceName := "OAI.PiExponent.HomogeneousSubmoduleGrading.gradedSMul",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7bb97b5e9893936adda45e7e9a21ab1170fdc07eb46219d9337bfbbeab8bb637",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading:3464",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading:3464"
    },
    {
      sourceName := "OAI.PiExponent.HomogeneousSubmoduleGrading.piece",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9f4878c8940780f9297525e1cdd87373ac4a80adf99fa8f86ee865c4fba038f5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading:378",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading:378"
    },
    {
      sourceName := "OAI.PiExponent.HomogeneousSubmoduleGrading.subtype_degree_compatible",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0ab250ac05af6d6795b453127721334ba61b8d939b9f58cedf52befe11e1062c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading:3159",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSubmoduleGrading:3159"
    },
    {
      sourceName := "OAI.PiExponent.IdealFiniteGenerators.exists_generators",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealFiniteGenerators",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "00db5104a0cac60ba14959d6e6fbac641bfe6af2f87a6e8e196ad3cd97567ef3",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealFiniteGenerators:116",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealFiniteGenerators:116"
    },
    {
      sourceName := "OAI.PiExponent.IdealSectionRestriction.comap_app_bijective_iff_open_square",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackOpenSquare",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f25a06d1467a85e1f6d010bc1c42bb8b9a631d7a1271ac6205fdfcabaea8aa63",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackOpenSquare:3721",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackOpenSquare:3721"
    },
    {
      sourceName := "OAI.PiExponent.IdealSectionRestriction.idealCongr",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealSectionRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7db170a18a9161311e0e1127da7c1e183d8502e499879c5a6c84f7fe276a4a6f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealSectionRestriction:3059",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealSectionRestriction:3059"
    },
    {
      sourceName := "OAI.PiExponent.IdealSectionRestriction.idealCongr_inclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealSectionRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0e03eda16f042bde93f35bf6260dc1929f6b7d73164905582503340b864362dd",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealSectionRestriction:3224",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealSectionRestriction:3224"
    },
    {
      sourceName := "OAI.PiExponent.IdealSectionRestriction.inclusion_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealSectionRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fbfc03cc6f753b0a76a34d5e3710cf73deedf343c3c2a299fc9377f9603152be",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealSectionRestriction:1067",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealSectionRestriction:1067"
    },
    {
      sourceName := "OAI.PiExponent.IdealSectionRestriction.pullback",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealSectionRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8ba9283a8763929699e376a355d1ebc1f379c6c598c27e6f8bde03515ea6e7af",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealSectionRestriction:1405",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealSectionRestriction:1405"
    },
    {
      sourceName := "OAI.PiExponent.IdealSectionRestriction.pullback_bijective_iff_comap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealSectionRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a87217681d74a7ad24c3f8c49858f49dbbf8f5fc585ab3286c43e8bbd6233802",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealSectionRestriction:4829",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealSectionRestriction:4829"
    },
    {
      sourceName := "OAI.PiExponent.IdealSectionRestriction.pullback_inclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealSectionRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8e1a04df1eef8719c62ae881ec539dc37b863cd7c77a74362e18dd5521c99222",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealSectionRestriction:1731",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealSectionRestriction:1731"
    },
    {
      sourceName := "OAI.PiExponent.IdealSectionRestriction.pullback_open_square",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackOpenSquare",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8d1552070d4faa08c919eba400ffd9692be47afcc48e123693850973ea344245",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackOpenSquare:1164",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackOpenSquare:1164"
    },
    {
      sourceName := "OAI.PiExponent.IdealSectionRestriction.pullback_open_square_bijective_iff",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackOpenSquare",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bdabff2b59807addf03ee46a1875f31ff5123b967bf5a2c4a9fee31d0f02aeb3",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackOpenSquare:2751",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackOpenSquare:2751"
    },
    {
      sourceName := "OAI.PiExponent.IdealSectionRestriction.pullback_self",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealSectionRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0f84e7bd6ec0fe1839e345ba164a5d2b4f36941ef2d9778c02928276df03b1e0",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealSectionRestriction:4450",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealSectionRestriction:4450"
    },
    {
      sourceName := "OAI.PiExponent.IdealSectionRestriction.sectionsEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealSectionRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7029cfde6764041761c48660e6097d4846f88b8f70128b3549ed5f93545774e0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealSectionRestriction:359",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealSectionRestriction:359"
    },
    {
      sourceName := "OAI.PiExponent.IdealSectionRestriction.sectionsEquiv_inclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealSectionRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e040caae1d1da4233c30554c2cc0d4e642dcc0a71fc645c10c7001a83bcf7f38",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealSectionRestriction:692",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealSectionRestriction:692"
    },
    {
      sourceName := "OAI.PiExponent.IdealSectionRestriction.squareIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackOpenSquare",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5f7689ffe88cb93b028ac103dd09625b96fc826b6538129802b76ec4997a10ca",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackOpenSquare:886",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackOpenSquare:886"
    },
    {
      sourceName := "OAI.PiExponent.IntegralAffineOpenDimension.affine_dimension_eq_ring",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IntegralAffineOpenDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c18f937c03cd73ee308f20e0b13637112bde9d5e5c99bf6102ae30722807b3ee",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IntegralAffineOpenDimension:3242",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IntegralAffineOpenDimension:3242"
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
      sourceName := "OAI.PiExponent.IntegralAffineOpenDimension.affine_ring_dimension_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IntegralAffineOpenDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c6a2be4818961c703c1b1678a696cb6162dbacd50c79d1f892e45ccd161cb073",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IntegralAffineOpenDimension:4437",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IntegralAffineOpenDimension:4437"
    },
    {
      sourceName := "OAI.PiExponent.IntegralAffineOpenDimension.chartAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IntegralAffineOpenDimension",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8183c0ebc497413a66087be6813d9a9eb83f57372d7730cb393c6a9087ba7692",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IntegralAffineOpenDimension:662",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IntegralAffineOpenDimension:662"
    },
    {
      sourceName := "OAI.PiExponent.IntegralAffineOpenDimension.chartConstants",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IntegralAffineOpenDimension",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bd1603c2214fe74048b04b43518c61b89ab695728c154647d222fb28defa0b1e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IntegralAffineOpenDimension:552",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IntegralAffineOpenDimension:552"
    },
    {
      sourceName := "OAI.PiExponent.IntegralAffineOpenDimension.chart_finiteType",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IntegralAffineOpenDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2de937660358c63ca61340aa56c61f7cb4399737345b7b6557b8362c54015245",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IntegralAffineOpenDimension:1793",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IntegralAffineOpenDimension:1793"
    },
    {
      sourceName := "OAI.PiExponent.IntegralAffineOpenDimension.chart_functionField_scalarTower",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IntegralAffineOpenDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "df31a2cfd5e0ec8045e8fa5c26032d57440d44ee4743779f3e72e1e1a717192d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IntegralAffineOpenDimension:1160",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IntegralAffineOpenDimension:1160"
    },
    {
      sourceName := "OAI.PiExponent.IntegralAffineOpenDimension.chart_ring_dimension",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IntegralAffineOpenDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1d4e5f832c7b299a36563a85563141cb7066159772450f9c96b4315fb2e81002",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IntegralAffineOpenDimension:2485",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IntegralAffineOpenDimension:2485"
    },
    {
      sourceName := "OAI.PiExponent.IntegralAffineOpenDimension.functionFieldAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IntegralAffineOpenDimension",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "08de8e6df002b3fdd5ef5251e00b02e3f872b7758bd87b9ca43a3432e497932d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IntegralAffineOpenDimension:784",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IntegralAffineOpenDimension:784"
    },
    {
      sourceName := "OAI.PiExponent.IntegralAffineOpenDimension.germToFunctionField_fromSpec",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IntegralAffineOpenDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b58e92e45f81754390c8a235b98f3473f15bb83c7520b34b6ebb34610ffb2347",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IntegralAffineOpenDimension:939",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IntegralAffineOpenDimension:939"
    },
    {
      sourceName := "OAI.PiExponent.InterpolationMatrix.Column",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "99b51bbf41b6927c6d942783d855f6e3bbf8b609c48e178bcd56401871815ded",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:2516",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:2516"
    },
    {
      sourceName := "OAI.PiExponent.InterpolationMatrix.Row",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "44b01340fc31199b300735d46af8dadce845823150f853e579c7bf52583089b0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:2649",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:2649"
    },
    {
      sourceName := "OAI.PiExponent.InterpolationMatrix.columnWeights",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b4649aa17c94b147a971a0103ddfb8b742cc7bc83d77a08bcd002eec5559b7ce",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:2274",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:2274"
    },
    {
      sourceName := "OAI.PiExponent.InterpolationMatrix.column_mem_iff",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "55da3e5ba50f6832b16e5967d53cf1bd778da3d0821d29b76f80dcd78bd75f76",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:2803",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:2803"
    },
    {
      sourceName := "OAI.PiExponent.InterpolationMatrix.column_weight_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "55bc67da6240a56ea8b8eaa447f2f59c5117930b09efb7698c82a5b594a72661",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:3845",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:3845"
    },
    {
      sourceName := "OAI.PiExponent.InterpolationMatrix.entry",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "adea7557d1f4e6389410cf84be65cbae9c83b0114511afbd483e6286cfd1bd12",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:1150",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:1150"
    },
    {
      sourceName := "OAI.PiExponent.InterpolationMatrix.entry_eq_binomial_product",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5539733b04cece3daea12cfc19bb4fbd82c193c59a2ccad741c3a3c23b97aec7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:300",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:300"
    },
    {
      sourceName := "OAI.PiExponent.InterpolationMatrix.entry_eq_zero_of_not_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "725d1ede5bf1883858ca746ef7adc918a6f5bccfdd4cc957f55cfac48e7e5178",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:1897",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:1897"
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
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:198",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:198"
    },
    {
      sourceName := "OAI.PiExponent.InterpolationMatrix.exponentVector_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "85555e75c5c508b567c70404e7b24342b90556571f99ca292d367110857c89db",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:321",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:321"
    },
    {
      sourceName := "OAI.PiExponent.InterpolationMatrix.gaussian_center_cast",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b2b5fa68283d6a268126a806fc092ca48a925955edd3b6766f289439ae7ee865",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:2950",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:2950"
    },
    {
      sourceName := "OAI.PiExponent.InterpolationMatrix.linearEvaluation",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eba74696307a5b9b0330df20dbca4b2ace0dfb5f82293a76f2670c919be3714d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:4674",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:4674"
    },
    {
      sourceName := "OAI.PiExponent.InterpolationMatrix.linearEvaluation_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "92e601d821e2a76cd15ed57f576b789d867c45ff350c17331714290ea205fdd3",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:4948",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:4948"
    },
    {
      sourceName := "OAI.PiExponent.InterpolationMatrix.linearEvaluation_eq_coeff",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "77c8e0659054045489325164e6c0aa35070145b8302ea6eeb9e4ee1bf8628463",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:5332",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:5332"
    },
    {
      sourceName := "OAI.PiExponent.InterpolationMatrix.matrix",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b50e45de51ce7fc5e347128e0cba975d3b0165b6d5a6b77008223dcf68e21dec",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:4363",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:4363"
    },
    {
      sourceName := "OAI.PiExponent.InterpolationMatrix.monomialImage",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7974bc06efb855731b00686cac46d3db49616b6cfb9aaab5612ed3e30ba687b0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:824",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:824"
    },
    {
      sourceName := "OAI.PiExponent.InterpolationMatrix.rowWeights",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3086f7e37df893e7b9548134e9ac8bf191310cf5f25cd4e96f932d98b32bbcb8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:2379",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:2379"
    },
    {
      sourceName := "OAI.PiExponent.InterpolationMatrix.row_card",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "10a91e1e0073d665bbc29b3ce0b054684e685100bb0cc3812f0993e669ae7c7f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:5836",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:5836"
    },
    {
      sourceName := "OAI.PiExponent.InterpolationMatrix.row_mem_iff",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cc924895fcd81279eac3ece6509640cd5557c86b287375c09bfd9cc6b8530fa9",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:3259",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:3259"
    },
    {
      sourceName := "OAI.PiExponent.InterpolationMatrix.row_weight_lt",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cbce62b2854fc4d2584401b2fb65b481ff270ce6797ac765e1c6fd3727668504",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:4085",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:4085"
    },
    {
      sourceName := "OAI.PiExponent.InterpolationMatrix.scalar_product_mul_coeff",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b5a29f3b49959a25703fae2a6d45901da0c8eb5194b698186f7b5ada8e1c2606",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:2418",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic:2418"
    },
    {
      sourceName := "OAI.PiExponent.InterpolationMatrix.sectionImage",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ef80ea28a0ade0b92b7aa795990c084764ce0e8e6b3e6f245544b0a764f48951",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:1383",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:1383"
    },
    {
      sourceName := "OAI.PiExponent.InterpolationMatrix.sectionImage_coeff",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "94fa766b06f9c842fdcb4f5147d9b39e509828b6a7fad734e1fed1cc6b3fe673",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:1708",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:1708"
    },
    {
      sourceName := "OAI.PiExponent.InterpolationMatrix.truncatedLog",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7ef7357df66b51deafd170fc419e02859efa431bf58989c475c879d6f8d96f33",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:466",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:466"
    },
    {
      sourceName := "OAI.PiExponent.InterpolationMatrix.truncatedLogMatrix",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "546fb3e82c50f72d1d42a0345147cb72db3d31fbbd42f000b5ae5e6ee1ae5eb5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:8124",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix:8124"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.dualMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b04701d0f9549dac25d67dab4cb0c5989b7804b46922ca50c6c1b06ce27d74aa",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:6304",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:6304"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.dualMap_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "431d259ef9bd8e35aadf99f3e1b25d0d7c05170a3e20a6b6645955ef1acc6a72",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:6452",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:6452"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.dualMap_coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "63ae0960a2ed7f548f957a55e49015d139222da85dc919bfeb27ffe5ab0728e3",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:6927",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:6927"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.dualMap_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseDualRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c73ea1221ee9eec527c215999cc0398d153c07108592d19a6e641db4e605cdcc",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseDualRestriction:407",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseDualRestriction:407"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.dualMap_restrict_coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseDualRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "43abff16da5d7f04f3ba928550ff6c6bc8d280ed0e64245136ff6e0e72ee68da",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseDualRestriction:2012",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseDualRestriction:2012"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.dualSection_restrict_coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseDualRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ed308cc28b70ebd144f32f5b57c62b58c4a82024348b06915d94960d97254573",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseDualRestriction:2480",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseDualRestriction:2480"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.frame_generator_change",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c8f7e794411a0349c8d597dd609298e5ffd887abc749f227121bae8e6f1bc496",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:2125",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:2125"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.inverseOpenFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8d5bf7f27dea86c5068fd49466af31f26ccc460ad9ca9d0c7fd2d6deb67c2434",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:7685",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:7685"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.inverseOpenFrame_frameChange",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8dc5765cd94e840f34c5d633fd04b2f3cfa8603b834a3c5bfaa0c7cbac0db729",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:7878",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:7878"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.inverseOpenFrame_pairing",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrameRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ed6900afb827075c0945846332ae7fd8d9288033bf16de6442ad2e71cb41a4a1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrameRestriction:1407",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrameRestriction:1407"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.inverseOpenFrame_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrameRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "69edaf764105f0d8b6470f8e28544615dbe62c194e2bea151dbe46ed30184008",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrameRestriction:4627",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrameRestriction:4627"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.inverseOpenFrame_restrict_pairing",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrameRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e9f9d7499d42412467e325dff04fe8522eeca529171aacea01a4c920f67b42a0",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrameRestriction:3069",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrameRestriction:3069"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.pairingFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5f042187732cadb03bb4f1ceb0c3a467eb2ddc6581d44eff79978a3f53637dd7",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:522",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:522"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.pairingFrame_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e4f81e5ac35e0b13603d0e806c3a71d3f7ddf2281d5b416d67f8408ee693c279",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:1617",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:1617"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.pairingFrame_change_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "84b06c779078e44b8ed3fc17256d959cf4262a901bc9b1f634f6d613c9bfd01a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:2702",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:2702"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.pairingFrame_frameChange",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8ae798caa17ccbfe2dda7ab33d5c95456f8f261004773effd1e54e6777de9b37",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:3645",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:3645"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.pairing_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "acd5238ee238b3b2eda7bc17781d6802fbbcd4b6a20c63c65e7c17d5125111ab",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:4407",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:4407"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.pairing_inverse_generator",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4deea2dc47541f8b0cacbe8bad8a3b71d68ab3dd0be3922707bed2530ae2eda7",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:5644",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:5644"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.pairing_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrameRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "07818bae385c922e4edca419521396aef13854c1513dc254f15c0f73358baa23",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrameRestriction:1880",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrameRestriction:1880"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.regularValue",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "29b5bdccc72df8574c18d1ec69cce65e8b4d20ea59a55cbdcad52ed70d08f3dd",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:405",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:405"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.restrictPairing",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6cc54c8a9440a209d6ab772d7fd749782f6272a55bdfa2ea6b5f94981b404690",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:7389",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:7389"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.restrictPairing_pure",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrameRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "50738baa7a9b5ed4edacd5fdae63072f8289fee83f60acfec06c89d56f964449",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrameRestriction:417",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrameRestriction:417"
    },
    {
      sourceName := "OAI.PiExponent.InverseFrames.unit_inv_pure",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4da4316bd6869d4585450ee4dbd132d9293ca359337c704819dceedde53174dd",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:687",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrames:687"
    },
    {
      sourceName := "OAI.PiExponent.InvertibleIdealAway.inclusion_isIso_of_comap_top",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealAway",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9be3628bbbd4651e0d5993b3470ecb3dece3f84b2c6f3ca55cc44fa1714a2752",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealAway:1845",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealAway:1845"
    },
    {
      sourceName := "OAI.PiExponent.InvertibleIdealAway.pullbackIsoOfAvoids",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealAway",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c1cfb251145cd26d78c7c74dbcf7a53e454b7d0d44aed9fc9e5395f76a30a677",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealAway:4938",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealAway:4938"
    },
    {
      sourceName := "OAI.PiExponent.InvertibleIdealAway.pullback_inclusion_isIso_of_avoids",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealAway",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "92375909eb874bc4faa3ee6c4acc6f355526d03385d919618e63f2c20198784b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealAway:3455",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealAway:3455"
    },
    {
      sourceName := "OAI.PiExponent.InvertibleIdealAway.pullback_map_isIso_of_factors",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealAway",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "92541da5488be0906251d82e59e290bd5187751909583b66c9154dcbda5790df",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealAway:2623",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealAway:2623"
    },
    {
      sourceName := "OAI.PiExponent.InvertibleIdealAway.restrictedInclusion_isIso_of_unit",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealAway",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "34dfe23fe3581bcaefed66e5f3e898602ea226358a69a865df0ebad19934ff63",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealAway:699",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealAway:699"
    },
    {
      sourceName := "OAI.PiExponent.JetCenterIdentification.centered_of_closedPoint_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetCenterIdentification",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fd1fb589862cec4507c33f02bf2340e34cdc2d90d17944e441ccdbb0603561a3",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.JetCenterIdentification:389",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetCenterIdentification:389"
    },
    {
      sourceName := "OAI.PiExponent.JetGeometry.RationalCoefficientPacket",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetGeometry",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f2f3b033afc8e54fd7366ac8149e75168d90ecc52f2f99aeadf8bba381de2d7a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:8569",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:8569"
    },
    {
      sourceName := "OAI.PiExponent.JetGeometry.coordinatePowerIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetGeometry",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a575c534cf80c72e21edf89cc1a60779c22fbe299dc74757e16986cb381a2837",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:2101",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:2101"
    },
    {
      sourceName := "OAI.PiExponent.JetGeometry.coordinatePowerIdeal_pow_le_rational",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetGeometry",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dd9980d799bc7e1f9f63a44bfb993c0107502220c3d987f052ed40136c30d9dd",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:7991",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:7991"
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
      sourceName := "OAI.PiExponent.JetGeometry.ideal_pow_le_weightedIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetGeometry",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bad24716e0a034c49b54be6f2762c3f73e93ea0d27285741e6698f6347e99ded",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:1576",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:1576"
    },
    {
      sourceName := "OAI.PiExponent.JetGeometry.mem_rationalWeightedIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetGeometry",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2436bdcad1db281c88f2578dcf703fb01313e193803533148ee94e9fbdbe7ed8",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:6270",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:6270"
    },
    {
      sourceName := "OAI.PiExponent.JetGeometry.mem_weightedIdeal_iff",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetGeometry",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "adfff4f12f12cf3f5cee56068b4704be75f9f9d863f85129bad549fe61295ba7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:794",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:794"
    },
    {
      sourceName := "OAI.PiExponent.JetGeometry.rationalCoefficientPacket",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetGeometry",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6b635bdb7ffbabfba37e1000b5b0da03e349af14fddea2ed72f868e90c7ed5f9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:8687",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:8687"
    },
    {
      sourceName := "OAI.PiExponent.JetGeometry.rationalWeightedIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetGeometry",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "32e325a1c11e414b39019959f83051c27016287422cee716bcace50a5a3535ab",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:5541",
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
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:5300",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:5300"
    },
    {
      sourceName := "OAI.PiExponent.JetGeometry.weightedIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetGeometry",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8cb1a802cafb0361ff351c30d8a45bdc4f5754650412adba9ab385e0e0c77dfe",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:242",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:242"
    },
    {
      sourceName := "OAI.PiExponent.JetGeometry.weightedIdeal_mul_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetGeometry",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7b28b25164269ba9da07688fa8f7f6924c579c837cd203342102db1b73a85109",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:1210",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:1210"
    },
    {
      sourceName := "OAI.PiExponent.JetPowerIdealCoprime.center_pointIdeal_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetPowerIdealCoprime",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e9044e314ebf718269cf043e5f8380b71a645f1a3c091133cbf630010c4ea31c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.JetPowerIdealCoprime:666",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetPowerIdealCoprime:666"
    },
    {
      sourceName := "OAI.PiExponent.JetPowerIdealCoprime.pointIdeal_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetPowerIdealCoprime",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7faf987460fcb97247714591ec36109626f3fd66c4278b717710892e357470b1",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.JetPowerIdealCoprime:275",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetPowerIdealCoprime:275"
    },
    {
      sourceName := "OAI.PiExponent.JetPowerIdealCoprime.powerIdeal_pairwise_isCoprime",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetPowerIdealCoprime",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "292427a85d59face6d9f21b4551c63e2d5e97b82f67a3778f12dc2fbab710617",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.JetPowerIdealCoprime:893",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetPowerIdealCoprime:893"
    },
    {
      sourceName := "OAI.PiExponent.JetPowerIdealCoprime.powerIdeal_pow_pairwise_isCoprime",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetPowerIdealCoprime",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "876e8c944726a94cda578a688269f1f2f430e1c2794e04bc5c722cf7bb6cf690",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.JetPowerIdealCoprime:1664",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetPowerIdealCoprime:1664"
    },
    {
      sourceName := "OAI.PiExponent.JetProductLocalization.logarithmicIdeal_eq_top_of_residue_ne",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "466b3eab631e9baab5f966ecd24ad7ebff248fad3469a436445cbe5f625db1d9",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization:1967",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization:1967"
    },
    {
      sourceName := "OAI.PiExponent.JetProductLocalization.map_polynomialIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0187ec53e7ddcfa3cfe29896cd4cb6f6d65530159d9989f2fe6d2d771d4184c2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization:3866",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization:3866"
    },
    {
      sourceName := "OAI.PiExponent.JetProductLocalization.map_polynomialIdeal_eq_selected",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "913428d6b7d749767a575221e18031bd7970722b0acb61b22ccf67bf8ad68746",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization:4505",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization:4505"
    },
    {
      sourceName := "OAI.PiExponent.JetProductLocalization.map_powerIdeal_eq_top_of_ne",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a7029627236b713cb1a67422066c48a9dad19fea09b99bebbe8cc5958d69e10f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization:3208",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization:3208"
    },
    {
      sourceName := "OAI.PiExponent.JetProductLocalization.residueAlgHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9126324de820e827909e6282113117308de76e01b5adf6817eeabe0209336c12",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization:354",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization:354"
    },
    {
      sourceName := "OAI.PiExponent.JetProductLocalization.residue_ne_zero_iff_isUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "79c70def9bcf6fd6cb3a0f681de24e8a0502e75303acc81f5d5dccd7e5b3afce",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization:521",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization:521"
    },
    {
      sourceName := "OAI.PiExponent.JetProductLocalization.residue_polynomial_aeval",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "579c8b336f4ebf87861f70def2ec10b192f88db0771a4fd8fdfcf62382e50089",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization:892",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization:892"
    },
    {
      sourceName := "OAI.PiExponent.JetProductLocalization.residue_truncatedCoordinates_succ",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f5177cb2021bf97db8382c9edc9121fe565cac2cce8e435fa096bd20d6738445",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization:1229",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetProductLocalization:1229"
    },
    {
      sourceName := "OAI.PiExponent.LiteralAnalytic.ChoiceFamily",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b7b1350437fa43d4ab26e3ed927378f14bc9c91d45704e1b313e594ad3de8b84",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:958",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:958"
    },
    {
      sourceName := "OAI.PiExponent.LiteralAnalytic.RowChoice",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f6a1aac4ada433b06f78455a6aac6bade0262fc0e5fa7e7d49b5f923523dd191",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:769",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:769"
    },
    {
      sourceName := "OAI.PiExponent.LiteralAnalytic.Transverse",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7aea9a44c618ec4631fe725aef3c4f83d6426ac872d6611cbcb590c9c8d2ee52",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:476",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:476"
    },
    {
      sourceName := "OAI.PiExponent.LiteralAnalytic.actualRowCount_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1999010315f3621ed3cefd8491f25c91ae62ba91e3312274424470a1621e5f92",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:6046",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand:6046"
    },
    {
      sourceName := "OAI.PiExponent.LiteralAnalytic.actual_minor_analytic_bound",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.AnalyticAggregate",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "59cdcd0ef173c246a5f9da61a277b6f42bc57cb520ca03033903490f50956ede",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.AnalyticAggregate:2486",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.AnalyticAggregate:2486"
    },
    {
      sourceName := "OAI.PiExponent.LiteralAnalytic.actual_minor_expansion",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.AnalyticAggregate",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9f41def67553af73626c1d348d6fca2ecc70bdc5eb8c157ecf7f7c195a456cbc",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.AnalyticAggregate:275",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.AnalyticAggregate:275"
    },
    {
      sourceName := "OAI.PiExponent.LiteralAnalytic.analyticAggregate",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.AnalyticAggregate",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7e3390d249095a01af216e0e894007457ed425a09509bca6b43e4fa9dcbbdc06",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.AnalyticAggregate:4686",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.AnalyticAggregate:4686"
    },
    {
      sourceName := "OAI.PiExponent.LiteralAnalytic.analyticRemainder",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.AnalyticAggregate",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7963b2560a3c2cc7a10574cc7284e20151bde7c829ea66eac0759ec1a0796f9a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.AnalyticAggregate:2283",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.AnalyticAggregate:2283"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_016.jsonl"
