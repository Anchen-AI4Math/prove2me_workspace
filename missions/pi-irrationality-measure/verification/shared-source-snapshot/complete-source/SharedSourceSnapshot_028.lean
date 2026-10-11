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
      sourceName := "OAI.PiExponent.WeightedSliceDegree.supportBound_sliceMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c3797e1ea756d77afe2eb1449e8eca8d308faffae9213226b5defff09620a9d7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:5844",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:5844"
    },
    {
      sourceName := "OAI.PiExponent.WeightedSliceDegree.supportBound_sum",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "815c4bfeb3cac70ded83f97a7f73516f4ea665ef70ff5559305bfffe9aeb0159",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:2902",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:2902"
    },
    {
      sourceName := "OAI.PiExponent.WeightedSliceDegree.supportBound_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dc441061a873843e7f236da8a53a943be85bb5945bc66072859af8a02aebf90c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:541",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:541"
    },
    {
      sourceName := "OAI.PiExponent.adjoin_finite_no_logarithmic_differential",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.AlgebraicLogarithmicObstruction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2f09631d414eeca025f7bebadbd30ea6ef13f3886d266dc3f4a0c774494ae442",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.AlgebraicLogarithmicObstruction:3098",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.AlgebraicLogarithmicObstruction:3098"
    },
    {
      sourceName := "OAI.PiExponent.algebraicIndependent_of_pderiv_kernel",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceBasis",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "344e02a3cdd070cc6a9ce0c6743374107471e91c0b21a5e278f82b7917a1f483",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceBasis:6450",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceBasis:6450"
    },
    {
      sourceName := "OAI.PiExponent.approximatePeriod",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ApproximationCenters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e9a8432b0a205dd35eca65c13179fba7cc8fa5e19c96f527356ca67136d20ad5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ApproximationCenters:94",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ApproximationCenters:94"
    },
    {
      sourceName := "OAI.PiExponent.card_residueRectangle",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6d8b867545dff6682e0de84f829448de7c64bb98387cc2ca3f1b1f7c65636625",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:1333",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:1333"
    },
    {
      sourceName := "OAI.PiExponent.card_unweightedSimplex",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7512611b07e6fe56eb9839dcf211cce5ccab3676a47790ddbc0e29c05ba8177a",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted:751",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted:751"
    },
    {
      sourceName := "OAI.PiExponent.ceil_log_bounds",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ApproximationCenters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e8ec878d330a691eb8cc9c0c7cd6813e190ebd34568bbf549e35d77a65f3e4ac",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ApproximationCenters:1864",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ApproximationCenters:1864"
    },
    {
      sourceName := "OAI.PiExponent.common_denominator_simplex_constant",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexRational",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2720f490e2e1382e48dfd77ffc11a3983293f0601f5b90aa5c8e5c38caa81cef",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexRational:228",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexRational:228"
    },
    {
      sourceName := "OAI.PiExponent.constant_of_differential_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DifferentialConstant",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d14b5986ee1d38b901ab1c05e15ed3640b626626aec289f50338044eb38e62af",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DifferentialConstant:410",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DifferentialConstant:410"
    },
    {
      sourceName := "OAI.PiExponent.constant_of_logarithmic_differential",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.AlgebraicLogarithmicObstruction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "83de2692fe38f915b469bb10e4496715d706f717eb1eca4a08c91b6291ceabae",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.AlgebraicLogarithmicObstruction:5594",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.AlgebraicLogarithmicObstruction:5594"
    },
    {
      sourceName := "OAI.PiExponent.constant_zeroth_coordinate_of_generic_normal_separation",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GenericNormalRigidity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "050f944b0a2f04dc8fcc799c51d14545f32a0d732a7ab97cf2332c752fd6ee8b",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GenericNormalRigidity:1152",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GenericNormalRigidity:1152"
    },
    {
      sourceName := "OAI.PiExponent.coordinate_constant_of_generic_normal_separation",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GenericFibreRigidity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bc450becc8a35d138ca273954db884e868d4a610a496693dd1042def3f1f9fed",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GenericFibreRigidity:2166",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GenericFibreRigidity:2166"
    },
    {
      sourceName := "OAI.PiExponent.coordinate_constant_of_generic_normal_weight_comparison",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GenericFibreRigidity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0f2102724c8bec5f4a4830244b2e30c04bf81e5f4719f91e53ac95f13cf3fe53",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GenericFibreRigidity:2824",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GenericFibreRigidity:2824"
    },
    {
      sourceName := "OAI.PiExponent.coordinate_constant_of_generic_unique_normal_basis",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GenericFibreRigidity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0a3a80a14c493d231d6a330aba6cac90513203664984e69b1fdd920761d870af",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GenericFibreRigidity:619",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GenericFibreRigidity:619"
    },
    {
      sourceName := "OAI.PiExponent.derivation_basis_coordinates",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicObstruction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d6aa48a55bda110a39f241e2149d51e340f950ccd326d320da146cd71d932f6e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicObstruction:4915",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicObstruction:4915"
    },
    {
      sourceName := "OAI.PiExponent.derivation_eq_zero_of_field_generators",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceBasis",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1019020f916075a5eeff461a68582e8f53679b2ad6b607aa0ed516b92a3ac6e7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceBasis:8857",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceBasis:8857"
    },
    {
      sourceName := "OAI.PiExponent.derivation_intermediate_smul",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicObstruction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d5d6ac7e2631fdd8594dbc7945d7ac5c9f98c4ad7aa4cc10945cc37c27ef957a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicObstruction:4469",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicObstruction:4469"
    },
    {
      sourceName := "OAI.PiExponent.derivation_mem_polynomialTangent",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3df31054008d3653128f2e05bbb56978f734a54faf362b8307d68c1443ada607",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential:1676",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential:1676"
    },
    {
      sourceName := "OAI.PiExponent.derivation_polynomial_map",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "39505a239f3b34cbd8d8be8d1f817d3cebe6d106f114649c2210cb3362459f6a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential:477",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential:477"
    },
    {
      sourceName := "OAI.PiExponent.derivation_trace_of_basis",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicObstruction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6de2b51b6ca661c3c2a75c55bee62edbb0ba8364d643c11bfacd8022f3030821",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicObstruction:5681",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicObstruction:5681"
    },
    {
      sourceName := "OAI.PiExponent.determinant_bounds_inconsistent",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Comparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ad8df9f13714b21a1804010dcea86442e049d0d8028a9cd4e925c4a0034aaa60",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Comparison:146",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Comparison:146"
    },
    {
      sourceName := "OAI.PiExponent.differential_eq_zero_of_polynomialTangent",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "956f2ef324b824206e440cecff6932b059c143f2c1321dcc03da855a2d9b4e6e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential:3414",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential:3414"
    },
    {
      sourceName := "OAI.PiExponent.dimensionK",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f3045b67fedd17de5cd0ff4b327d1ee153229e76dd52c9aae93545eb0da21145",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:338",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:338"
    },
    {
      sourceName := "OAI.PiExponent.dimensionK_div_W_le",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a536d27bf90a2d287985b6606824b4634192ab61349e9b5f65d6ecd96e83e90f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:1904",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:1904"
    },
    {
      sourceName := "OAI.PiExponent.dimensionK_le",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ff9c8385d6295513aa8d89002112afe6d73ce04c110a0659e309ff086817c1a5",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:574",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:574"
    },
    {
      sourceName := "OAI.PiExponent.dimensionK_one_le",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "01ca67e6ba502f2c9f93b13ef82b6c1a2350958552219ac93d09cc671ad58ff9",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:711",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:711"
    },
    {
      sourceName := "OAI.PiExponent.dimensionV",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "80bfe228db13db7ba55f64588ebdbe776aa94e9632cc48e093bee9d988109a45",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:460",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:460"
    },
    {
      sourceName := "OAI.PiExponent.dimensionV_geometric_lower",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "590a45d19642887efb28c590764644cd4fba084111f6d6a5f7ed446964edc3aa",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:2175",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:2175"
    },
    {
      sourceName := "OAI.PiExponent.dimensionV_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a359025b7fd814e130b58b53ba853ef0a902ff9bcd203e770dd46d018a9b7b5e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:991",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:991"
    },
    {
      sourceName := "OAI.PiExponent.dimensionW",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "177680d0c0bed82b9a91b92f44da3ef4cf2d6bcae1f6cade40b10918b8fc6b99",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:400",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:400"
    },
    {
      sourceName := "OAI.PiExponent.dimensionW_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "74f0dcceb5ca1d1423c9e1402093eae0e1791af0859a7515c4de895986ec49ca",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:864",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:864"
    },
    {
      sourceName := "OAI.PiExponent.dimension_collision_identity",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b75b38551fe04f34843efade4e6d1b5e497595939238ce4a2acd1c3e3affde3f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:4023",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:4023"
    },
    {
      sourceName := "OAI.PiExponent.dimension_error_le",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ab17d5f0fb39e52ecb41829396dd6c4931702fb15528cb47b86eac0150e7020e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:3178",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:3178"
    },
    {
      sourceName := "OAI.PiExponent.dimension_volume",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "292c5c988c2826ae96318c3b8d1bcb8faec7445e778bdbfc414c7937ba29105e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:1367",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:1367"
    },
    {
      sourceName := "OAI.PiExponent.dimension_volume_lt_one",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "357bb7cfadc6c3be3c226e38dd497c44ae8fcc28dbf1db5e835659c3b95c13dd",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:2711",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:2711"
    },
    {
      sourceName := "OAI.PiExponent.eq_C_of_pderiv_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceBasis",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1d72e9ae2f53d5534d56a1769c56183a33be61d186f583dcb70f398ed18603a9",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceBasis:5618",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceBasis:5618"
    },
    {
      sourceName := "OAI.PiExponent.eq_constant_of_pderiv_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialNormalNonzero",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "330eca8d3586ddb12c9893fbe8dd615335c9dea0b51ed8b9675214261e5755db",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialNormalNonzero:1267",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialNormalNonzero:1267"
    },
    {
      sourceName := "OAI.PiExponent.eventually_auxiliary_card_lt",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.AuxiliaryPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6efe97bdc21a651e35dbf5b513f71fb16ae76d14fd3940ede5cce0821043150f",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.AuxiliaryPolynomial:4745",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.AuxiliaryPolynomial:4745"
    },
    {
      sourceName := "OAI.PiExponent.eventually_exists_auxiliaryPolynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.AuxiliaryPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6dbd9819a1d423c6df63dd6ec434fa3adb2f7d63bdd55f25f2e89879841490e7",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.AuxiliaryPolynomial:6481",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.AuxiliaryPolynomial:6481"
    },
    {
      sourceName := "OAI.PiExponent.eventually_exists_formalJet_auxiliaryPolynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalAuxiliaryJet",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7e92c038f9faf70a974ccfd65d9dabd47881f7163eb575dac9168e15378efb62",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalAuxiliaryJet:627",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalAuxiliaryJet:627"
    },
    {
      sourceName := "OAI.PiExponent.eventually_exists_formalJet_auxiliaryPolynomial_nat",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalAuxiliaryJet",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "da0da9b62ee251a5a9677627c9b637e624bb505c98010b7cd80789f81611509b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalAuxiliaryJet:1880",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalAuxiliaryJet:1880"
    },
    {
      sourceName := "OAI.PiExponent.exists_admissible_parameters",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4b055702bee6709b5df25877821a58836b842d4ccaca3e7138d22bfdb2b28100",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:4510",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:4510"
    },
    {
      sourceName := "OAI.PiExponent.exists_dimension_margin",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0f789582016806e57b459fbdfc8bf55c4414705bb6947330a4d8675df8180da9",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:5946",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:5946"
    },
    {
      sourceName := "OAI.PiExponent.exists_eta_preserving_exponent_gap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "648c20f32265b41d721dfdda3d2cc4675ab6633e6f57f26e6d57b9d89b995363",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:3327",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:3327"
    },
    {
      sourceName := "OAI.PiExponent.exists_initial_scale",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bb09a24d3a15687e2d217a6bea2815451d0c7296310b72816622c530fdb4df2f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:1601",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:1601"
    },
    {
      sourceName := "OAI.PiExponent.exists_intermediateField_finite_over_simple",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TranscendenceBasisReduction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "60d8119f5e29374a81f9b545a328ef879a63f4a97c18888721ecf7db0176f90b",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TranscendenceBasisReduction:249",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TranscendenceBasisReduction:249"
    },
    {
      sourceName := "OAI.PiExponent.exists_large_log_approximation",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ApproximationSelection",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "29ea3aefe6abc1fdf1ef571cc94bd04330236567a60e9b405ab64ff23c93455d",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ApproximationSelection:131",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ApproximationSelection:131"
    },
    {
      sourceName := "OAI.PiExponent.exists_minimum_weight",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightErrorMargin",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "76f976313216cbd1f2533fb5a8e364c2cfc0c0aeb3b17e3f04ca6a5a990e1097",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightErrorMargin:2136",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightErrorMargin:2136"
    },
    {
      sourceName := "OAI.PiExponent.exists_nonzero_kernel_of_card_lt",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.AuxiliaryPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "25b75c7e2557a0ec598e79f35d1e4d509fb02ac6a69debef44ba2ee25f48a896",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.AuxiliaryPolynomial:3474",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.AuxiliaryPolynomial:3474"
    },
    {
      sourceName := "OAI.PiExponent.exists_normalized_selection_of_selector",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SuccessiveApproximations",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0bb51e7427576e5caf1618bcd5426012f6ceff8fdb14368caaf5015526d09441",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SuccessiveApproximations:4368",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SuccessiveApproximations:4368"
    },
    {
      sourceName := "OAI.PiExponent.exists_normalized_successive_approximations",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SuccessiveApproximations",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fb3282cd490be3713cb045d44e60e9cf05ce28ac117a68b3d01f8858df2ef27e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SuccessiveApproximations:5926",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SuccessiveApproximations:5926"
    },
    {
      sourceName := "OAI.PiExponent.exists_parameters",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "874df33393af03a3b18c4eb2637b747d07f0750d6c6c7db0ddc918475ea83a4f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4839",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4839"
    },
    {
      sourceName := "OAI.PiExponent.exists_rational_parameters",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c28aee6d6c9c15d7b97dfa935532c2f91277023fddbef8555baafe5f6ff58f0f",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:91",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:91"
    },
    {
      sourceName := "OAI.PiExponent.exists_small_rational_sigma",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Sigma",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d36aeaaafe98665f85be84363040f8d59363715d62dc3c1b0bc1f5b2b10598be",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Sigma:91",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Sigma:91"
    },
    {
      sourceName := "OAI.PiExponent.exists_successive_approximations",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SuccessiveApproximations",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7f4079f521b5b240f3ef651bf5813d243a9e2e7c89ba03dcfa8cf9a4896d0fc5",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SuccessiveApproximations:164",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SuccessiveApproximations:164"
    },
    {
      sourceName := "OAI.PiExponent.exists_uniform_weight_error_margin",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightErrorMargin",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3bf1f6d8c9d1b0b60063d250163216e8f123e2a13aa9cb9fbb62ea6d7a108686",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightErrorMargin:1236",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightErrorMargin:1236"
    },
    {
      sourceName := "OAI.PiExponent.exists_weight_error_margin",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightErrorMargin",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9d5450c1f488e837b07162ed7a9d7624cbd2219f770ee46f2fb31baaf13214da",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightErrorMargin:91",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightErrorMargin:91"
    },
    {
      sourceName := "OAI.PiExponent.exponentVector_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.AuxiliaryPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "933a7b1f53fb903252a7acc669d13b0385c3ef52112ebc4e75b04d6051a9b87a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.AuxiliaryPolynomial:756",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.AuxiliaryPolynomial:756"
    },
    {
      sourceName := "OAI.PiExponent.extendDerivation",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.AlgebraicLogarithmicObstruction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9b24d6dae54a67ef00f35a09ec65489a31b05b684844db3eb81cdda348dfd516",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.AlgebraicLogarithmicObstruction:438",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.AlgebraicLogarithmicObstruction:438"
    },
    {
      sourceName := "OAI.PiExponent.extendDerivation_algebraMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.AlgebraicLogarithmicObstruction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3d981dab0fdfb4ec7582af27d2009fd746f42be4887517f9ea21bedabb713162",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.AlgebraicLogarithmicObstruction:850",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.AlgebraicLogarithmicObstruction:850"
    },
    {
      sourceName := "OAI.PiExponent.extendModuleDerivation",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8f8b1b2c0cac1c15e6ee209f6faa8b1c4bbd4e14ea18b75ac2584578dc2a7a71",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent:369",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent:369"
    },
    {
      sourceName := "OAI.PiExponent.extendModuleDerivation_algebraMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "214c17347ecc4b8c3e33979a57c461ebd7e04e012dcf9869ed63bd6ad5fcf41c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent:889",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent:889"
    },
    {
      sourceName := "OAI.PiExponent.finite_extension_derivation_ne_simple_pole",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicObstruction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8a4fb757898826bd340c4a2aa41dd876846616a60fc1c9ac48bfe95e26324201",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicObstruction:7453",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicObstruction:7453"
    },
    {
      sourceName := "OAI.PiExponent.finite_extension_no_logarithmic_differential",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.AlgebraicLogarithmicObstruction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fd9eac578c62d4e957780bfd668f873a0aa644b2b93ad38238be83ee231a802a",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.AlgebraicLogarithmicObstruction:1970",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.AlgebraicLogarithmicObstruction:1970"
    },
    {
      sourceName := "OAI.PiExponent.formalJetEvaluation",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalAuxiliaryJet",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f448563d56275c267bd4ab03d746fe8e21e99c3cde0367ae96b7871df789cbc1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalAuxiliaryJet:236",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalAuxiliaryJet:236"
    },
    {
      sourceName := "OAI.PiExponent.formal_period_collision_bound",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.Collision",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6499fa7aa2b0d6f947e74b53a40f84bd1325bee08080ed3cfa4699f7e0b6efcb",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.Collision:426",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.Collision:426"
    },
    {
      sourceName := "OAI.PiExponent.fromSpecStalkStalkIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FromSpecStalkLocalIso",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7c151c075da3756e9d96ee9674f46c8e88ef4cb3266c176645d6b31ca2957c82",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FromSpecStalkLocalIso:2410",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FromSpecStalkLocalIso:2410"
    },
    {
      sourceName := "OAI.PiExponent.fromSpecStalk_stalkMap_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FromSpecStalkLocalIso",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "31bb02190355e7c404945e7b01fb2e5ca529f979d6157db612162cd87cc27fa6",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FromSpecStalkLocalIso:1532",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FromSpecStalkLocalIso:1532"
    },
    {
      sourceName := "OAI.PiExponent.genericCoordinateNormals",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GenericFibreRigidity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e7fa6251a1ee7fff00708ee8d7754789ee03b37ced5aaf8fc7a369afe8c060a5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GenericFibreRigidity:414",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GenericFibreRigidity:414"
    },
    {
      sourceName := "OAI.PiExponent.gradedMap_homogeneous_lift",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SurjectiveGradedMap",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b5c1d818104c1558d13e8de36ae0b71e85b6759fa2fd74d55833dc90327209bd",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SurjectiveGradedMap:399",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SurjectiveGradedMap:399"
    },
    {
      sourceName := "OAI.PiExponent.gradedMap_irrelevant_le_map",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SurjectiveGradedMap",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "72dc35ee9c1765d275b019e34d285d1f0d1d7b90272eadf994aad8c2e22db08e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SurjectiveGradedMap:740",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SurjectiveGradedMap:740"
    },
    {
      sourceName := "OAI.PiExponent.holomorphicError",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.Collision",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2faf0d0fcc7fc01cade36a60aff045c007cd4abcfc2a372e93365e157c2ebf22",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.Collision:286",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.Collision:286"
    },
    {
      sourceName := "OAI.PiExponent.homogeneousAway_map_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SurjectiveGradedMap",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "979e1651e206eed96d46164a3572520779266fd7724322aa512bbf2e93d63ab2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SurjectiveGradedMap:1077",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SurjectiveGradedMap:1077"
    },
    {
      sourceName := "OAI.PiExponent.idealResidueMap_field_generation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceBasis",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b14df93a5d000f33f9b6e22dff2b5da5c3dc5f2c18e6cdba1320177695fce155",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceBasis:13738",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceBasis:13738"
    },
    {
      sourceName := "OAI.PiExponent.idealResidueNormalBasis_complement_isTranscendenceBasis",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceBasis",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7704a10be04b384e3237d6b8098c575bab2812cd5de8d53c82f3219ca61159ef",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceBasis:14588",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceBasis:14588"
    },
    {
      sourceName := "OAI.PiExponent.ideal_eq_bot_of_pderiv_stable",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialNormalNonzero",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3b242dac51ad75408fbb0390da41a87e245f901204b534499cdc252492f8bf33",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialNormalNonzero:2297",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialNormalNonzero:2297"
    },
    {
      sourceName := "OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_oAI",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PolynomialProjectiveStructure",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "36200a3151e5e849e58228b859bb67b33bdb767c26bedd59b6bb091578757300",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PolynomialProjectiveStructure:1257",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PolynomialProjectiveStructure:1257"
    },
    {
      sourceName := "OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_oAI",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PolynomialProjectiveStructure",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5ec86caff9b67611f714232e099235b2edd38ed6ac2bcdee39d1957f9bffe993",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PolynomialProjectiveStructure:1051",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PolynomialProjectiveStructure:1051"
    },
    {
      sourceName := "OAI.PiExponent.interpolationSeparationConstant",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4f5a507b47c8d9b0742c774a1b9da1545a4d1829a09979bbdad51ebc5971c23e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:552",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:552"
    },
    {
      sourceName := "OAI.PiExponent.interpolationSeparationConstant_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d671dbb3797bf3b62ccdf0a8ba3986cc8a52dc2407cd8624f191947f98016275",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:726",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:726"
    },
    {
      sourceName := "OAI.PiExponent.isAlgebraic_of_logarithmic_differential",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.AlgebraicLogarithmicObstruction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d1494e3e4db5d2b1848694c47b28efb9b60807794636546daef445449362ddf7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.AlgebraicLogarithmicObstruction:5146",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.AlgebraicLogarithmicObstruction:5146"
    },
    {
      sourceName := "OAI.PiExponent.literalJetSubstitution",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AuxiliaryJetMap",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d2c06faed246519f027612a714df08b2caaca18672f98eddccf85162a57ccf43",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AuxiliaryJetMap:161",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AuxiliaryJetMap:161"
    },
    {
      sourceName := "OAI.PiExponent.literalJetSubstitution_monomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AuxiliaryJetMap",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "818cc9ba9c81568376b0a7046b0007bc7b66fa71067175f5d76cdabbdc1bcf85",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AuxiliaryJetMap:1538",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AuxiliaryJetMap:1538"
    },
    {
      sourceName := "OAI.PiExponent.literalJetSubstitution_polynomialOfCoefficients",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AuxiliaryJetMap",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9cab0f5b37220392f3304d833eaf0720ec1b2bd0f89dc07dfe916b950e2bfa08",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AuxiliaryJetMap:2219",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AuxiliaryJetMap:2219"
    },
    {
      sourceName := "OAI.PiExponent.localIsolatedBezout",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalBezout",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "050e1fbcd6df306f88ae6cd7c99b300317a61c33c53489972a24d053fe835311",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalBezout:219",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalBezout:219"
    },
    {
      sourceName := "OAI.PiExponent.logarithmicPeriod",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ApproximationCenters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "865991db65d4ff0e74db78071749ee0e0524912f3fc1167b50a4ce88d6b58d70",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ApproximationCenters:809",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ApproximationCenters:809"
    },
    {
      sourceName := "OAI.PiExponent.logarithmic_differential_base_change",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.AlgebraicLogarithmicObstruction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3c69acc968d8d26e2bad04200a3d95a6fa73229fd7898dedf2ec7ecb0fba02a8",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.AlgebraicLogarithmicObstruction:4336",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.AlgebraicLogarithmicObstruction:4336"
    },
    {
      sourceName := "OAI.PiExponent.logarithmic_differential_of_polynomialTangent",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a92153e4d96e0f20f3f15b3dabe4789fd947dc18d77fb41629ee3ea95d78c206",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential:2708",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential:2708"
    },
    {
      sourceName := "OAI.PiExponent.mem_natWeightedSimplex",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c248602e530a7a7cf17cd37a86b9ae269d2ec7080d7bf5bd08122d3d6425b6d1",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:392",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:392"
    },
    {
      sourceName := "OAI.PiExponent.mem_realWeightedSimplex",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a93601ce7592a04a476f1b4c6010fa5b88e7c8ad4b50d54c0a05b54cc3a64342",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:6916",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:6916"
    },
    {
      sourceName := "OAI.PiExponent.mem_residueRectangle",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4495ab61bec324275139968b21c6899739e2f2643458557d93b04202306e261c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:1153",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:1153"
    },
    {
      sourceName := "OAI.PiExponent.mem_strictWeightedSimplex",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "11a56cef67214cf0ea1dc56d44457b1f13bf47939e83de5cf63c18ad0446db8d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:7589",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:7589"
    },
    {
      sourceName := "OAI.PiExponent.mem_unweightedSimplex",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f7ba98b1b9326590a091f40cfbb36e0b9173df80973b96c35decac1b5aa471b8",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted:327",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted:327"
    },
    {
      sourceName := "OAI.PiExponent.natWeightedSimplex",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6cf5e05f7c860ed80436703c40b898102a2e1dba2f2433a908126bf9142dda36",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:198",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:198"
    },
    {
      sourceName := "OAI.PiExponent.natWeightedSimplex_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "52a189e57abdd32af6b5ea584669ef686682f12e5e4746d6fb1af0939edf3805",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:4710",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:4710"
    },
    {
      sourceName := "OAI.PiExponent.no_logarithmic_differential_over_intermediateField",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.AlgebraicLogarithmicObstruction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ab9c0b26de67c193f5338d03384f49f30be24f755d786a2c3b6a887eb6b54b68",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.AlgebraicLogarithmicObstruction:4739",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.AlgebraicLogarithmicObstruction:4739"
    },
    {
      sourceName := "OAI.PiExponent.norm_center_error_exp",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ApproximationCenters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b64c31d127bb1c79ab36ef84cb50d48bb45e0d3f70061373b1480074dda94b5c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ApproximationCenters:2617",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ApproximationCenters:2617"
    },
    {
      sourceName := "OAI.PiExponent.norm_center_error_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ApproximationCenters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b50c5347f03c0180396b2a651d16e5a24d1875940262f5a97ec6df6cdd791bf1",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ApproximationCenters:1336",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ApproximationCenters:1336"
    },
    {
      sourceName := "OAI.PiExponent.norm_period_error",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ApproximationCenters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "26ff22adb75aa0cf9cbd93476911ee9c25702e677db7e02da23361c7e218900e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ApproximationCenters:889",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ApproximationCenters:889"
    },
    {
      sourceName := "OAI.PiExponent.normalBasis_complement_algebraicIndependent",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceBasis",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7ad4f9d3c7826186ddeb72286231da0d3de969f398d6554dc08ff22df3b9d3ff",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceBasis:7432",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceBasis:7432"
    },
    {
      sourceName := "OAI.PiExponent.normalBasis_complement_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceBasis",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d3302a5c2417792174b375b5c8dbab04f0a9d350a8dd25c99b04e9607de4a857",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceBasis:1890",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceBasis:1890"
    },
    {
      sourceName := "OAI.PiExponent.normalBasis_complement_isAlgebraic",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceBasis",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4e088101cc2c89d91c51fdd6891a776997819ab6b9fcd0eaff5e4f8e78c80561",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceBasis:9550",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceBasis:9550"
    },
    {
      sourceName := "OAI.PiExponent.normalBasis_complement_isTranscendenceBasis",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceBasis",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b10302124fa6a56375a436c7575e52434b70a73dfd868dd628ad67dd180e82c2",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceBasis:11514",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceBasis:11514"
    },
    {
      sourceName := "OAI.PiExponent.normalBasis_complement_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceBasis",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1cddb25916c6c73c425390c277d38f74fe43806aebcb639198ec976e9d53a238",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceBasis:354",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceBasis:354"
    },
    {
      sourceName := "OAI.PiExponent.normalizedLogWeights",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SuccessiveApproximations",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1beb69af48ddad770d723b3deecdb35bbe39e5b0d33fcb3c3feb11243f60a5f1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SuccessiveApproximations:3411",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SuccessiveApproximations:3411"
    },
    {
      sourceName := "OAI.PiExponent.normalizedLogWeights_succ",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SuccessiveApproximations",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fd09a0be5134564117bacd55983a356da3cdf8e294753c8fe1cce5cfcd5d5a15",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SuccessiveApproximations:3651",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SuccessiveApproximations:3651"
    },
    {
      sourceName := "OAI.PiExponent.normalized_products_separated",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparationProducts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a7b94f884578c6bf9939399145b35b091827395a4bad85a6b33371c75b768fdc",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparationProducts:1246",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparationProducts:1246"
    },
    {
      sourceName := "OAI.PiExponent.pderiv_totalDegree_lt_of_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceBasis",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "73138820002f29d2689129fcccde6cbb5ac31a66196e75844d1b6996eb23f629",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceBasis:4867",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceBasis:4867"
    },
    {
      sourceName := "OAI.PiExponent.piEventualLowerBound_of_globalInterpolation",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InterpolationConsequence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "12daf679b1ca6ab8d8c5a85675e8b9ed6eb91be07b71336425b027a096bf65d8",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InterpolationConsequence:227",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InterpolationConsequence:227"
    },
    {
      sourceName := "OAI.PiExponent.pi_eventual_lower_bound",
      expectedModule := "OAI.NumberTheory.PiExponent.Main",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "df072f70c8921491aec529fa197854c86afbb3421d894ed901460a2312b442ea",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Main:193",
      commandUnit := "OAI.NumberTheory.PiExponent.Main:193"
    },
    {
      sourceName := "OAI.PiExponent.polynomialGradeZeroEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PolynomialProjectiveStructure",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8c0d255c088f7319e05e05a2cac526e533182275fa16ef6157847cf473101d5a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PolynomialProjectiveStructure:294",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PolynomialProjectiveStructure:294"
    },
    {
      sourceName := "OAI.PiExponent.polynomialGradient_mul",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceBasis",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3bbcda94b06e79dc4ac8b8714e0c6a84a505cd7a76748cffb3d6005862ac5226",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceBasis:3453",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceBasis:3453"
    },
    {
      sourceName := "OAI.PiExponent.polynomialGradient_rename",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceBasis",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "95d43408cd8cd2ea9b790d9c926e007794be4639a508fc9a8ba075c33e1b0359",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceBasis:3913",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceBasis:3913"
    },
    {
      sourceName := "OAI.PiExponent.polynomialJacobian",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b7dfd1fff6ceddacc7d3c4aac67ca24ad042d6b36ec99432f278884d04b84b9f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential:1043",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential:1043"
    },
    {
      sourceName := "OAI.PiExponent.polynomialNormal_mkQ_ne_zero_of_kernel",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GenericNormalRigidity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9779d325a5724c69599528876dd15df50d418eee337e2164d3e3d6fb747a6e20",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GenericNormalRigidity:270",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GenericNormalRigidity:270"
    },
    {
      sourceName := "OAI.PiExponent.polynomialNormal_span",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dedc422630f7469979881d3b5c822e73ea8aeea3fc47e1f3d6e21df8129893a6",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential:3866",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential:3866"
    },
    {
      sourceName := "OAI.PiExponent.polynomialOfCoefficients",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.AuxiliaryPolynomial",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7a786b6e9b5cafd707e4fe5c87d0b860bf5b49baee6bca6cd0bc0a0bb2e72209",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.AuxiliaryPolynomial:291",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.AuxiliaryPolynomial:291"
    },
    {
      sourceName := "OAI.PiExponent.polynomialOfCoefficients_coeff",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.AuxiliaryPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bae3a5f466ffd0f15808644c360df089963d0692305eaafcaeb9f5663b0a2316",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.AuxiliaryPolynomial:1026",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.AuxiliaryPolynomial:1026"
    },
    {
      sourceName := "OAI.PiExponent.polynomialOfCoefficients_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.AuxiliaryPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3de733ab12c5e636b593e4ab87c1d9a7f0a4b91d407298521022d371df9edaf0",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.AuxiliaryPolynomial:1787",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.AuxiliaryPolynomial:1787"
    },
    {
      sourceName := "OAI.PiExponent.polynomialOfCoefficients_support",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.AuxiliaryPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "65df1211a3c0be631eff63e694cda5ff118c00f9e04139fcdc26705564be8065",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.AuxiliaryPolynomial:2134",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.AuxiliaryPolynomial:2134"
    },
    {
      sourceName := "OAI.PiExponent.polynomialOfCoefficients_weighted",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.AuxiliaryPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "30243c3c5a6046538612dcd64d2548e2c41c1306c707ea9124a2f6d8e0ca7e71",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.AuxiliaryPolynomial:2907",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.AuxiliaryPolynomial:2907"
    },
    {
      sourceName := "OAI.PiExponent.polynomialProjectiveProjection",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PolynomialProjectiveStructure",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1e97d25e1aca15d48a78659acd564cd1cb611fd5d83fa3ea6a1e20be51370f83",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PolynomialProjectiveStructure:820",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PolynomialProjectiveStructure:820"
    },
    {
      sourceName := "OAI.PiExponent.polynomialProjectiveProjection_proper",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PolynomialProjectiveStructure",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "da6ea0c365ea94c173796a87b3049ebf7ac3c21bc843e4b7cecd10a943f37870",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PolynomialProjectiveStructure:1464",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PolynomialProjectiveStructure:1464"
    },
    {
      sourceName := "OAI.PiExponent.polynomialTangent",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5a3db68c0ffadb71289c26bf0f6e532350794100aa8b18769b52d1be6fd730fc",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential:1364",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential:1364"
    },
    {
      sourceName := "OAI.PiExponent.polynomial_logarithmic_equation_impossible",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicObstruction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2f795dc2cdbe8ba0753f33f01fea5cf5a000bf9d52d3c1d131a1ae08935c0b27",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicObstruction:813",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogarithmicObstruction:813"
    },
    {
      sourceName := "OAI.PiExponent.positive_rational_weights_common_denominator",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexRationalWeights",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ad2abb5e5933fbacb65261beb26f50b64a167c49566e3c504072588984c38521",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexRationalWeights:119",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexRationalWeights:119"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_028.jsonl"
