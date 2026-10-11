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
      sourceName := "OAI.PiExponent.WeightedSliceDegree.enumeratedSliceMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3ff12dc9ca0b977a5200e3434b009b70e1710b00d2893d88c4da20528dd94220",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:7687"
    },
    {
      sourceName := "OAI.PiExponent.WeightedSliceDegree.sliceMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f7c34deff4197e19a4dc504251cb8c7e18198281c161a8c1c2c13726e5dc91d2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:4618"
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
      sourceName := "OAI.PiExponent.approximatePeriod",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ApproximationCenters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e9a8432b0a205dd35eca65c13179fba7cc8fa5e19c96f527356ca67136d20ad5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ApproximationCenters",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ApproximationCenters:94"
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
      sourceName := "OAI.PiExponent.dimensionK",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f3045b67fedd17de5cd0ff4b327d1ee153229e76dd52c9aae93545eb0da21145",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:338"
    },
    {
      sourceName := "OAI.PiExponent.dimensionV",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "80bfe228db13db7ba55f64588ebdbe776aa94e9632cc48e093bee9d988109a45",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:460"
    },
    {
      sourceName := "OAI.PiExponent.dimensionW",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "177680d0c0bed82b9a91b92f44da3ef4cf2d6bcae1f6cade40b10918b8fc6b99",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:400"
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
      sourceName := "OAI.PiExponent.extendDerivation",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.AlgebraicLogarithmicObstruction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9b24d6dae54a67ef00f35a09ec65489a31b05b684844db3eb81cdda348dfd516",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.AlgebraicLogarithmicObstruction",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.AlgebraicLogarithmicObstruction:438"
    },
    {
      sourceName := "OAI.PiExponent.extendModuleDerivation",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8f8b1b2c0cac1c15e6ee209f6faa8b1c4bbd4e14ea18b75ac2584578dc2a7a71",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent:369"
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
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalAuxiliaryJet",
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
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FromSpecStalkLocalIso",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FromSpecStalkLocalIso:2410"
    },
    {
      sourceName := "OAI.PiExponent.fromSpecStalk_stalkMap_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FromSpecStalkLocalIso",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "31bb02190355e7c404945e7b01fb2e5ca529f979d6157db612162cd87cc27fa6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FromSpecStalkLocalIso",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FromSpecStalkLocalIso:1532"
    },
    {
      sourceName := "OAI.PiExponent.genericCoordinateNormals",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GenericFibreRigidity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e7fa6251a1ee7fff00708ee8d7754789ee03b37ced5aaf8fc7a369afe8c060a5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GenericFibreRigidity",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GenericFibreRigidity:414"
    },
    {
      sourceName := "OAI.PiExponent.gradedMap_homogeneous_lift",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SurjectiveGradedMap",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b5c1d818104c1558d13e8de36ae0b71e85b6759fa2fd74d55833dc90327209bd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SurjectiveGradedMap",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SurjectiveGradedMap:399"
    },
    {
      sourceName := "OAI.PiExponent.gradedMap_irrelevant_le_map",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SurjectiveGradedMap",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "72dc35ee9c1765d275b019e34d285d1f0d1d7b90272eadf994aad8c2e22db08e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SurjectiveGradedMap",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SurjectiveGradedMap:740"
    },
    {
      sourceName := "OAI.PiExponent.holomorphicError",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.Collision",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2faf0d0fcc7fc01cade36a60aff045c007cd4abcfc2a372e93365e157c2ebf22",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.Collision",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.Collision:286"
    },
    {
      sourceName := "OAI.PiExponent.homogeneousAway_map_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SurjectiveGradedMap",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "979e1651e206eed96d46164a3572520779266fd7724322aa512bbf2e93d63ab2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SurjectiveGradedMap",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SurjectiveGradedMap:1077"
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
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PolynomialProjectiveStructure",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PolynomialProjectiveStructure:1257"
    },
    {
      sourceName := "OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_oAI",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PolynomialProjectiveStructure",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5ec86caff9b67611f714232e099235b2edd38ed6ac2bcdee39d1957f9bffe993",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PolynomialProjectiveStructure",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PolynomialProjectiveStructure:1051"
    },
    {
      sourceName := "OAI.PiExponent.interpolationSeparationConstant",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4f5a507b47c8d9b0742c774a1b9da1545a4d1829a09979bbdad51ebc5971c23e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:552"
    },
    {
      sourceName := "OAI.PiExponent.literalJetSubstitution",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AuxiliaryJetMap",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d2c06faed246519f027612a714df08b2caaca18672f98eddccf85162a57ccf43",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AuxiliaryJetMap",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AuxiliaryJetMap:161"
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
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ApproximationCenters",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ApproximationCenters:809"
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
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:6916"
    },
    {
      sourceName := "OAI.PiExponent.mem_strictWeightedSimplex",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "11a56cef67214cf0ea1dc56d44457b1f13bf47939e83de5cf63c18ad0446db8d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:7589"
    },
    {
      sourceName := "OAI.PiExponent.natWeightedSimplex",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6cf5e05f7c860ed80436703c40b898102a2e1dba2f2433a908126bf9142dda36",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:198"
    },
    {
      sourceName := "OAI.PiExponent.normalizedLogWeights",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SuccessiveApproximations",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1beb69af48ddad770d723b3deecdb35bbe39e5b0d33fcb3c3feb11243f60a5f1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SuccessiveApproximations",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SuccessiveApproximations:3411"
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
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PolynomialProjectiveStructure",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PolynomialProjectiveStructure:294"
    },
    {
      sourceName := "OAI.PiExponent.polynomialJacobian",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b7dfd1fff6ceddacc7d3c4aac67ca24ad042d6b36ec99432f278884d04b84b9f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential",
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
      sourceName := "OAI.PiExponent.polynomialOfCoefficients",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.AuxiliaryPolynomial",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7a786b6e9b5cafd707e4fe5c87d0b860bf5b49baee6bca6cd0bc0a0bb2e72209",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.AuxiliaryPolynomial",
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
      sourceName := "OAI.PiExponent.polynomialProjectiveProjection",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PolynomialProjectiveStructure",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1e97d25e1aca15d48a78659acd564cd1cb611fd5d83fa3ea6a1e20be51370f83",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PolynomialProjectiveStructure",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PolynomialProjectiveStructure:820"
    },
    {
      sourceName := "OAI.PiExponent.polynomialProjectiveProjection_proper",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PolynomialProjectiveStructure",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "da6ea0c365ea94c173796a87b3049ebf7ac3c21bc843e4b7cecd10a943f37870",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PolynomialProjectiveStructure",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PolynomialProjectiveStructure:1464"
    },
    {
      sourceName := "OAI.PiExponent.polynomialTangent",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5a3db68c0ffadb71289c26bf0f6e532350794100aa8b18769b52d1be6fd730fc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential:1364"
    },
    {
      sourceName := "OAI.PiExponent.positive_rational_weights_common_denominator",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexRationalWeights",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ad2abb5e5933fbacb65261beb26f50b64a167c49566e3c504072588984c38521",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexRationalWeights",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexRationalWeights:119"
    },
    {
      sourceName := "OAI.PiExponent.primeLocalDirectional",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f8b110f79e5faa72c4e61716a0b887f050ce2da13a9eb666d6a745e2ba45b135",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent:4615"
    },
    {
      sourceName := "OAI.PiExponent.primeLocalPartial",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ed0f8f6fcef2901576ed591c4b0b656c9b26fa6aa9ac9444a354f69da13f81c0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent:1827"
    },
    {
      sourceName := "OAI.PiExponent.primeNormalPairing",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c258ce972788f4243edee424ac750917cd8b368302b0c6949fbd8e0f1654642b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent:2978"
    },
    {
      sourceName := "OAI.PiExponent.primePartialNormal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4c942cf84c0fd8c028ea2056dde8aeeac2af18d0164cdde697c3263ca421993d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent:2750"
    },
    {
      sourceName := "OAI.PiExponent.primePolynomialCotangent",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c57af2ebf262fcba389dda96d530ba01d4e14b68a6c52ce2760b7ad6d3972413",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent:3297"
    },
    {
      sourceName := "OAI.PiExponent.primeResidueMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "118697b7b6ab1b97d205706562044b5ebb7fb6621b14dfb4d3e5e0836bed8533",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent:1693"
    },
    {
      sourceName := "OAI.PiExponent.prime_cotangent_evaluation_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bddc82c08874916276573fe9004aa4fad23a5f045d711c94bdb6fdf37d278be0",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent:6240",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent:6240"
    },
    {
      sourceName := "OAI.PiExponent.prime_frame_rectangular_length_lower",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeFrameMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "52014b1a0052858fd8b625f6d71c8762146478aea617d0a188702cdbb78b3d53",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeFrameMultiplicity:415",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeFrameMultiplicity:415"
    },
    {
      sourceName := "OAI.PiExponent.prime_rectangular_mapCotangent_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PrimeTaylorCotangent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2b465d4e38620e70455da81f48423ef3cbf4d5957c300779689b604032bbbf64",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PrimeTaylorCotangent:1120",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PrimeTaylorCotangent:1120"
    },
    {
      sourceName := "OAI.PiExponent.projectiveGenericPoint",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveDenseChart",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "892e305475e2c616b62c3f617047efbf014ea1b999a25a8603424ac6787ecc34",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveDenseChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveDenseChart:356"
    },
    {
      sourceName := "OAI.PiExponent.ratFuncDerivative",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.AlgebraicLogarithmicObstruction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a2f5aa5c7be533cf2469f856b386850adfef183ab701bb931f73853729c96846",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.AlgebraicLogarithmicObstruction",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.AlgebraicLogarithmicObstruction:1322"
    },
    {
      sourceName := "OAI.PiExponent.realWeightedSimplex",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "350f9e7abdb193382b0ec5588da613ef47e9087e3d1e7b88292d3f1da317619a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:6443"
    },
    {
      sourceName := "OAI.PiExponent.rectangularCutoff",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "680fa678c00673d3b7023b5a008f7469e98cc0e142888445440d6ce7b4012226",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume:122"
    },
    {
      sourceName := "OAI.PiExponent.rectangularCutoff_weight_lt",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5323b915bbf957691b4b43cd0d09437043213775faac40d1f109be9827b3d6a2",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume:2104",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume:2104"
    },
    {
      sourceName := "OAI.PiExponent.residueRectangle",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e95203858fdc52a3d7d2d4cb1550fdd0dd580e94d7c480d13c886160d33176c7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:1021"
    },
    {
      sourceName := "OAI.PiExponent.simplex_count_lower_sandwich",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "32550919c6a092b470e3882ead26d4db3780d662f8eeea7df5bbc198c495ca0a",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:1506",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:1506"
    },
    {
      sourceName := "OAI.PiExponent.simplex_count_upper_sandwich",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3be5d197c182f42e1ef1b28687c97b8527ecfe640d86659f6b56dfa96d9e9f44",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:2826",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:2826"
    },
    {
      sourceName := "OAI.PiExponent.specMap_stalkMap_isIso_of_isLocalization",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FromSpecStalkLocalIso",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "72c7cd7171c21f3254e0f545ffd39be9452e5c6f704b803c734b006daed74a38",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FromSpecStalkLocalIso",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FromSpecStalkLocalIso:163"
    },
    {
      sourceName := "OAI.PiExponent.strictWeightedSimplex",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "509ba2c89601bf4b66d6dc9eb6f9989d284493cda0e870d16af28d904f07addf",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:6702"
    },
    {
      sourceName := "OAI.PiExponent.subringGrade",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedSubring",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8016e0fac12384c6d895adc8cd9a66db58504d68d3a90779bab2ddac8b916bb3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedSubring",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedSubring:250"
    },
    {
      sourceName := "OAI.PiExponent.subringGrade_independent",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedSubring",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2f48b7e3854372fd2982a949a96264ca31afd45303a9782ac11b560614734645",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedSubring",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedSubring:359"
    },
    {
      sourceName := "OAI.PiExponent.subringGrade_spans",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedSubring",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "122c750d088ce1c039ee1e90c0f190a63f72f67835d6c03a643ade86091f7e17",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedSubring",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedSubring:955"
    },
    {
      sourceName := "OAI.PiExponent.subringGradedAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedSubring",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "037bdae973f27e26a62eb29c6eed779e9a7be3eda1f41c5926a36bea80f32739",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedSubring",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedSubring:1617"
    },
    {
      sourceName := "OAI.PiExponent.tendsto_card_natWeightedSimplex",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e76a614393c0b41d06d2b460c406de4461fc3b9192f368e1e67781009882b5b8",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:5000",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:5000"
    },
    {
      sourceName := "OAI.PiExponent.tendsto_card_strictWeightedSimplex_scaled",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9bcbdf73c502b767e770d56544588cf0a1eb5aa8d8c8d9b688430f08199a8a0f",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:9837",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting:9837"
    },
    {
      sourceName := "OAI.PiExponent.tendsto_choose_add_normalized",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f3154e730a3708ea4887f24837dff71fb9b443a979db28c15dfaa5f549aec9d5",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted:2924",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted:2924"
    },
    {
      sourceName := "OAI.PiExponent.tendsto_log_div_of_normalized_pow",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexLog",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e765cae5ae5ee9a5ab96fcc46444d29f413cc25989919d685dfe168b04e954c1",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexLog:157",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexLog:157"
    },
    {
      sourceName := "OAI.PiExponent.tendsto_natFloor_affine_div",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexFloor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a645952e449e46d2e1bf4b93d68de9a0d9e8329301bb6a5661f89dffd85f99c6",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexFloor:372",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexFloor:372"
    },
    {
      sourceName := "OAI.PiExponent.translationTermCount",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.TranslationCountLimit",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0c7896882e41a877f297b07b7f4362dccc7f0e1dd4a11370a28470c3e84f582c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.TranslationCountLimit",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.TranslationCountLimit:187"
    },
    {
      sourceName := "OAI.PiExponent.unweightedSimplex",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "038ab30ff7c2537f5dbb153ad137d4922b0bcdd3e92eaaa581ef2a4303a968ab",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted:168"
    },
    {
      sourceName := "OAI.PiExponent.weightErrorCoefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "322c4bc9061dd34804a634f9cd9814ce4f61a73741c1d6b5beef10ae5177516f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:939"
    },
    {
      sourceName := "OAI.PiExponentApprox.FramePolynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d88fadc83b3ac8ead76e1aff1472aa2752c2a572d8d01766f330be8a2af8e327",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame:251"
    },
    {
      sourceName := "OAI.PiExponentApprox.HasWeightedDegreeLE",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3362a18e5d51e6ddf686b09a93ebf6931988c7b35cf5775efb34c0c353216e69",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:303"
    },
    {
      sourceName := "OAI.PiExponentApprox.SeparatedWeightGrowth",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3f4c737c6a3a7b54f4c5083cb137eda92fa06e4fc75472c942ce6546c838117e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparation",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparation:4666"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.RectIndex",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a11d469125951e4afc5cceacb9d3bc4c2de65365624336a194da526e3cb5f06e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:569"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.RectangularRing",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "57463454d27842b808868170d74afbd08d84628135494cd0db4116703aaa3362",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent:353"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.firstCoeff_mul",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7e7db475d204270f793c1f28cad96b6cfcb0fa9e4e0b2d08e20328aa110321bb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent:1874"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.localizedTaylorMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f77d2d08e8faa9ee411d58bb5b6ee0b439a6d65cdf5ef54d9eee3fe8acb886d4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:15304"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.localizedTaylorMap_linearCoefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6ce1ae6755960acd216b07bc3cac2d752d4bd67ebec165254fbdbb7bcd2bd245",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:17393",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:17393"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectIndexEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0fc9e12260154a314e9fbb4b477ffe79e36873d6e1023b438a591b0df5037962",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:3559"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectIndexFintype",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d29596ae273761760216c7b1a3bef23f63d8695f43c3bac08d35b982767eb278",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:3938"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularAugmentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "25d517ee405bdc8fd8b16503c24b6e2200919ea807e6a5f83bd1acfec2d31678",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:4716"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularAugmentationIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4a0734f4f1025e7647e0299dd3fd36c7a6c84e2832a27143a5e0d8c7733fef16",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent:632"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularAugmentation_ker_pow",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c01eb3876d4e5e0021bd5ba0f5e17c06578efd2139e57035ac826e56955232c3",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:7443",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:7443"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularCotangentFirstCoefficients",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f70865191c072535e1d84f12528ee0410a638e5be800bfb0900c1e7cd553818b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent:7233"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularFirstCoefficients",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d4c424984d2c131b064247fe5b3db6beacaf7d49f38d687da68a9d8b126cf58d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent:1138"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularFirstCoefficients_mk",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e99d93ceab40800bc641b57e41432079f48781dcbc7d0d354736c6cf34bac561",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent:1572"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6cfd8012a9c05af95d1c36e0a3626bbc4aaea99ff643e2780c208057a1c77e0f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:646"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularIdealFirstCoefficients",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6916cb44a2fb22bf10ad962403e0fa32425a54573b9d768008497331175e00cb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent:5960"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularIdealFirstCoefficients_mul",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "86b5724ea1e188a124ed570a9d6b97758b82b3323f7d21079f146ef7e18b6a8b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent:6247"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularPacket",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0f8bd9258536dd7381366bc314b0ac1a9fb7736927fbe857520af9d3a535879d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:1318"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularPacket_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2aaa7fce012ed96304f97af5f23142ac528dd16561feda235db0ca2941da7a10",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:1552"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularPositive",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d92f0a6fbba59063eb4895b0a13f8b3ca5a970af3d8e3f0406b4295c636ab4a7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent:453"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularQuotientCoefficients",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eee503db8eb88e83c05a16b094c61b35a7720d64a553a5b8b88938e31fe4f9a9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:2029"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularQuotientCoefficients_bijective",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a3099c4f206bb91a730ea20fc9c8b328740c3acf5d54cd0d07a0aa15d443d56c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:2661"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularQuotientEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d5979a3a2293c8b3b919b6cf7aaa449b2b071e97bea0880cc30ee00c04c121a7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:3303"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularQuotientFinite",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "607c9cd75a5ca4ceeb90926f2a1c3339cdb6dbd4c6675d552a3033f7fa0823fc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:4259"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangularTaylorAlgHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "81943523125ac1576101207d3d013839336273385883c7c0514076aed93ebecd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:12595"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.rectangular_quotient_length_le_of_residue_cotangent",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "312094aa320541b50e0a3123864ac7842066da4b191ae26b8969b256e14ebef0",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:10780",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity:10780"
    },
    {
      sourceName := "OAI.PiExponentApprox.TransverseMultiplicity.unitRectIndex",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7b9dd5ebb28fc990edf4ad5287d0e40aa55dec3c072cfc5a506f0cbd47b2ce01",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.RectangularCotangent:833"
    },
    {
      sourceName := "OAI.PiExponentApprox.exists_persistent_frame_component",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bdef4aa840c145e319f4beaa18b57b75ec04246cb3383b9ece5d86b8c9e83b42",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContact:5640",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContact:5640"
    },
    {
      sourceName := "OAI.PiExponentApprox.frameDerivativeIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContact",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bb0e669215647ab637117c0a336dc66d61136881ddde9168e633473910ad70f8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContact",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContact:1006"
    },
    {
      sourceName := "OAI.PiExponentApprox.frameWordCost",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContact",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "156b9c04d76718559be42fc6f000cfaf6286f41e2dec022ea6ef082f4d66e22a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContact",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContact:279"
    },
    {
      sourceName := "OAI.PiExponentApprox.geometricDegreeWeight",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d43756fb2019c569b0f5f3df6970576af9c2e129ab564ce6619e03ac407d3e0a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparation",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparation:328"
    },
    {
      sourceName := "OAI.PiExponentApprox.geometricJetWeight",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6a2c4b6969e64d885af0d2ae263876fb387e967666327e00b75d6dbd9127e01f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparation",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparation:434"
    },
    {
      sourceName := "OAI.PiExponentApprox.geometric_weight_products_of_normalized",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2f36f0f720e37ae7cf447a406532e94bac9cfc14e212450a7ef33bcbf1a02d1b",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparation:1005",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparation:1005"
    },
    {
      sourceName := "OAI.PiExponentApprox.logarithmicDerivation",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fce7b3723cd7851ac8c95509a236c0370596ceb10d3d35eceb636b1d4ccccd2d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame:321"
    },
    {
      sourceName := "OAI.PiExponentApprox.monomialWeight",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "01f36c75bdf6fe96787cba2023e52f0479a6f634b366d2f13e44d10c1c7da5cc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:174"
    },
    {
      sourceName := "OAI.PiExponentApprox.polynomialDerivativeCore",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContact",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3a7fb658fffb8b658a5f60faa03b28520e53957b592838d8e4f0ec397980f329",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContact",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContact:2162"
    },
    {
      sourceName := "OAI.PiExponentApprox.polynomialFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4fce4c5386239239ef3c8e18c9f6fe72406fc4ce79b0b88769ea2d9d88f9ca1f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame:601"
    },
    {
      sourceName := "OAI.PiExponentApprox.polynomialFrameWord",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fb40371d38df407c3065224bf9705ad4f52f6d2e088eb1274cadbb4f084d67d7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame:5814"
    },
    {
      sourceName := "OAI.PiExponentApprox.weightSeparationFactor",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "63133c54b6583c5e64b866394545b1371ecfcfffa89c6007ba6fc620405e9e92",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparation",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightSeparation:551"
    },
    {
      sourceName := "OAI.PiExponentJets.EndomorphismEuler.cokernelMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4caa80bc5c33ad12efce38b3b11b66df6ebde8c0bf825b9fbde85fc3d8e0b56a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity:1187"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_020.jsonl"
