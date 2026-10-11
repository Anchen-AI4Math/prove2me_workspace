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
      sourceName := "OAI.PiExponentJets.EndomorphismEuler.connecting",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "66420eac8e08ef52140978405809aa41d3b7747d50650ec301da787e7b6edf8d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity:4527"
    },
    {
      sourceName := "OAI.PiExponentJets.EndomorphismEuler.endomorphism_euler_cross_add",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d031776d2e49ee7d5cfdd3152377a6bdee4372adba812e031b05b98e30741ced",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity:9175",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity:9175"
    },
    {
      sourceName := "OAI.PiExponentJets.EndomorphismEuler.kernelMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bade52a78e90330358b2719ff63f748bdcd72833c8f84c20362f510aae250087",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity:311"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.CoefficientClosedLocal",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a847089723690bd29c586290e92dc6cc7d762c87155be931f3c380ca380c512b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv:1243"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.LocalPolynomialResidue",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialLocalResidueResolution",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1ac3b17b5b6aeea966107f2104f20bf30f7753b53beedc40ee2c2c106d1ac3f2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialLocalResidueResolution",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialLocalResidueResolution:2562"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.RemainingCoordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "08971ec9b03350c8329e439a8e8a6b4462e160d4c556ece18daad15539018e38",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting:454"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.SplitCoefficientField",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f455f1e38c8560569bdd9c95cd0bd284f5c9500094af39e9945cad0e216818ab",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint:566"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.SplitLocalRing",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2d7a07dc363f0ba59a828a9aa78d7b51f8642949238453910347254fcfeaba17",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint:478"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.SplitResidue",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c8a1dfc2dfb2e2dc2ac48db4aa1744937c07df968c7053a21a968c1e874a0183",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint:527"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.algebraic_field_kernel_isMaximal",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoefficientLocalizationMaximal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5d82ce83d54b9e68b8cdd3c03ca763e2a6184c09784dd3239c5992d93ba5db93",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoefficientLocalizationMaximal",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoefficientLocalizationMaximal:471"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.closedLocal_isLocalizationAtOriginal",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8425e86e61c357f7e06caf5390b2e37265ea1e18dd24bbd13e17359ca51657e0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv:1338"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.closedPointEvaluation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c9bc883fee017890802dc5184e608c2c0e03ee2b0a2f8022ece691167a997287",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint:1745"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.closedPointEvaluationRingHom",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fdd0a59fe280b1695e8f301910cd66169c49610a93442b0344f903f1af4969d5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint:2138"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.closedPointEvaluation_coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9278936a66d6d06fcb1a15a036b7a7331c30e277190869272a766ab33dd6acb6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint:2674"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.closedPointEvaluation_kernel_maximal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "351aef086fdddc99a14ef4f2d88f18642c199f862356631face586f421f289ac",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint:2366"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.closedPointEvaluation_original",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitClosedPointCompatibility",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cd492d20a2cb882cfc8ac475c3454966a62e1b8553a27524c682c5725ed22346",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitClosedPointCompatibility",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitClosedPointCompatibility:351"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.closedPolynomialIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ffe4ac214a1d8173b58da81be7270399dac35a2b46b4c17442cfbade18e889f4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv:2588"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.closedPolynomialIdeal_isMaximal",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fc7c7cae920a9812af506bfb105b51c6bb4e6608b43e94a2ed23fba22582c650",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv:2808"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.coefficientClosedPoint",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ff33796b22b1ce938de553f32f05c0031c675dd01ba7307e581297ffbb9f3158",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv:499"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.coefficientClosedPoint_comap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitClosedPointCompatibility",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aedd016aa93c9bc7eab52d33be77d3486886fd1835077a333987a62041924a83",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitClosedPointCompatibility",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitClosedPointCompatibility:3603"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.coefficientClosedPoint_isMaximal",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f2e5f1faa2a68398674c9a66e860169633abdec828c3452a43aa6717426dadf6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv:767"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.coordinateBasisClosedPointEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "42b15c24b0bb9a9d28223ffce5e70bff157dc33a08f5eeef7d2388ae99bd06ce",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting:3172"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.coordinateBasisLocalEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b439945a319e67599676fdcb4bb2b3feb22a938360c04491b7554f22954b2aeb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting:2950"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.coordinateBasisRenaming",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "65cbfe9f35d4f5d2c4e15d01142e1d48c15a4e3cc9c0ee351aa673762f14b432",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting:1094"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.coordinateIndexSplitting",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5ee0c86f6a04f6b6346be553bbdda53175335e41c377e21cefb1d0d4f4b72774",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting:520"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.coordinateIndexSplitting_inr",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0fe07e50460061460258acba5f85587af3c6cc4a020b31c795b4494a7110c7c5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting:770"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.coordinateIndexSplitting_symm_selected",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4b286bfd7024dcfa71b76f10a12cb2393830cbce601ab67501926122b1856e20",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting:888"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.coordinateSplitPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "165a7816840fba579c2edc8b7b2de44cd36a3e144a57d904eebf6320a1f7ec92",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting:1618"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.coordinateSplitPrime_basis",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "433291f6092099e57234d0432e5809eb5102be260cc9481f0781fae0ef0b05b5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateBasisSplitting:1701"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.exists_regularParameters_actual_height",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialLocalRegularParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "740498f8df81f23f094dbfabda5b3fec627969c9db7f3a97663e0a9d76c38f21",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialLocalRegularParameters:436",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialLocalRegularParameters:436"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.originalLocalCoefficientLocalEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b925e9fe738fbd32166ae83e3836a3f2d251a89d2bec5122100a219a94e93a4e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv:2279"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.polynomialPrimeClosedPointEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d10185d32c051fd85d41934230c680ce478d952cae286040c598b0d7ad1ce65f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeClosedPointEquiv:3177"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueAlgEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeResidueAlgebraEquiv",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a3fa0b13e0944ceb621ac6031db4c7561fd0a089a32ffcd9a363d1a5a86bdfd0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeResidueAlgebraEquiv",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeResidueAlgebraEquiv:1441"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueAlgEquiv_algebraMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeResidueAlgebraEquiv",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2fbad1468fe3cb344af5db2bc826207d9e3329e99e19e0a6e12ca26354bb199d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeResidueAlgebraEquiv",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeResidueAlgebraEquiv:1866"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueAlgEquiv_transcendenceBasis",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeResidueAlgebraEquiv",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fcb862c7d9185294214814eaa22680bbaa8bb676b1b95e80dea2fb23f760afa5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeResidueAlgebraEquiv",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeResidueAlgebraEquiv:2095"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeResidueAlgebraEquiv",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1c81f0e56f0dbf17f9e140881f8649b226f01f2a3b1c6b192904c0843a71733c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeResidueAlgebraEquiv",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeResidueAlgebraEquiv:454"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueRingEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeResidueAlgebraEquiv",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6c8d84d9efca2ecd1de51f2bcf05fc1cf995e7d0ccfe6d78ae6afa97d2f36a74",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeResidueAlgebraEquiv",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeResidueAlgebraEquiv:557"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueRingEquiv_algebraMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeResidueAlgebraEquiv",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "05b86e7702b843d9a7c2eb516fc8dd79b62682e2df01fb13434cf70ffb89e0de",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeResidueAlgebraEquiv",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeResidueAlgebraEquiv:750"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.rationalResidueEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.RationalResidueCoefficientField",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9c0d7578b5783b8340ca7665b0b3faeac5fdeb4ef2a899239d1ba989e835cfd5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.RationalResidueCoefficientField",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.RationalResidueCoefficientField:482"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.rationalResidueEquiv_polynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.RationalResidueCoefficientField",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b4bf8f05353820bf4c6cd5e379cc051fba1f18b95670bb93398d7acb0707dd32",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.RationalResidueCoefficientField",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.RationalResidueCoefficientField:692"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.residueCoordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialLocalResidueResolution",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "db0576c00e1bbadc20f8d9f1763322d9feb54f01be4dd961a2b00d655d733c41",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialLocalResidueResolution",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialLocalResidueResolution:2743"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.splitCoefficientResidueAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f810edb698d83c572c43fcbfd0c53f85b987d6573a4d9c19df49fe360e49fdcb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint:1005"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.splitLocalBeta",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "561d949a870cd02b3c641b050e2f0d4f6981a8bc36a5755de6f0c747135b2a07",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint:634"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.splitResidueBeta",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "948e1535449624e4e385ca62808ec91d327db243d9997e6f0658bd5e20ca2526",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint:794"
    },
    {
      sourceName := "OAI.PiExponentJets.PolynomialLocalResidueResolution.splitResidue_algebraic",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5838da1488e0134c150299eef258a4f6463e60fb3f5efa14c5fdb1cca6c71bcf",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SplitCoordinateClosedPoint:1304"
    },
    {
      sourceName := "OAI.PiExponentJets.RegularSequenceQuotientTail.principal_image_eq_scalar_top",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceQuotientTail",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c5f2fbabfdf3cd5ff8954135a724e575c2a7ae6ac21d60f82e64350e5c2c2fbb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceQuotientTail",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceQuotientTail:278"
    },
    {
      sourceName := "OAI.PiExponentJets.RegularSequenceQuotientTail.quotientTailEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceQuotientTail",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f246f330714c409e754d695f95a4635180fe15a8d489c90194ddbb07eb55069a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceQuotientTail",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceQuotientTail:674"
    },
    {
      sourceName := "OAI.PiExponentJets.W06.colon_pow_succ",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.StabilizedColonPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c2ed06724bc0662e5af28b9165f29fa868caf8272bbeb447b0e29ebdaabb8a6b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.StabilizedColonPowers",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.StabilizedColonPowers:510"
    },
    {
      sourceName := "OAI.PiExponentJets.W06.colon_pow_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.StabilizedColonPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a6f45ef5d7dd451578858c0c7f614051964ba82a8169b5f13a5a416af0ba6e7d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.StabilizedColonPowers",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.StabilizedColonPowers:351"
    },
    {
      sourceName := "OAI.PiExponentJets.W06.colon_powers_monotone",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.StabilizedColonPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "310cd9485270e67da02a543d47b8945baf8b0e0390100c5465090d6ad8628f28",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.StabilizedColonPowers",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.StabilizedColonPowers:751"
    },
    {
      sourceName := "OAI.PiExponentJets.W06.exists_colon_pow_stable",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.StabilizedColonPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "28cc2b322ce485d5dc466f64f8f60b0b12a92f23c3510582883ba578200795db",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.StabilizedColonPowers",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.StabilizedColonPowers:1736"
    },
    {
      sourceName := "OAI.PiExponentJets.W06.exists_colon_powers_eventually_constant",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.StabilizedColonPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a4761dee6898b581d329722a2942ebc007b217b62327f4872369cc5fe9adc795",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.StabilizedColonPowers",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.StabilizedColonPowers:1293"
    },
    {
      sourceName := "OAI.PiExponentJets.W06.isFiniteLength_of_parameter_killed",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterKilledFiniteLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "688e7b4f4fe414b0190995f1b3cafbc8d605c094b2763f9e88fcaa4443f55e25",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterKilledFiniteLength:727",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterKilledFiniteLength:727"
    },
    {
      sourceName := "OAI.PiExponentJets.W16.regularPrefix_quotientMul_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularPrefixLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "08b2acc333dab3dc09ce3ed19608a17b47acdfe62fd79b0fef23d2d71dbafcd6",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularPrefixLocalization:2245",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularPrefixLocalization:2245"
    },
    {
      sourceName := "OAI.PiExponentJets.W18.augmentationRangeShortComplex",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExtObstruction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0cd8db3fc0887716e2361a956ac11c97dacb1dc5ec4d12cc99be6495f0351658",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExtObstruction",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExtObstruction:1628"
    },
    {
      sourceName := "OAI.PiExponentJets.W18.differentialRangeShortComplex",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExtObstruction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f74c6b047ec8eb8a651c91670ac76e0e5d66f009e34bc2fd6155804858ad4ee8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExtObstruction",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExtObstruction:615"
    },
    {
      sourceName := "OAI.PiExponentJets.W18.regularSequenceDifferentialRange",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExtObstruction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e8bdc11f441b16f8fe5ff2949779c71c2a086c75649edf8ba24ef3c98be9e43d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExtObstruction",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExtObstruction:3024"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.ActualRegularCutHistory",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "inductive",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5eb2e70d1a30b374f5fd1ab2ebf0d88968fe7068ccf937009c7234d154de26f9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:2635"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.ActualRegularCutHistory.casesOn",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aadca363642a976d9cd90d814e8a565309df4eef1cca30f5be646153e28b6f16",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:2635"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.ActualRegularCutHistory.nil",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "ctor",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cb79fb17dbc6eeab2b6ddfd536a3370c3d660f7e038f6c2f79077438feda3dd2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:2635"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.ActualRegularCutHistory.rec",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "rec",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "74bdff2ee32bc187c6306b2e2a63d25704892bb08c378878d33c7beabcb63819",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:2635"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.ActualRegularCutHistory.recOn",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6776aa1cfa893075e2471c8477212f1865ed58c1e0ebf8d1f9da98e25a5126ef",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:2635"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.ActualRegularCutHistory.step",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "ctor",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2d1f3ae76b32a62c6ef09a23437639cac4909e6b2a3a89e0333e899ebc5f92bc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:2635"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.HomogeneousPolynomialIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a5bb34fbf34bd2908f1906b1c462f8b876c172d65ad1ac0a6b8842cd0fbe1ea8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:357"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.HomogeneousPrimeStep",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousPrimeFiltration",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9d4c868c504073b7eb780dad2767cac872bbbac95c07a41fe364c3ac88ccaa5a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousPrimeFiltration",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousPrimeFiltration:283"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.MinimalParentsBelow",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedMinimalPrimeFamily",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b9716a7cf9f006a03d8e3a90ae7a785afab9eb8ce43a27685a67d59533c51edc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedMinimalPrimeFamily",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedMinimalPrimeFamily:210"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.ProjectiveComponent",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a94cd610bdc02eda32f06e0a43002e25efc24ce9fb49249ae6433e58ef8d5637",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:324"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.ProjectiveComponent.coordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a8455222c6abbb64278be3df2fdb05f4e0c6a2409a2adb2fcb4967e1b3963a17",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:846"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.ProjectiveComponent.hilbertDegree",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d5ff5f90a8d3459cadf43d5d8faae91c6fa1bd5675e56cd22435b5eb7cab09e3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:1103"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.ProjectiveComponent.homogeneous",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8112417d9e3cbe2bf0a949f5077aa8d49b9d9875803328ca515e4fc96e55052a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:706"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.ProjectiveComponent.instIsPrimeMvPolynomialValIdealAndIsHomogeneousNatSubmoduleHomogeneousSubmoduleExistsNotMemX",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "82faa3ca9fd7bd4e1882393b3ef3e7326ff221f8947d54dfa0026c2e07846ee0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:631"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RegularPrefixCut",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "inductive",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8e334228197d32416ddaf12693cf3173fe2af66dfdc87dc7a483e27a51382212",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RegularPrefixCut.avoidsParent",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "109f7c74c3704cd582ac9507225530f956a85bc11810c2118adbb00c5c5e76f2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RegularPrefixCut.casesOn",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eaa6fb6efbd7b764b07964fce84ddd3d11b2124210d24dc4aa960b5c4c22d20f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RegularPrefixCut.dimensionIndex",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "89f02a1e9ce2a2430c88becde540afe493c569369a834606316478b2fc76eac6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RegularPrefixCut.homogeneous",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6a65fa5a3b7c6c5666f51f1b70c8906f03b9dedca8bc57fc72aacc3217fce1bd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RegularPrefixCut.localDimension",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5cfe9344248b8b8cf9daaac87b0c1b375557f17555453ea3e9b28eaed3776821",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RegularPrefixCut.mk",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "ctor",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0908703b7de12b92f98582bd5aa8e338820c8891534f0a405a3750e9947d6f35",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RegularPrefixCut.mk.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f006e390e36084a48ce0ecce7d2e6d32f295cf1dcd1c45d4733f57b5461ae01a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RegularPrefixCut.next",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fb9dea5be57170ca6674b28bcc8c462bae821ee2d4f8351b7b88c94f69c162b4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:1956"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RegularPrefixCut.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3c2c373087e36fed7deeb792392d41cd110c8ff7f385a691c7aa990ad1b3693d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RegularPrefixCut.parentDegree",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "de4ac213a0ad88fffb1557af2aac4cba15bb2fe6ab6b2f0f3099a861337ef9ee",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RegularPrefixCut.polynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7e8a9a7a9fb3706c77101dffc6f8da8ca9730aada9b5c1c4ce0632e50b14a5f4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RegularPrefixCut.polynomialDegree",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3dbf62c35404cd39a3cfa29ea14c580bdd1ba0e97457f3d46e9922abdb4e2b60",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RegularPrefixCut.positiveDegree",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "84f2fbf58d6bf80715899c56a5e9a19ea7ef5e5358ff3f1075e68958b76e4b31",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RegularPrefixCut.rec",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "rec",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0c0a296d24e1de0f73886193bc9fb481c18d6c0d8fef17bbec4bb5fd70c46725",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RegularPrefixCut.recOn",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a751e4c9f0689aff9fbaf1d9e3a8ac315f9941ca967660aa562e1a000fef50a0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RegularPrefixCut.regularAtChild",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0955dcef776203db5374732b4659d1fa30f76b361368d3a598d4625bc3e73f64",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedMinimalPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedMinimalPrimeFamily",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "200dbc987c8506d65ca7ffa77d7c2415cae127ce8d32603fbebc189b51a79826",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedMinimalPrimeFamily",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedMinimalPrimeFamily:392"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedMinimalPrime.finiteFamily",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedMinimalPrimeFamily",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "04f2d480056c38fc3145033a3f802785586025e414ab449a1f55b64fb0ab38bc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedMinimalPrimeFamily",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedMinimalPrimeFamily:609"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedMinimalPrime.instIsPrimeMvPolynomialValIdealAndMemSetMinimalPrimesLe",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedMinimalPrimeFamily",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4e1ca64137c072536cca8140640fb16042adae31edcc92fd802419420b45ed23",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedMinimalPrimeFamily",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedMinimalPrimeFamily:958"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedMinimalPrime.toComponent",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedMinimalPrimeFamily",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0cabb84ea07578bf96a323a2a16519a04142970afaac4b5dd046361067930c76",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedMinimalPrimeFamily",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedMinimalPrimeFamily:1037"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "inductive",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b57daf01b22b656e92046e03f3e1b63f06476962b8fa4c92d2329397ca12b03b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:1670"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.Index",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e099c49a173767b66a5e7099b6379b15582f31767f1c219631652d9dd0144709",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:1670"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "inductive",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "75718fcadbc3aaeda226587506de51994ccd31618314c852547c4521fee24a8e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut.Child",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "de334c0f15cd68fe2d0c2879699dd05153e1f3e4b862dff66f4828f122917504",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut.avoidsParent",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "629c816556e1c0249a2f96a57aa93634cdfa79b0d113fa408b9a3d78ed9cd619",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut.casesOn",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "13e6088e1c4dc549ce117f67f03c7003934a5601bc4dbb9ab5bab61dc8762f48",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut.child",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "537167fb8e3608fbab413051f27f07c5c3437194384cabcf5c50dd66776ac589",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut.childDegree",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6c9865bd12576af9fa36ddf2d0e6c6a2a0014f04e74959fa3d195763414bb16c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut.dimensionIndex",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "286e083a1baa8463d98f3a960722b6328c4aa670d7e098827ae4c827e696e281",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut.distinctChild",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fccabae50816d2138c288466bcc5759e6dffcd13f4c00fa82dc15f85439735c3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut.finiteChild",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "947399d4a018295e4db0620476d6dda67111774a57faa2e9cdc7b5d7527dac63",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut.homogeneous",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dd20c0dfd266c9b5c422f0eaba7e43ee6319d53db074c05b8572df55016f4180",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut.instFintypeChild",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c1f4480487491e0a0d64be77548c56ae3b67b228fc94d0eb0960973ef7afd909",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:4132"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut.minimalChild",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9e89146e5c504b50396d7cf53b9d08257c1ad32a6bd178b4b2213ad903be0919",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut.mk",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "ctor",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1f396faae2aad4ff363fd6458c7dd764f2c745cbc427764accb63b3708fd3400",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut.mk.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7afa2e05b6acde74772389c3517b4ff1e92d1341b7b95b781355b709e7c99204",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1b932aac6421ae6efa8baa12b783c614e382aee18c02fd702e6b9f5586074d98",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut.parentDegree",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "037972e4341f66a9c169cb905daae480125f6adf58cbdaa985cc5ccf3a2d8752",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut.polynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8bab4ecec31085f36815d036720443571aa9e42a9455c6d5616b0587b1101648",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut.polynomialDegree",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ad70d999dc5fb14f345ffce998b139a80aa7a467e375b4ec6803ee80cd6ad496",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut.positiveDegree",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0ad8fd06da450e5e2cbb057c8335d87c1a5f818984933db24d74e52b6f657e24",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut.rec",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "rec",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "73f28da41ad402b3f2f1f1d82de1e0e95adc5d01cf8d7da20d2e8d0650463f24",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut.recOn",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3c2d47ea498f2cebb18abf5bd806c6f8539d1658db771674c3aa02dcc71aaaad",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.casesOn",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "66818ac46c7b301f8bb6d74ac62d6729d14398a1aeaf1c4867592807ccc626a8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:1670"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f0c821891740c82369fd95dd5a2dee7eda89aa6497eed07af30793d60ca8f1ca",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:1670"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.coefficientAt",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9665ec8ae4348dc0788c9a7c566e2c31ea576e12dabae57c6e72519a18dbd7f1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:2195"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.coefficientAt_le_degree",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5893dfb72924dadafaa83f07448add85f78f8b33f26d2dd69399f009b83ede63",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:2627",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:2627"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.component",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ca7fc49ee9d03ea52e3da406f065a46a2cd40d4f966eb61374f30cecf6ba3052",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:1670"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.degree",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "09a4e73749b5fb172fe3ed88c511b61a20e4d408ee0c85f3aec3b4510e1f0984",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:2054"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.finiteIndex",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "02ec6efa3752f94d8cd4e99416eaf48625578454a5598d2ad6e13efa4671b687",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:1670"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.instFintypeIndex",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "43b2e518d860318e82622d5fc82fb1f6dc571ffc2c6814ef82807b46b9040f0c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:1969"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.mk",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "ctor",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7f2cc7c192f08112d893e5537f1c4ad4eb0ff0b72549459c1817b82627503329",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:1670"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.mk.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f9a8c22cbd8b7a9c5cd939d04b0700d9cb29b03f5cbfc3b53876b3e7307f4d53",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:1670"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6eabfbf5310b4a523336fa36b54a01f1df0319f5cd2bf99f9118620d0554ee05",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:1670"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.rec",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "rec",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "31ac691fb7e6eb273ed6415388062ec4b92f7aaa8689a0104cfb581e99db3dbd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:1670"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.recOn",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ce2bbf9b211ae1491136193dd26bd7db9c1129870342e3e4197c211ad45f62fe",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:1670"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_021.jsonl"
