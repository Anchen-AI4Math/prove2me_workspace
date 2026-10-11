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
      sourceName := "OAI.PiExponentSeshadri.TensorPure.sheafify_restrict_unit",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "adffebf5906c6112c58a8e6417ab895b5f223b34b1697073173497c76eefe7de",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:3066"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.tensorSection",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "724e277b14f9a8e0e9055d5f2e5eb662b9d31812baa984ade8e2457ca9b9e171",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen:1025"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "97e3277c3e507b069beef6b711352fafa099675aa208f3504f76fc6a8ee5395f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection:6403"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.unit_inv_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7be4c7808c11b05ab659036f06f9acfcc1eb64edc25d0e6fc952a60fc7ae6810",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection:4448"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.unit_pure",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ac6e16f57c5bdbb8b10b9738072f6fbb19794a3bd82a6493cc826f41475c7273",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:8732"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TildeExact.map_mono",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c202b834415e6608fafe6471c64defef21d7009483cec9ce1c0af258411b53c7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:24417"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4835d47897caa93be4ece012a3a02a73f8a074ad9596dd7133acc9c968d6ac4c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:25105"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TildeExact.preservesHomology",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "01bf5fa811905a8431365d0ad3656846cb3de462f7638277e62ddd22d8c3bf99",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:24963"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "422a3044ab1d12fea549fe6afa523ffc48103a767f70b07ce2fb503584d1283d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:24848"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TildeFlasque.flasque_of_injective_global",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bd887964da3e9e26c302e62b57d91c3c9b8fd3774eced6e7a5ad22f12336500b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:23298"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "332db7c12b8574e7380029e942f2a66c17beba5ea658dad97feb25d67a2c4b14",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:23812"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TildeFlasque.top_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d1529d42354b6406faba88914a7b9e8d83447437ea5b65a4e96720eb72fd0419",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:22225"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.UnitEndomorphism.app_eq_mul",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "12bb5390c471f2e23d670414f664f0771659ef68b38f57e257e5149eab934c61",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:500"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.UnitEndomorphism.equation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "679e95b7170c465bfab5e2cdfcc0f2ed97c30b50a897abc6bfe51d99f5375a87",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:424"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.UnitEndomorphism.equation_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a43323f49e0782e276a7a87b544926a80a5226ce3f98f15f894a30a3ad5e2c55",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:1171"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.UnitEndomorphism.image_principal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a601e8df45c44ff6345a5d6bc07a72742d6fb18e51379e19ad9a73bf4a297956",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:793"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.UnitEndomorphism.unit",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "68c73dbdd1892420d1ddf474c6036ddd684b85a9fd9850c4c18f8d1dc19b444b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:308"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coefficientAdjoinRootQuotientEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1a6b31e891dfe492bd37fe139fd829e6106c76d777347168523f0eb69446a1ee",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient:2498"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateCoefficientSplit",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "25da8da8f12eb53bfc17eafdd30b8a586e515043ea85034a7d301e136ccbe7ea",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient:409"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateCoefficientSplit_X_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e4b98c4493fd19a58490e5ffc3f46302b62b7cf65965288391b5364a6684b930",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient:651"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateCoefficientSplit_aeval",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8847ae4d9f71eb9d07740804366550c7db5866f4acc4c482fcdf0d8aed3938e3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient:1255"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateEval",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ac4414a563cf7a3b1d25b04daaa4435c3c5844f0c5a3e0bc06accd6e6fac4fba",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:354"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateEval_X_none",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a6c580f6f64d6398df4d9640f0bd57db70e2ea0595ad82222a7b9ddcb0a04d46",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:648"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateEval_X_some",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "74130ba22f02bc45fc077a225b5704aaa4d2e537fffc5862dd28c7d7eb989d89",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:772"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateEval_homogeneous",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a6b83b163d16bbd36b96ae93d98a32d5ba80c193b91e761a335f8e1be581c77e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:1353"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateEval_include",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2d4322c18232d94bad2428a06fe459c27eabf64e72e9319d2aa7d165cf9b3188",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:900"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateEval_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "995d811dab5e56b3bb406786758e01993dfcc6b0e4fe5950156b202fc4458561",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:1185"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateImageIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "476d7073256559e1b1a947832bb48c4f07d897d4560e51360135f05471a17d67",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:2070"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateImageIdeal_homogeneous",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a7b61e8cc581a6f2534d4de2835a174cd8cc657ebb06813b994bc0c2275377fb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:2885"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateInclude",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2006c87f9824bdb2f78f8c92e862b68989f7baa173b5fac97f04234b7da9cd76",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:514"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateInclude_eval_mod",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "31db06db28e98de00db09becad8caf93d606004b83d6a0fc34a878a3781b2231",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:3255"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateInclude_homogeneous",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8c19bf82abf0997721759868dcd644b698d2b518617685a0fc38db66f75ad164",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:1895"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateInclude_image_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "989b8b60d27440e65f7329324894a10c62433ad37aedaa231ef744e8054f2fdb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:4081"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateMinpolyIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6959d27b98cf1257ddbd51cdd53692529c8bc0f5049ed97a61a98eba1a0bf2c4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient:1917"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateMinpolyIdeal_map",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2f31269663c30ad8f7be6b1e1ee19ddf8a6927455ae75b5e172aa7608cf4f6aa",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient:2097"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateMinpolyQuotientEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d008c4987893d7e9a50db2448f80dfca2a17083efdacbcf0a2736e67901df729",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient:3170"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateQuotientEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "da111812f0d010fec852e6c028629bde5bcd0268cbd2d6e3708c015fd73147c8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:4930"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateQuotientEquiv_section_map",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "35246904d26e6ca59bd23498e336fbcfdd4e109fefcde5f77028a11436fe081c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:5867"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateQuotientInverse",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "36090d6697b96a83e0f72e0d7619ca0786aeba77c530e17115519230ec1a6781",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:4614"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateQuotientMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "24d6c637508c7559e58a82cd561dde8f8eb480ab56d7a6ffb2937e654dfe4e92",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:3805"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateQuotientSectionEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2f739afd052d93cc5b9cc75980d36bfcb790153a0cb4dcf4daec034978b40dc5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:6824"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateQuotientSection_finrank",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "57bbeee8513df40d63b4f9482109dbf042f03ed548225b184b34ced465f26064",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:7195"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.homogeneous_ideal_map_of_degree_preserving",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6649777ddd74fe3bfb252b57c9d643a8d27ccea25f695f639e5ed70c3ff9edf3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:2220"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.renameImageIdeal_homogeneous",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9b5303545f53984c6ae273336a2988cb855333e0151cba12b578ef048bac0c9d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:9572"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.renameQuotientEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d00d629a16329419695660f5e27522f9d4b7e2e779e15dd6e4392fc1294772aa",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:7575"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.renameQuotientEquiv_section_map",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9de7f02400a11adb0bb41cf349f6768f0bca9d4a1b4810dc22e683855c4eacb3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:7846"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.renameQuotientSectionEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b41198106807ef82d296f2f7a5072fcc9aabefdf2e527df502414f80438fa997",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:8874"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.renameQuotientSection_finrank",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c83d9869f9fe0cf3d86443fe167eca8a8ec222b825af0db6490ce6e10bf4a2d6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:9235"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W10.TriangularLocalParameters.firstCoordinateContraction",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "deeda6e6bbc00c8967fe27142d2155993fd33f1ffcffdf170d9f32df790609df",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters:8251"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W10.TriangularLocalParameters.firstCoordinatePolynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6ac13fdef2c80b52d49d1f211c7cbeecb56420b2246308788edc98f1f7edeefc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters:9200"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W10.TriangularLocalParameters.polynomialMaximal_regularParameters",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParametersAssembly",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7f4eb0e95cfa372377de51dc6eb18c94ec3cb50f5b146ecdf24d7bb93b3c5cc8",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParametersAssembly:297",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParametersAssembly:297"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W10.TriangularLocalParameters.principalModuleQuotientEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ab5acfae941991c13e943c91e81f5829dab1e049ba4023eb10b1ba017e2fb871",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters:900"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W10.TriangularLocalParameters.scalar_top_eq_principal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "99fa6a3935e9c27a35f1d80dfed0e20b789c94e43ac705932a1e639b40c23c65",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters:723"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.AffineRing",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bfe0dc060975c1be7f2b56d4369e754e815b7a885d45952348aeba66be8a1773",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:6568"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.ConeAway",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9a3b59d4ffd7109fe42c13968f2244ca495fc30282b8fb2abee267f18be4224d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:6655"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.ConeRing",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4160e00f2c21d5b8fb41f99a295bc70afeb4be80909ac2b47c3792a6fe5271f5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:6608"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.LaurentChart",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7e992e1d35b840779d65e88e03b37deeb62f113633253e233cb0f8d029dcc13d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:6731"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.affineLocalConeAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fe21d35610951cf606a973b5d16fa90a8099d1ec260c00b238e81a4c85bf3598",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization:2159"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.affineLocalToConeLocal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fd10110f77711067872b4f387ca178e5b1eda86d2a9df9b082cff714ab77b09f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization:1883"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.affineToConeAway",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fa4b76193ade1a8e2c946d4fc59c5de9e05a3f9d1f8dffda6950bff12b81527f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:7431"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.affineToConeAway_C",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "89cb7b926ed8372b42abf76b4ebb6546c87d58db0961f68504521c7aa867951b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:7725"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.affineToConeAway_X",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2a17051c2071887fe234d7574410f716f67f92fb4f06cef20d1252c704a5980e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:7923"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.awayChartPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "df5d873daa8324124dda1ce70d406db4031e4a122d0fcff3d3381d5e295376c4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization:447"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.awayChartPrime_isPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4506b5fd4ecc0c802f5a6f930d106d0d4a76b63df61890b22c359c3bf9fb8545",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization:574"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.coneAwayToLaurent",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2989ac4ce9789db3f1cfd48536b3c6413d210be1c478689993479201b93f64b6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:8945"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.coneAwayToLaurent_algebraMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "32dc70f0b20fe23fb9e5c45ef2245e3099f9ae618deda88c282e7f61e0a63998",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:9179"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.coneAwayToLaurent_comp_affineToConeAway",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c11f607f82ef10791c191a2695d88b1ba5dd869ac54748b1772e05b0b4d49e17",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:10648"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.coneAwayToLaurent_comp_laurentToConeAway",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eb7c626ef290ae0d61667d7d444e3b9b5f84b0c59af77e9bd38314fb4da6c1b6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:11553"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.coneHomogenizingUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "22f9e0197a3943ab31cd7186e3769db37a92b5a3b9ad3e2bee9176e3219b544c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:6793"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.coneHomogenizingUnit_inv_mul",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "08670ef2721340ddd131f67bf0ccc47472ee9c11fc480cce2b5dc37f3a84ec0c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:7150"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.coneHomogenizingUnit_val",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d028aedfd505849babe5549d2b85f8cecc5595689b55d23329bd1fa8ab13f48d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:6956"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.coneLaurentEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d8f1446abfc8c49f2b1ded6cc0493a34681c2a212cc4d5d37158ea8095814a3d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:12364"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.coneLocalCoordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeRegularSequence",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7e1496613a3893f8c30ec1a95a1974bfb04ddc71b227249f8a8aa791b1752321",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeRegularSequence",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeRegularSequence:2232"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.conePrime",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "61018d8f2e91030eb4293609e0bf7788de496e98c505b38b00ab0126093af80c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization:692"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.conePrimeLocalizationEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c4437333ba9ec3898c0699888b21d29845e57a5903e0e03a5f21cb133d0617d3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization:1407"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.conePrimeLocalizationEquiv_algebraMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeEquationLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "40f53da5d56eb99c0540ff3f7956a62de92cfb1d80045196f2a0012bbabcad73",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeEquationLength:328",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeEquationLength:328"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.conePrime_isPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6c0a5c790972fdc6fc6be453ae79c82e0feb272b40ea980d034ab3ec0d2a9a48",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization:814"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.conePrime_minimal_over_homogenized",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ConePrimeProperties",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bb3bb9514e722abaaba3b61b43828a900e3f59756945f59bf12408204e71aa02",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ConePrimeProperties:1891",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ConePrimeProperties:1891"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.coneToLaurent",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "17697696b257654da1658c8b5a6d47fb9364e5480bb671c2d8b798dac5aec343",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:8176"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.coneToLaurent_C",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e1dd8ffb8947e9e254ba7ad04cd1a650f44bcb73f01db3897510590a072daa0c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:8437"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.coneToLaurent_X_none",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "345b36c198aae022f6613d0ad2f7c1a5735e0d2497967e48e30a515f3f9a08f7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:8600"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.coneToLaurent_X_some",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b4fa8f04eb282849d78af243021806fde9ab8be154869aa80b0ac9fcd268556c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:8742"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.homogenized_cone_local_length_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeEquationLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5b1c59064ce245a265ac1e7fd62ccf58f0e22367ad2862daf20e1a10a664091d",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeEquationLength:2914",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeEquationLength:2914"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.homogenized_list_regular_at_cone",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeRegularSequence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "42d46784ee3f9894f3cae25b24663519e2444eddccbd0b43966eefc2414250ea",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeRegularSequence:5073",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeRegularSequence:5073"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.laurentPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "daba7f550088f15c5edd31a5508765cae760d647cae5d19ded42adb0c674b2d6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:2762"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.laurentPrime_comap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8a63f2acb2a1253a60f74cbc2a2fc50f46e979a6a6505872a58ecead147c0eb1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:4306"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.laurentPrime_eq_map_polynomialPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "448c9991a0dd010c89eecb0e035634e640a2f8e3c2a03363ba28f1d596d5d330",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:3445"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.laurentPrime_isPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e27189414eac1d00526549906ab2a3419af76f848574f113327aee54159b21b3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:3985"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.laurentPrime_liesOver",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "26d696e50ff9b2c7922fbb3cc110f545a2e2d58bf3a81bfbafda9d924eaa2ba8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:5032"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.laurentToConeAway",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5b7a0321c1a896452bf2c13f909c190a442f4a28324235f27fe5918459e6a70e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:9385"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.laurentToConeAway_C",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e640e5b9c5c1345c49e9e0098d63427dd13bf3d7d696ed8795b5f76f395adb30",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:9534"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.laurentToConeAway_T",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "abc0c6c390a59edac6bac6190e2cb1a2c5781545f71b2f24697a34f068924cab",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:9709"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.laurentToConeAway_comp_coneAwayToLaurent",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "07717b9d1209453ba865a660a445ff8c8bebd3a0d0078447579a85b438d311b5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:10172"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.laurentToConeAway_comp_coneToLaurent",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bcfab8d7af828e5926b70f0799d2875067062b33ffb3692e274fb50353b8d26d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:9864"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9fc5988ec8c7c8370ea1db8433164ef1c1e3a6095cbb537ee236beda0c69f270",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:5163"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a52b7206a5d749d16308d251b8a4602c3b54c6176192f2e38cb5dee97e39f93d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:2844"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.map_homogenized_span_eq_laurent_span",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.ConeHomogeneousEquations",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3c526e10612a9ad46e194f6ad3256e1b9bc05b9c73ae80be579d26ad09c35b8b",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.ConeHomogeneousEquations:2982",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.ConeHomogeneousEquations:2982"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.minimalPrime_isHomogeneous",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ConePrimeProperties",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9ae0c04941308becdd89d982858193228bfc866d5ff3a6569a302906041ac0d0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ConePrimeProperties",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ConePrimeProperties:1016"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.polynomialPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8c85969951e04df3107306eb712d43ad3db4254e0da3bea596ad0f1f41b9dcf0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:1544"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.polynomialPrime_comap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ff90eb774d1e0850c8d2cc78ff50074fa6c6b47c9f6b04d92944d17f70561f0e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:1615"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.polynomialPrime_disjoint_powers_X",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d5ecd3847ccfb1afac25742150ba28c319920f903af4dc78845e76329491ec24",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:3113"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.polynomialPrime_liesOver",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "db129fda609d720c176e41ffd9dc45b941643d0454d42e3072f80a273fe5b479",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:2009"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.IsolatedIntersection.local_regular_avoids_retained_minimalPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IsolatedIntersectionSteps",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "174525f6155a7188b034d7f6658d9f7b4a478f0b3a8f1e9721dd8ff60518167f",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IsolatedIntersectionSteps:1141",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IsolatedIntersectionSteps:1141"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W20.prefixIdeal_homogeneous",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularPrefixes",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aba61bc7e1d03f289008f77d120013c44f3ce319e52a26fe428a749824dbafa0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularPrefixes",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularPrefixes:1456"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W20.regular_homogeneous_degrees_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularDegreePositivity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "09c5e409980f7b28b1386339659ae384112e3c12ebb9d53b317d4cfd389e87d0",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularDegreePositivity:1802",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularDegreePositivity:1802"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W20.regular_sequence_term_ne_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularDegreePositivity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fc6a34b8052effb524bc37cc0fbfa0886305969c95db32b3436d5417c0784e93",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularDegreePositivity:919",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularDegreePositivity:919"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.affineClosedQuotientLocalEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a484d45d8c1f4d80b318ecf249a26b6678dee9ed5d7b43bbe62926ef95163635",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:6616"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.affineCoefficientAlgHom",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c43edd3e51c57a8a3c43ca1b5e5bcf8d035b29a910c491831f42f0c8e6315c8b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:485"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.affineCoefficientAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2be63f0da4599239d9a56dbf516e9182cc6f379e1d208a431f9d0926998c1e4d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:929"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.affineCoefficientMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "db9326dd6a1edbbe297af026facb5a6b832b90943950e1ce0ad5f3cf6d4cc54a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:773"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.affineCoefficientMap_comap_closedPoint",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "63277f5ad1a40f8cf98412cd2f59083644bcf87d35c0347f92b1aaf1ad3dc3f9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:1774"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.affineCoefficient_isLocalization",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "540a041ff34de50bbd97c2bc0c01c4d33217b90ca4f0940d5cf764dbfa86ebab",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:1157"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.affineLocalQuotientEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bf47ab078d579e25db44eb9477aec2f0b3c1f6770b18ca76ced9719d08b9a97b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:6158"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.affineMappedIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a94b58e5e52c9c0915f6890e7d03988f83b2b516671af315ce252f1df3e8e737",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:1484"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.affineMappedIdeal_le_closedPoint",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8e33242bf87e7074b1cbeafab345ea74ee74e0d1accbf5184e0360feb44b420f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:3375"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.affineQuotientAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3cb17854d328cf63616c8addd82a89ac0af16b36397dad292e2d478509097480",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:7621"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.affineQuotientMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "184b124db47687b98b542dc0d6229933902effab6d5b21995b55ef5d83e39273",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:7358"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.affineQuotientMap_mk",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "335ed8a212791f98f4118d789816d31ea8ca26e2035b07d0643ff403e767e757",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:8195"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.affineQuotient_isLocalization",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3fe8365d29f80a2a326153d5e181a7c427e451a45a90c11fc674376bc44efdad",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:10476",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:10476"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.affineQuotient_scalarTower",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "88035e3be6dac486c9aded0ec39a223415551d5512e99019f13cbd7764215602",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:8436"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.atPrimeEquivOfRingEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1884389e4a905b22b1a738ef1ddbe8022af6397e253ef14b862791a221e6181d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:9693"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.atPrimeEquivOfRingEquiv_algebraMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "94dd29c5e70f140604a81eeee378a58edabed80eb17541e9472ce685d8f04a22",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:9945"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.atPrimeImage_comap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c3a87fe564cb98e57e8ed79fa881b3598b184beab8f5318db0c46dbc8710aa6a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:9478"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.closedPointLocalEquiv_algebraMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3ca3f750ac4622b60485c430876b88865a19b722a1d99989e4730080cf69feea",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:4545"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.closedPointLocalEquiv_map_ideal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "de5393c5158a04e2f5cc865600d6a19276972ec3eb43b65af10c1c6780bf3a40",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:5672"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.localizationQuotientParametersEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "707b1503fef9477f8076fb6421d3cde3f420405626c9365973a9e255fdf48a41",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:6206"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.localizationQuotientParametersEquivTrans",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "51fb2d8e0b87a2676ea9b06777b917f4db2d89b63a907c850f0969c230311a6b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:10358"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.mem_quotientParameterPrime_mk",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "63ffdaeef351068d0524fb42db71f50ec48c2e758d5953be76d8ee34b99561a5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:1056"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_033.jsonl"
