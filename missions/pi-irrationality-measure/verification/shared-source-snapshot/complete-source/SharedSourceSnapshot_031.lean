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
      sourceName := "OAI.PiExponentJets.W22.ActualRegularCutHistory.recOn",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6776aa1cfa893075e2471c8477212f1865ed58c1e0ebf8d1f9da98e25a5126ef",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:2635",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:2635"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.ActualRegularCutHistory.step",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "ctor",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2d1f3ae76b32a62c6ef09a23437639cac4909e6b2a3a89e0333e899ebc5f92bc",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:2635",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:2635"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.HomogeneousPolynomialIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a5bb34fbf34bd2908f1906b1c462f8b876c172d65ad1ac0a6b8842cd0fbe1ea8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:357",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:357"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.HomogeneousPrimeStep",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousPrimeFiltration",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9d4c868c504073b7eb780dad2767cac872bbbac95c07a41fe364c3ac88ccaa5a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousPrimeFiltration:283",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousPrimeFiltration:283"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.HomogeneousPrimeStep.homogeneous",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousPrimeFiltration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a82b355f5b65981e4c35676877a2207ec59e2844a4cbdcef44153d0de6a0bab5",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousPrimeFiltration:555",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousPrimeFiltration:555"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.HomogeneousPrimeStep.lt",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousPrimeFiltration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "707a9b83337d838b8de59f4b7b06b1b5526b5f4676685200fc14439bb4db2adb",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousPrimeFiltration:953",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousPrimeFiltration:953"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.MinimalParentsBelow",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedMinimalPrimeFamily",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b9716a7cf9f006a03d8e3a90ae7a785afab9eb8ce43a27685a67d59533c51edc",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedMinimalPrimeFamily:210",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedMinimalPrimeFamily:210"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.ProjectiveComponent",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a94cd610bdc02eda32f06e0a43002e25efc24ce9fb49249ae6433e58ef8d5637",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:324",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:324"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.ProjectiveComponent.coordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a8455222c6abbb64278be3df2fdb05f4e0c6a2409a2adb2fcb4967e1b3963a17",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:846",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:846"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.ProjectiveComponent.coordinate_not_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ed598817e7840d2fa1bad5500550f639ac8b070b91dcd871a53be787e9b18080",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:942",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:942"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.ProjectiveComponent.hilbertDegree",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d5ff5f90a8d3459cadf43d5d8faae91c6fa1bd5675e56cd22435b5eb7cab09e3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:1103",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:1103"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.ProjectiveComponent.hilbertDegree_ge_one",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3ed7469183f91bfa8d72f3a13b24bd54b79ac4ccf3c43a260a9300c3f9948094",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:1261",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:1261"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.ProjectiveComponent.homogeneous",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8112417d9e3cbe2bf0a949f5077aa8d49b9d9875803328ca515e4fc96e55052a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:706",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:706"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.ProjectiveComponent.instIsPrimeMvPolynomialValIdealAndIsHomogeneousNatSubmoduleHomogeneousSubmoduleExistsNotMemX",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "82faa3ca9fd7bd4e1882393b3ef3e7326ff221f8947d54dfa0026c2e07846ee0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:631",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:631"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RegularPrefixCut",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "inductive",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8e334228197d32416ddaf12693cf3173fe2af66dfdc87dc7a483e27a51382212",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RegularPrefixCut.avoidsParent",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "109f7c74c3704cd582ac9507225530f956a85bc11810c2118adbb00c5c5e76f2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RegularPrefixCut.casesOn",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eaa6fb6efbd7b764b07964fce84ddd3d11b2124210d24dc4aa960b5c4c22d20f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RegularPrefixCut.degree_step",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d7e6944e55ea07f654e9bded665f5381f18ce39b8483264e8082cc629050335f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:2163",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:2163"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RegularPrefixCut.dimensionIndex",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "89f02a1e9ce2a2430c88becde540afe493c569369a834606316478b2fc76eac6",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RegularPrefixCut.homogeneous",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6a65fa5a3b7c6c5666f51f1b70c8906f03b9dedca8bc57fc72aacc3217fce1bd",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RegularPrefixCut.localDimension",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5cfe9344248b8b8cf9daaac87b0c1b375557f17555453ea3e9b28eaed3776821",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RegularPrefixCut.mk",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "ctor",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0908703b7de12b92f98582bd5aa8e338820c8891534f0a405a3750e9947d6f35",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RegularPrefixCut.mk.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f006e390e36084a48ce0ecce7d2e6d32f295cf1dcd1c45d4733f57b5461ae01a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RegularPrefixCut.next",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fb9dea5be57170ca6674b28bcc8c462bae821ee2d4f8351b7b88c94f69c162b4",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:1956",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:1956"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RegularPrefixCut.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3c2c373087e36fed7deeb792392d41cd110c8ff7f385a691c7aa990ad1b3693d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RegularPrefixCut.parentDegree",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "de4ac213a0ad88fffb1557af2aac4cba15bb2fe6ab6b2f0f3099a861337ef9ee",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RegularPrefixCut.polynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7e8a9a7a9fb3706c77101dffc6f8da8ca9730aada9b5c1c4ce0632e50b14a5f4",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RegularPrefixCut.polynomialDegree",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3dbf62c35404cd39a3cfa29ea14c580bdd1ba0e97457f3d46e9922abdb4e2b60",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RegularPrefixCut.positiveDegree",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "84f2fbf58d6bf80715899c56a5e9a19ea7ef5e5358ff3f1075e68958b76e4b31",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RegularPrefixCut.rec",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "rec",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0c0a296d24e1de0f73886193bc9fb481c18d6c0d8fef17bbec4bb5fd70c46725",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RegularPrefixCut.recOn",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a751e4c9f0689aff9fbaf1d9e3a8ac315f9941ca967660aa562e1a000fef50a0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RegularPrefixCut.regularAtChild",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0955dcef776203db5374732b4659d1fa30f76b361368d3a598d4625bc3e73f64",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:676"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedMinimalPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedMinimalPrimeFamily",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "200dbc987c8506d65ca7ffa77d7c2415cae127ce8d32603fbebc189b51a79826",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedMinimalPrimeFamily:392",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedMinimalPrimeFamily:392"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedMinimalPrime.finiteFamily",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedMinimalPrimeFamily",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "04f2d480056c38fc3145033a3f802785586025e414ab449a1f55b64fb0ab38bc",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedMinimalPrimeFamily:609",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedMinimalPrimeFamily:609"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedMinimalPrime.instIsPrimeMvPolynomialValIdealAndMemSetMinimalPrimesLe",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedMinimalPrimeFamily",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4e1ca64137c072536cca8140640fb16042adae31edcc92fd802419420b45ed23",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedMinimalPrimeFamily:958",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedMinimalPrimeFamily:958"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedMinimalPrime.toComponent",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedMinimalPrimeFamily",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0cabb84ea07578bf96a323a2a16519a04142970afaac4b5dd046361067930c76",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedMinimalPrimeFamily:1037",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedMinimalPrimeFamily:1037"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedMinimalPrime.toComponent_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedMinimalPrimeFamily",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7eb78b3eced735b8ec2d612686cc1ff77f22c1a275a9f403b64e2d0b0fe1d2b2",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedMinimalPrimeFamily:1665",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedMinimalPrimeFamily:1665"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "inductive",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b57daf01b22b656e92046e03f3e1b63f06476962b8fa4c92d2329397ca12b03b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:1670",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:1670"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.Index",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e099c49a173767b66a5e7099b6379b15582f31767f1c219631652d9dd0144709",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:1670",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:1670"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "inductive",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "75718fcadbc3aaeda226587506de51994ccd31618314c852547c4521fee24a8e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut.Child",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "de334c0f15cd68fe2d0c2879699dd05153e1f3e4b862dff66f4828f122917504",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut.avoidsParent",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "629c816556e1c0249a2f96a57aa93634cdfa79b0d113fa408b9a3d78ed9cd619",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut.casesOn",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "13e6088e1c4dc549ce117f67f03c7003934a5601bc4dbb9ab5bab61dc8762f48",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut.child",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "537167fb8e3608fbab413051f27f07c5c3437194384cabcf5c50dd66776ac589",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut.childDegree",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6c9865bd12576af9fa36ddf2d0e6c6a2a0014f04e74959fa3d195763414bb16c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut.dimensionIndex",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "286e083a1baa8463d98f3a960722b6328c4aa670d7e098827ae4c827e696e281",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut.distinctChild",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fccabae50816d2138c288466bcc5759e6dffcd13f4c00fa82dc15f85439735c3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut.finiteChild",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "947399d4a018295e4db0620476d6dda67111774a57faa2e9cdc7b5d7527dac63",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut.homogeneous",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dd20c0dfd266c9b5c422f0eaba7e43ee6319d53db074c05b8572df55016f4180",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut.instFintypeChild",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c1f4480487491e0a0d64be77548c56ae3b67b228fc94d0eb0960973ef7afd909",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:4132",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:4132"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut.minimalChild",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9e89146e5c504b50396d7cf53b9d08257c1ad32a6bd178b4b2213ad903be0919",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut.mk",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "ctor",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1f396faae2aad4ff363fd6458c7dd764f2c745cbc427764accb63b3708fd3400",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut.mk.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7afa2e05b6acde74772389c3517b4ff1e92d1341b7b95b781355b709e7c99204",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1b932aac6421ae6efa8baa12b783c614e382aee18c02fd702e6b9f5586074d98",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut.parentDegree",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "037972e4341f66a9c169cb905daae480125f6adf58cbdaa985cc5ccf3a2d8752",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut.polynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8bab4ecec31085f36815d036720443571aa9e42a9455c6d5616b0587b1101648",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut.polynomialDegree",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ad70d999dc5fb14f345ffce998b139a80aa7a467e375b4ec6803ee80cd6ad496",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut.positiveDegree",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0ad8fd06da450e5e2cbb057c8335d87c1a5f818984933db24d74e52b6f657e24",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut.rec",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "rec",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "73f28da41ad402b3f2f1f1d82de1e0e95adc5d01cf8d7da20d2e8d0650463f24",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.ProperCut.recOn",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3c2d47ea498f2cebb18abf5bd806c6f8539d1658db771674c3aa02dcc71aaaad",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:3223"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.casesOn",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "66818ac46c7b301f8bb6d74ac62d6729d14398a1aeaf1c4867592807ccc626a8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:1670",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:1670"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f0c821891740c82369fd95dd5a2dee7eda89aa6497eed07af30793d60ca8f1ca",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:1670",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:1670"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.coefficientAt",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9665ec8ae4348dc0788c9a7c566e2c31ea576e12dabae57c6e72519a18dbd7f1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:2195",
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
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:1670",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:1670"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.degree",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "09a4e73749b5fb172fe3ed88c511b61a20e4d408ee0c85f3aec3b4510e1f0984",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:2054",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:2054"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.finiteIndex",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "02ec6efa3752f94d8cd4e99416eaf48625578454a5598d2ad6e13efa4671b687",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:1670",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:1670"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.instFintypeIndex",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "43b2e518d860318e82622d5fc82fb1f6dc571ffc2c6814ef82807b46b9040f0c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:1969",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:1969"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.mk",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "ctor",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7f2cc7c192f08112d893e5537f1c4ad4eb0ff0b72549459c1817b82627503329",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:1670",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:1670"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.mk.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f9a8c22cbd8b7a9c5cd939d04b0700d9cb29b03f5cbfc3b53876b3e7307f4d53",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:1670",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:1670"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6eabfbf5310b4a523336fa36b54a01f1df0319f5cd2bf99f9118620d0554ee05",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:1670",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:1670"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.rec",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "rec",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "31ac691fb7e6eb273ed6415388062ec4b92f7aaa8689a0104cfb581e99db3dbd",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:1670",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:1670"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.recOn",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ce2bbf9b211ae1491136193dd26bd7db9c1129870342e3e4197c211ad45f62fe",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:1670",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles:1670"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.RetainedPrimeCycle.retainedChild_dimension",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.EquidimensionalRetainedCut",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "84f0707b8fea1851aa023a53bbabe4be796b7237f3baa4941b544ce74e9e5861",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.EquidimensionalRetainedCut:344",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.EquidimensionalRetainedCut:344"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.actualHP",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HilbertPolynomial",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "50243878f9a6bf35821a74fa85fcda60d27db2e7efc9367d62f05fadf92d3e79",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HilbertPolynomial:1135",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HilbertPolynomial:1135"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.actualHP_colon_step",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HilbertPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "34f3d400e1d916e786922fe02c7fa3c1fc97bbd9257c2b6c839ec9269f88512f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HilbertPolynomial:4178",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HilbertPolynomial:4178"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.actualHP_congr",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HilbertPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7c289401445a315abeab4ca693ab4a04e083c58b94af51f915b2acb7e6dc0101",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HilbertPolynomial:2142",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HilbertPolynomial:2142"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.actualHP_eventually",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HilbertPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "394963d18a358e08d667787aba41fe55d79c52105aab5d4ce54d3fa7d7a62be5",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HilbertPolynomial:1344",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HilbertPolynomial:1344"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.actualHP_leadingCoeff_nonneg",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HilbertPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f71b2dae374b448fc2e34fb7ec28897a4ee44dcd6a319901bdb189dd9d1472b9",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HilbertPolynomial:2811",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HilbertPolynomial:2811"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.actualHP_natDegree_antitone",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HilbertPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3a16090de249547302fc179105e86513415a87bb6cb55e739ce0738c0b15f029",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HilbertPolynomial:3181",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HilbertPolynomial:3181"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.actualHP_natDegree_of_prime_dimension",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeCutBudget",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "944dba8e833f0a733693fe4d7cf20e33bbcb6a73488b74e27caf3e1adfe6d06c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeCutBudget:4698",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeCutBudget:4698"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.actualHP_prime_cut_degree_multiplicity",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeCutBudget",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9b07f28504078a7bd4d7c36eced3c6f9681dc8e66b3a2eb9ee12a3c8693f1094",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeCutBudget:2220",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeCutBudget:2220"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.actualHP_regular_sequence",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CompleteIntersectionComponentBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7e9407f17a9e5cc092713d47303e929f19b45a2d5809dc5635affd58c0a9c720",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CompleteIntersectionComponentBound:506",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CompleteIntersectionComponentBound:506"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.actualHP_regular_sequence_natDegree",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CompleteIntersectionComponentBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "478008dc1f0e30ca978b0c3cbbe09b49983e1c4979b1bb435f8b7402944fbf9b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CompleteIntersectionComponentBound:1827",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CompleteIntersectionComponentBound:1827"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.actualHP_top",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HilbertPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4f0c92a2d54f1242d28d3ebbeb17baeb246b11219910f8fb5239b948c620cca6",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HilbertPolynomial:2413",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HilbertPolynomial:2413"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.actualHP_unique",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HilbertPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b7dd77e67e462fa2ec582d64a51106b11bc43de6e45a47fb8581fd73e2b34373",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HilbertPolynomial:1672",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HilbertPolynomial:1672"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.actualHP_zero_natDegree",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousListHistory",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1316ba34ae39f6e94cf6c74f7133bd9abf977a351ad10a6009d612f78ffb9105",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousListHistory:2313",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousListHistory:2313"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.actualLocalLength",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeCutBudget",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0a0954a07e75b7f0bbf654af335634c889721a3279e4de70c75cc64a34b0c317",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeCutBudget:452",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeCutBudget:452"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.actualLocalLength_spec",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeCutBudget",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b32063ae39eb3ff5d09362558fe27e456192d146f9b3d455aee8ab4295dae749",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeCutBudget:701",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeCutBudget:701"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.actualMultiplicity",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertMultiplicityFiltration",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ec368c13cf5d25c394c62100c140e2f9b378bcec2ab786f71334e18d7f6b018c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertMultiplicityFiltration:275",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertMultiplicityFiltration:275"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.actualMultiplicityCycle",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.MultiplicityCycles",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "48e8ea9a499bfd26df6b7a0005b7825f15d6a783b28e2d50026250c39c881a7e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.MultiplicityCycles:361",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.MultiplicityCycles:361"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.actualMultiplicityCycle_coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.MultiplicityCycles",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1713bf3fde0afb15d0c33be15140e85f6b43e7a726440a78f8c6f5a0d36d58f0",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.MultiplicityCycles:812",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.MultiplicityCycles:812"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.actualMultiplicityCycle_cut_degree_le",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.MultiplicityCycles",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aac33dd77af6be1c98027c0bda3ee024773144441e8b1fadb48dc7c36999e06e",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.MultiplicityCycles:7273",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.MultiplicityCycles:7273"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.actualMultiplicityCycle_cut_expansion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.MultiplicityCycles",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "13eb512541e6fcb80770b39eb0c392f5adc920a25125330fc9c389237e96e401",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.MultiplicityCycles:1688",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.MultiplicityCycles:1688"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.actualMultiplicityCycle_parent_budget",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.MultiplicityCycles",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "339d1d95056eda42d42878516b9adfa5134ed893b07454482ca9c40219c5d62c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.MultiplicityCycles:4699",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.MultiplicityCycles:4699"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.actualMultiplicityCycle_zero_degree",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "daa7e05a13efb4e5fffc73a71046c1dbb4fb62f13d74de72c96c64cc68a964c0",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:3962",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:3962"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.actualMultiplicity_congr",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertMultiplicityFiltration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e360a4d70d7673eb64777d7cb54eb1a15b27779e1b7f35736e73c460e69aa9ea",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertMultiplicityFiltration:484",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertMultiplicityFiltration:484"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.actualMultiplicity_cyclic_step",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertMultiplicityFiltration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3c203dab9b3d30d42604a8a9940d3b4ef2fc6c1e46800ca04b9a6b46db69e1c9",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertMultiplicityFiltration:1530",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertMultiplicityFiltration:1530"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.actualMultiplicity_nonneg",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertMultiplicityFiltration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "36d51e8a9ff2bcbecef8ab4d0520b1b0c2f538b9722a8b4ccf6f90d70c20a85f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertMultiplicityFiltration:841",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertMultiplicityFiltration:841"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.actualMultiplicity_regular_sequence",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CompleteIntersectionComponentBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d4a1161b21cf6ec3154d3ff0ae66ba764d42a42f55df5fb5969d4fdf8edbffdf",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CompleteIntersectionComponentBound:2648",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CompleteIntersectionComponentBound:2648"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.actualMultiplicity_top",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertMultiplicityFiltration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "af9817834e2a6042a75527b61fbee016abf301706f6da3240c1d1695a63a37e1",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertMultiplicityFiltration:1252",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertMultiplicityFiltration:1252"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.affine_local_regular_list_bezout",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineLocalRegularBezout",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7babea9363178d2c7812edc746460420a486e227b9d47ad3b1ecf4cf1c6dc4c4",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineLocalRegularBezout:2245",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineLocalRegularBezout:2245"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.component_multiplicity_sum_bound",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ComponentMultiplicitySum",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7b5e11d324c282025bcde037fe58ebd6ce26df8729a56e08b694e7f711520b38",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ComponentMultiplicitySum:1787",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ComponentMultiplicitySum:1787"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.cut_ideal_homogeneous",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.NaturalMultiplicityPropagation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1585dbc5e2cfda6f03e8f0a0262bfd70a1c8072190eb1d3daa29287fd3fa5028",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.NaturalMultiplicityPropagation:760",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.NaturalMultiplicityPropagation:760"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.cyclicFactorEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CyclicPrimeFactor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d229965dd0ac5633f892db9e9a226aba0a239301524cfff1bef47d7015b51a66",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CyclicPrimeFactor:208",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CyclicPrimeFactor:208"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.dehomogenize",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.Homogenization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4083b7b17726a48055ae60d6f6cee6011783a59d38d1dc4cd7df2d78b279d27c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.Homogenization:228",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.Homogenization:228"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.dehomogenize_X_none",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.Homogenization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7bd24cbc6666decaf5363d4440d60de95e1dc85c9cb350e54dc28f9731f58ed8",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.Homogenization:407",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.Homogenization:407"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.dehomogenize_homogenize",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.Homogenization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "20070dbb39555aa61eec8591ac5d6fecea2702001979f48df1e64b230feaf0b4",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.Homogenization:1204",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.Homogenization:1204"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.dehomogenize_rename",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.Homogenization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "90c542014c0c55f7d4c43237a25a0746d55da970b1c0deabfab07cd6f98d75b8",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.Homogenization:550",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.Homogenization:550"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.distinct_selected_factor_weight_le",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ComponentMultiplicitySum",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e65c8eeab54de141f8255fb5fa5b680426831dd6b9a91d8a75edd436f3c3ede9",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ComponentMultiplicitySum:323",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ComponentMultiplicitySum:323"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.exists_homogeneous_component_length_count",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousComponentLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "963b5f1fdd106e3caac8d55aab84ad47840f1a4e045d27823bf4263f54235010",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousComponentLength:2572",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousComponentLength:2572"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.exists_homogeneous_cyclic_filtration_nat",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousComponentLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ecee02a2334a49a2494c7caf94d6ee5a50a4e47fe65e8105b198c690ba2d73c0",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousComponentLength:343",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousComponentLength:343"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.exists_homogeneous_prime_colon",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousPrimeFactor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0fd444376e6d91419399a4d3a090b068b64ad303bd59a433f62299c5448edf25",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousPrimeFactor:1063",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousPrimeFactor:1063"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.exists_homogeneous_prime_filtration",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousPrimeFiltration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b6f8204b13322af0f59440b198fdac2476fc7003f21436eb2703c85339bef1b0",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousPrimeFiltration:1705",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousPrimeFiltration:1705"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.finiteLength_localized_minimal_quotient",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineLocalRegularBezout",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dfeb8768806ce197fa69a7f4f723efb89c69c6ac2edce283d4697c40692fd6c5",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineLocalRegularBezout:1245",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineLocalRegularBezout:1245"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.globalParentCutSum",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedOneCutPropagation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "85ece0cef9e407f732524572d3760afee3ac91127346ae1f63b7796dc8e5e0c8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedOneCutPropagation:341",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedOneCutPropagation:341"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.grouped_count_weighted_sum_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ComponentMultiplicitySum",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c931b2b89ca9c3096b1fc9c710505cb52ba6f0cb0b04b742313df1ff77c3561b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ComponentMultiplicitySum:1260",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ComponentMultiplicitySum:1260"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.homogeneousListPrefix",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousListHistory",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e3dbe76e37e80c6817b354d7aab77b34f6482cf5b94ee20dc3055b670cfc735d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousListHistory:577",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousListHistory:577"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.homogeneousListPrefix_succ",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousListHistory",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2dea8e0ae219244fbff2350a68fbd8dff66643e10ec54ab863272fefc158bbaf",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousListHistory:910",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousListHistory:910"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.homogeneous_colon_singleton",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousPrimeFactor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6d4ed5928ff6f779f72ed61328df942e2be7397ca40b318eb998aa7b1c67c3d4",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousPrimeFactor:440",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousPrimeFactor:440"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.homogeneous_degrees_pos_of_local_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.LocalHomogeneousDegrees",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "58637d90812fbd08403a4471458b75b734f697ce93d118b10b6559bb357e5824",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.LocalHomogeneousDegrees:215",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.LocalHomogeneousDegrees:215"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.homogeneous_list_actual_history",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousListHistory",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c39623fbcaf983ebe12e24bd584c331370a939052a0bc6abb572bf0084af54e8",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousListHistory:6260",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousListHistory:6260"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.homogeneous_local_regular_bezout",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousListHistory",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "79de4fee5c0024861af60625f939b4b1dc3586d63892e59adece72f6d375a4e6",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousListHistory:8738",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousListHistory:8738"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.homogeneous_prefix_hilbert_degree",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousListHistory",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a600a8cc8ff9c83c2192aebc24e1ef251be69c2df1008c7bafc84fa155deb828",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousListHistory:3299",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousListHistory:3299"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.homogenize",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.Homogenization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f7cd58eee6cc97f20f8c239b6558a17ec54a47a85fe66062a3b3b581f0570871",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.Homogenization:948",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.Homogenization:948"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.homogenize_isHomogeneous",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.Homogenization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "23cc83d4e264fd6e2145953b156b1bc9baa165fe455e7af3e087148fbd709c34",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.Homogenization:1483",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.Homogenization:1483"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.ideal_quotient_length_le",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "80e0f5d84227b4a1288cc1fe43019503b6cfe787faf472b0fbd477c5f3903e24",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalLength:437",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalLength:437"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.ideal_quotient_length_le_of_bound",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ca4af348bc737d45171eb6550858e6a8315346cc3374d0d7c8594b67b238bd4e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalLength:603",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalLength:603"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_031.jsonl"
