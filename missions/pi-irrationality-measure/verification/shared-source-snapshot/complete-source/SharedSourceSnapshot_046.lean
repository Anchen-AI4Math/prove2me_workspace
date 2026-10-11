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
      sourceName := "OAI.PiExponentSiegel.W23.quotient_module_length_eq_intrinsic",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientLocalizedLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "023334db67b8477959584cf9b3ab791f7df7148f2c7f3b7f9e02518e9cdac2ef",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientLocalizedLength:733",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientLocalizedLength:733"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W58.conormalPairing",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.ConormalPairing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "893753096661f009eabbfb3bdb70a20dd50cd1da01536b7a78e9bed912927428",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.ConormalPairing:954",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.ConormalPairing:954"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W58.constant_linearCombination_mem_ideal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularParameterSelection2",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "23dc55a54be114515b6460e73ccb6849e7d43342c4a5dbdf5e7c1f434e713f79",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularParameterSelection2:1705",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularParameterSelection2:1705"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.ResidueConormalPairing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ef660977ff90eccb343c6ea9c92ce221f986ecc310fad3449615415cb2a84db9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.ResidueConormalPairing:254",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.ResidueConormalPairing:254"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W58.exists_constant_regular_extension",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularParameterAvoidance",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b07cfc95513d55ead06f973ea63ce32c7fd99a31e94aa271fd4bf1beb12918cc",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularParameterAvoidance:1913",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularParameterAvoidance:1913"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W58.exists_constant_regular_parameters_of_no_maximal_associated",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularParameterSelection2",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fc7859a204a6c75a3b5733b44e9e746af8b106224910213f1b24dac82b510d16",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularParameterSelection2:2209",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularParameterSelection2:2209"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W58.ideal_smul_quotient_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.ConormalPairing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "37e47c128faf87ebe280018bf4c965ef92408404d75fe72aea4c34a0c7d59baa",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.ConormalPairing:284",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.ConormalPairing:284"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W58.isSMulRegular_of_avoids_associatedPrimes",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularParameterAvoidance",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ec444f4506ff282d2841084ee678fa6f360491e23dfd434bec8fc0a4f54851a8",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularParameterAvoidance:373",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularParameterAvoidance:373"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W58.normalRestriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.ConormalPairing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "548a422c1d865f20ba1c3a6d1fef893804bc32e64379ad2def0fac7d85a0563c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.ConormalPairing:503",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.ConormalPairing:503"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W58.normalRestriction_product_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.ConormalPairing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7fd2bf0d9155845400547cbabffb8bd84c17c793ab8eb479562964296689994e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.ConormalPairing:736",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.ConormalPairing:736"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W58.polynomialLocal_exists_constant_regular_parameters",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularParameterSelection",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8bacc1f26ac7e338e7262060641e76f0937af48d48761db4fb31de31bf31f4fa",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularParameterSelection:1542",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularParameterSelection:1542"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W58.polynomialLocal_exists_degree_bounded_regular_parameters",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularParameterSelection",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2b45240f0f83075fbd5421752f86cddc6f7aad07db01cdd237e7a4f7b7e17d49",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularParameterSelection:3531",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularParameterSelection:3531"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W58.polynomialLocal_regular_prefix_maximal_not_associated",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularParameterSelection",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "88be2ebb876c9fb3729361cbd60addede177b12b40440035748ce8eac5fa9168",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularParameterSelection:560",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularParameterSelection:560"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W58.regular_append_singleton_of_quotient_smulRegular",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularParameterAvoidance",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "758560168317cf924d79a1b7212368d167bb4f8dea6ed8d5543d9f250d965381",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularParameterAvoidance:913",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularParameterAvoidance:913"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W58.regular_full_length_radical_eq_maximalIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularParameterSelection2",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2c9f882919d789d415594cf95865c503ab1887e27a79e25167fff27e3c4928b0",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularParameterSelection2:411",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularParameterSelection2:411"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W58.residueConormalPairing",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.ResidueConormalPairing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "930c8a4d162fe7a77272d4b5904d41c230d4ee70459113967a3dc0701c4891d9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.ResidueConormalPairing:355",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.ResidueConormalPairing:355"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W58.weaklyRegular_map_of_flat",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialAssociatedLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ccb6f9dac60fb2b993aa1b1d34435cf977c65d9a72713e64df4ccbf61f869f5d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialAssociatedLocalization:667",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialAssociatedLocalization:667"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W09.CoefficientFractionField",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0c10e464383224cc41ab96148ed571324ecfdb428b8eb909f286fcd2655062ff",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization:383",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization:383"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W09.CoefficientPolynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9eb520de303a53e6759177492c5f1d67b9f5ca6731160e6832140c8546f4ef4a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization:332",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization:332"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W09.FractionCoefficientPolynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6dc2bd6820f1bd7580f1a38442ae0359729dc98b2b8e17e363cf526ff4d1f238",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization:461",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization:461"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W09.PolynomialCoefficientLocalization",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f67554d2d58bd4068ce2b99a790a606f8f48f7d0f60bb1753d1d118a9638fc05",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization:744",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization:744"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W09.SplitPolynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "02702aebe48ac3a2efd613bc24460ea91a8df89e512d359e4ad80f71129f47dc",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization:278",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization:278"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W09.coefficientDenominators",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0b9e2373504ac34a010ff58b496aab6caff86fa63d774c6b7655f94d2ebe3ba3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization:552",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization:552"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W09.coefficientPolynomial_scalarTower",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "74ca9d53a57302ae9deddfee0665e80c21070e6b4081860c5622fec0604698c7",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization:2306",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization:2306"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "def3b5f85fdf96fa2578fa3a20d8d77d1931686667f0c94a894fb53235a9979d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization:2947",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization:2947"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv_X_inl",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fe1b11592ac5c5db5f18c856ea9f7818b650db8c0c6fb2f8644bfe5a17486898",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization:3801",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization:3801"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv_X_inr",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eaf4fa8b7dbf3613a7fe0b9ec0481582e12a1ff2285cbd26171f4a16b65c3a11",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization:4198",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization:4198"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv_algebraMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6f837a7cdc4b4b995afd1a586d60d0971694d6e362563183334666b6832ac5ce",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization:3305",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization:3305"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv_coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "23a15c4bddeeabc29f1fdd3ee22c5443fda04b1556ed501b4045fef76afb61bd",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization:4702",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization:4702"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W09.polynomialMaximal_height",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialMaximalHeight",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cb8aa2d528c8a8400437b55439cfb4c0f34fd64e445b2aa3be97d7b3c7b9ff7c",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialMaximalHeight:250",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialMaximalHeight:250"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W09.sumAlgEquiv_coefficientDenominators",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e4e9c2694d073b6eaaabce2126f30c1b6c62b0cb63b1ba93f9be2ce5507108cb",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization:1740",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization:1740"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W09.sumAlgEquiv_coefficientRename",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "83ab72322b82b20e40c459366cc91c935e8f0db5365671449fedb2252f1a2dde",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization:1381",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization:1381"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.chain_dual_comp_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualStep",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ad18e5682fcf0d770ea8131bd24183398bc7bf85f15aa48f807db67f517630b8",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualStep:251",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualStep:251"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.chain_linear_comp_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0724c1bd150566aacb3038937ed6a444af802ba250c7e0cb731cf2abad2665bb",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex:1165",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex:1165"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.comp_zero_of_range_eq_ker",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceResolution",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "95cf7ef8e42224015ceb3a6e93536b6a05c795d80e0394fa29ef748935280fd7",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceResolution:1079",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceResolution:1079"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.coneBottom",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceResolution",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cf707dd79aff3e8a7cd557fc104339b93da58cc65efa736d6fd43f53b2f47011",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceResolution:815",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceResolution:815"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.coneBottom_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b9551d002830a7524caa6d6982648ff967dca64f11cc9244a828ad1fc618cbbd",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex:254",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex:254"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.coneBottom_dual_equiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualBottom",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "86ce0911911e18733ed3e15539168478024a8d46c8795dbd045d9f95734b79ae",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualBottom:576",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualBottom:576"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.coneBottom_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceResolution",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bcc3afbda2625e0215afabeed9c85652dbc4e089e4219d2914997906f5d26041",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceResolution:3233",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceResolution:3233"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.coneBottom_range_eq_sup",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceAugmentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "abc70b779c6b8f3994da5d755acdef2e0ef1a7b800e1a1617237403bcb192e55",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceAugmentation:228",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceAugmentation:228"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.coneDifferential",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceResolution",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ef49aa0b99a68f054f3b7eeb69cff05dfb5c0d3c05adee6df371a29bd404ee9c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceResolution:418",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceResolution:418"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.coneDifferential_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceResolution",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "99bdc0e6a6cee0b5c9cc14e18c61d93fd4c9cce0f6401755c20397b1a7b82b63",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceResolution:1360",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceResolution:1360"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.coneDifferential_dual_equiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualCone",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "867e603a198ca1ffcab7ba0a5448dd95858c8cd079b42c481b752ef6ada15159",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualCone:1363",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualCone:1363"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.coneDifferential_dual_precomposition",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualCone",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "58b50373925e77c9232e84eafd700961512980cae6651726776c9b8c6ded7312",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualCone:849",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualCone:849"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.coneDifferential_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceResolution",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0a3504ea6b53f925a63d03779981deb0ac6eedc7d70ef8a198a73f843ef35c69",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceResolution:1886",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceResolution:1886"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.coneQuotientAugmentation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeQuotientAugmentation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9f481de44027c4ef235a7cf098de48fd960b5515bcddb97d5cdf137324e3f9e6",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeQuotientAugmentation:288",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeQuotientAugmentation:288"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.coneQuotientAugmentation_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeQuotientAugmentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5124019e6467026e1707deeffad9a62cafd4ec3133e76fa935083ddcc6afa731",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeQuotientAugmentation:427",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeQuotientAugmentation:427"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.coneQuotientAugmentation_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeQuotientAugmentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "37071f17f0a074347c3d02409d54ed88adcb22c9ea268cfe88f4423e4168612c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeQuotientAugmentation:1770",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeQuotientAugmentation:1770"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.coordinate_quotient_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualInitial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0011cc1f3ae9b40e99ee06ab10c92c42a29737ba9fddb2b7bc35dad1b1c9f9a9",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualInitial:528",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualInitial:528"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.dualConeBottom",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualBottom",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "288ae119f03d963c561080b4debed829905cf4540f86ffc2bbd9f028ff41160a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualBottom:291",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualBottom:291"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.dualConeBottom_endpoint_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualBottom",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c32e307cf0651f3125fe93b152cf15e25e4750c5a9d27d2560682f55b5e9ce6a",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualBottom:2297",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualBottom:2297"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.dualConeBottom_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualBottom",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b97cfcbdbb27188445a47a45571b8b370ce2e6dcb24a9c71cfe1aaf2e2a252bb",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualBottom:910",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualBottom:910"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.dualConeBottom_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualBottom",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "379d4880b8e89fe4d5e4872be75a7e0ad0191702e9a1d62f03854924a1393e36",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualBottom:1876",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualBottom:1876"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.dualConeBottom_injective_of_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualBottom",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "faf5838cd311c0a478f808d1cb624b1f8f346b2513c4792434b981eb0dd5f690",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualBottom:2084",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualBottom:2084"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.dualConeDifferential",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualCone",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2cd1b7dd3e1fe34a07fd6e9d989c13c7ecf0fea6546386ccd47017d8fe240d5c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualCone:371",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualCone:371"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.dualConeDifferential_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualCone",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8f8c044c1ee9fa2f5236dbec2d4ddddbccaec48bf68b8d728d84d184711fe8dd",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualCone:1739",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualCone:1739"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.dualCone_endpoint_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualEndpoint",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ecf8ab8d97113adf93d1e2c9ed7c2fc967fd7a05e5fdb70ed8827c1ac55a2bcc",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualEndpoint:360",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualEndpoint:360"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.emptyKoszulComplex",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f283e359cd346e61b5e0cf5c9d94721c361fbba8226ebdbf47bb7257453070b4",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree:372",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree:372"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.emptyKoszulObject",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4a0d59c8608cf56b8bfe3789f99e2ab4727dae9ea2b97fcca2afc8e46a617e0f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree:251",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree:251"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.exact_of_equivalences",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualTransport",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f0e6ad2fd3183fc35f4085d674e4621b333f04e6c932e3299ec979bb67233da6",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualTransport:472",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualTransport:472"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.iterateScalarCones",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0b01ce4e2d6794e5ae5ee45bb47af5ddebde50e360d5dd9dee8fe3fd1de6a939",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree:507",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree:507"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.iterateScalarCones_bounded",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulBounded",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8acade7c1de7187b37a64ed30641bb15e12f03617eef9541b250a6a4db0be388",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulBounded:605",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulBounded:605"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.iterateScalarCones_dual_low_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceDualExactness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "93f161c5bdf043ad155717ee834d9268432dca11be5da735a6ef0f02f126bf36",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceDualExactness:371",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceDualExactness:371"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.iterateScalarCones_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IteratedKoszulExactness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fc2fcb5807f5efce6d319fdbd1b62beba17cf43b25d8343671e07bc7d1f8de30",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IteratedKoszulExactness:1382",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IteratedKoszulExactness:1382"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.iterateScalarCones_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "53298787a3df4849271ae9f8bc1ee30f2db3d0b0619150ba2158b484f46cf124",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree:1907",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree:1907"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.iterateScalarCones_free",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4d87a498141c0907e6d56a827f520cf022630cfa43851c768fd9cfbeda183b45",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree:1562",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree:1562"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.polynomialLocal_residueExt_below_height",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialLocalLowExt",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "df809d43a6730501f7c71c1e2143431eeb51a643984481aaadd6541028ca31ca",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialLocalLowExt:287",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialLocalLowExt:287"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.quotient_dual_eq_zero_of_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceHomZero",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "92c53d7a5dc41b88951de4bc9dece81115d5016863590c4dd3f58b4c78cec9e3",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceHomZero:195",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceHomZero:195"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.range_comp_eq_of_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulTopAugmentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d642c8d9cbb7b9e83dbe471217e2eb9c877f9ddb706f947a36f442d3a76ec78e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulTopAugmentation:362",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulTopAugmentation:362"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.regularSequenceComplex",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "92583dfcc428504861b842a92ba3a3e17559f653c552dce52a2b1a433fb445b8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree:702",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree:702"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.regularSequenceComplex_bounded",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulBounded",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f76abd1e5136f644888764a7667d4c25f63c42a3648d9e9e1006efb5c0501242",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulBounded:1095",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulBounded:1095"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.regularSequenceComplex_dual_low_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceDualExactness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "18f19afe36aab7b2fccc9b6bdd2a971f2e612390b8b809d915ca59325b6ee8a8",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceDualExactness:2741",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceDualExactness:2741"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.regularSequenceComplex_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IteratedKoszulExactness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6f73b0e8f77c9ee75d05fd3d37cc02a3bb663d40385356a3d3636bc5da776cd8",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IteratedKoszulExactness:3852",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IteratedKoszulExactness:3852"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.regularSequenceComplex_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3cc92e63da636bb8c2a74af793b5e39001da1e3e6bad7a6a4541986fdfe1f7e5",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree:2596",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree:2596"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.regularSequenceComplex_free",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e04f6f7d2f931c567ca618170eb255f1a31dae6f0a173282021f9c26f4a2d1f7",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree:2266",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree:2266"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.regularSequenceQuotientExt_below_length",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceLowExt",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e9749880f28015acfd5ef56c614cb31524ccc7a04461bb384744889a7e213be4",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceLowExt:1156",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceLowExt:1156"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.regularSequenceQuotientExt_positive_below_length",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceLowExt",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d92a51a4cd1fa3c92430094bb066fe7af4dc01b87810e3fa1bc7c4c8e6e1639f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceLowExt:389",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceLowExt:389"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.regularSequenceQuotientExt_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceLowExt",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7f50bd42463c3d1ff3c7e90d5d25272dbce3e57762bb0c8a02be165ff89d7383",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceLowExt:760",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceLowExt:760"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.regularSequenceQuotient_dual_subsingleton",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceHomZero",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4718c92b2131699447fdeb5167b24a448dd097d964cf93bb4d73458107461391",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceHomZero:786",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceHomZero:786"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.regular_on_dual",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualInitial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c3a446796c9b451058f84991a760d56c1c2c023cf43c3c0ef50eda71f154900f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualInitial:317",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualInitial:317"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.residueFieldExt_below_regular_length",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceLowExt",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "229cefd93713fc911b2d7173904636ebe68c68508d6c4145134102f6e615fef9",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceLowExt:1591",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceLowExt:1591"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.scalarConeComplex",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1613e01001989c2192b7ef5ce013cda07c3c2874acbcede53cc703940dd4e6c7",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex:1871",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex:1871"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.scalarConeMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c002e086fb4361b6b9e4ab50d7be9196b9512ad0b57aabc1c88511ca361cc497",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex:870",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex:870"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.scalarConeMap_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ab94807b035f689b0a649d26b906000ba101515456d9fc6d81c247f2133f0f93",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex:1439",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex:1439"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.scalarConeObject",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1528f60c53c57a966b2cb38d463ed23311a949962ca29501956072e53fa4da3b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex:711",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex:711"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.scalarCone_bounded",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulBounded",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9fdfeffae74f593ede00b5d5369e3d8f92a497bb6beefe30267e8f999c1fbe5d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulBounded:193",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulBounded:193"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.scalarCone_dual_endpoint_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualStep",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "64f383a776ca5a6c89770d73288e07dbdabedea1f3e1e28ca03ca4a88de91cda",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualStep:703",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualStep:703"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.scalarCone_dual_interior_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualTransport",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2b8c4953c64b814a4240e66f28f462d8bf397572066c938b0b8887e3bf0e5629",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualTransport:1759",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualTransport:1759"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.scalarCone_dual_low_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualStep",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "25daa50daf489d5e3ad029564ca92056124ebb793c2a0f8b449e81bbf21b710a",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualStep:3795",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualStep:3795"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.scalarCone_dual_one_endpoint_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualStep",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f02f0af002a4670bdf6088615caa3aa7487c312b7406b15787f7d6d28d75c277",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualStep:2435",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualStep:2435"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.scalarCone_dual_one_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualBottom",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "437b820024d0aaa73c20d9817e98c73f95c7f01bf27389b008f702338e9a2af3",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualBottom:3695",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualBottom:3695"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.scalarCone_dual_zero_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualInitial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "657919bc3431ae1f64397a201f693c39e709f809e040083bdb9730554df4231c",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualInitial:2161",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualInitial:2161"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.scalarCone_dual_zero_injective_of_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualInitial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f989b57a3d781db9a141eb7c2a26b13df04594e0e14499244c2d9b21dfd6526e",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualInitial:1312",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualInitial:1312"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.scalarCone_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "04d96dfa669ba080316f6cfe9f33ebf8989d57b5c014d6ec9dde4f603d071348",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree:1188",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree:1188"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.scalarCone_first_top_dual_image",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualInitial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a5f1c6d6671adec41d8441978079b40f03ecbbe46afe5dd6e9d2c4668fd549f5",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualInitial:3000",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualInitial:3000"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.scalarCone_free",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f0182bd339fe825ec69eb6fe4337b67c1d347246ec3850cf0ba6ca3396892d1d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree:830",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree:830"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.scalarCone_interior_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "81d5c64267b51b2a8df4492ba74eebe8ceeac4b8cf6414104d5775e16aaf5ab5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex:2075",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex:2075"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.scalarCone_positive_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IteratedKoszulExactness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3eca91566d588b80722a02dea5f63500274056980e41ab1ef4e5a1e0ff1ff596",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IteratedKoszulExactness:241",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IteratedKoszulExactness:241"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.scalarCone_top_dual_image",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulTopAugmentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "caf9edaf650e1175fb062023cbbc3532c6c6d8435132d3df84449a5e4f487c26",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulTopAugmentation:1658",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulTopAugmentation:1658"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.scalar_sub_range",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulTopAugmentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "23a059085f2d31731242bc23e442c0060547909600db6334732e5bb4fbc627ce",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulTopAugmentation:687",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulTopAugmentation:687"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W31.ext_subsingleton_iff_cocycles_are_boundaries",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFreeResolutionExt",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "17c94ff38024eaf7ddddc25c0f1921af10c9d2e3f570f58dd83393ba8ccdb4fa",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFreeResolutionExt:2038",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFreeResolutionExt:2038"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W31.ext_subsingleton_of_finite_basis",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFreeExtTransfer",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0183340a82371472761f37abd35b8aa53edc6d630017520cb04f598d71671e99",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFreeExtTransfer:1240",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFreeExtTransfer:1240"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W31.ext_subsingleton_of_finite_free",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFreeExtTransfer",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "12fb77c466e201767367971f089e2766e1089520db854b3254e6a2abbb5ddfa1",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFreeExtTransfer:1977",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFreeExtTransfer:1977"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W31.ext_subsingleton_of_finite_identity_factorization",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFreeExtTransfer",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bd1a661d1af6b1ab17c6868a0748ae95b5011b4cf283609f19605430db9e71d1",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFreeExtTransfer:374",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFreeExtTransfer:374"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W31.moduleFreeResolutionOfExact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFreeResolutionExt",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "17220b50a5f34600f15c43f0bcc1465eec974b61b8a4aeeccd27a175deae3f1e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFreeResolutionExt:4244",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFreeResolutionExt:4244"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W31.module_exactAt_succ_of_range_eq_ker",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFreeResolutionExt",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e2acdbbecb0814833f08fa3a4ccc6a0c002d364bcab1e26ab2b755d1e62ec400",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFreeResolutionExt:3108",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFreeResolutionExt:3108"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W31.projectiveResolutionOfExact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFreeResolutionExt",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "97c184e83f3e9acaaaf70487ef6c6b5c6d29a574d3dba43c0e33007e8f6a2da1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFreeResolutionExt:490",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFreeResolutionExt:490"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W31.regularSequenceAugmentation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExt",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9f5da1be57d9f6285a97582a611f088dde9de795c2e6ad8b315c40c622e661ee",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExt:436",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExt:436"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W31.regularSequenceAugmentation_spec",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExt",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8b20999d8597f83a7a7d596cd826ad798ea7b39e377cade1e30878c18ab36fa2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExt:667",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExt:667"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W31.regularSequenceQuotientExt_iff_boundaries",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExt",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2e9eae606b01ad936dfa6fab9d642c2ba181774494044df27a8bfead1d74618a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExt:2503",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExt:2503"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W31.regularSequenceQuotientExt_of_dual_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExt",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1d22e966ff73ce45c42ee49baa7873cedbca710fb21370ef653cc57a8b0bff2f",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExt:3577",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExt:3577"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W31.regularSequenceResolution",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExt",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "666f7bcb92083bb3dd9aeab9ab58d44b929531a217cee2cceb9b707e99713964",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExt:1191",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExt:1191"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W31.scalarConeFirstTopBoundary_eval",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.KoszulTopDifferential",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d5b0a8e72f36f94553983874d3e0f131ef174925e2068a89e8a691966066aa5f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.KoszulTopDifferential:2621",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.KoszulTopDifferential:2621"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W31.scalarConeTopBoundary_eval",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.KoszulTopDifferential",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "43fdd336258a7ccb79c80be0301c08243b05a9a08c872de384bc3341dfc29bde",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.KoszulTopDifferential:1298",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.KoszulTopDifferential:1298"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W31.scalarConeTopDualCoordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.KoszulTopDifferential",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "60c790b59c5e1a18ed1fd7661f4838905b5c43f6a6f9b9f097e308e7086aa935",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.KoszulTopDifferential:640",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.KoszulTopDifferential:640"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W31.scalarConeTopDualCoordinate_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.KoszulTopDifferential",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "daf53a7c619216edcdb641a36d7f816ba793e96f65fde921120e9e5f61d42c6c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.KoszulTopDifferential:958",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.KoszulTopDifferential:958"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W31.scalarConeTopDualCoordinate_boundary",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.KoszulTopDifferential",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d66610356e0d7825912546576ac18a0666b89df45eaa57e8715a0f04f44f344a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.KoszulTopDifferential:2000",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.KoszulTopDifferential:2000"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W31.scalarConeTopEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulTopTerm",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "90df04f3751bbc699301587f538706ab008c83dc4c958fe33cc54aa89deff47e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulTopTerm:265",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulTopTerm:265"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W31.topDualCoordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.KoszulTopDifferential",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4f0e14f177c9f9221c52c44fbde3765352bdd5fef6359913c2418a1d20bee33d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.KoszulTopDifferential:267",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.KoszulTopDifferential:267"
    },
    {
      sourceName := "Transcendental.ne_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.VersionCompatibility",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "46d07dfaaa91713041389c3974760e7263c526a750a2e769ff97c9b79dfb9394",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.VersionCompatibility:218",
      commandUnit := "OAI.NumberTheory.PiExponent.VersionCompatibility:218"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite.0.OAI.PiExponent.CoherentAffineFinite.epi_iso_comp_iso",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2e7b933b89d977e3927823d0261f46902807882107814e3277b0be9dd9cb8d06",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite:215",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite:215"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite.0.OAI.PiExponent.CoherentAffineFinite.finitePresentation_quasicoherent",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9c09d00f6e3124006c03f90a1698545af15e6f7d425d222a6464749261fb0b52",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite:430",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite:430"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction.0.OAI.PiExponent.ExceptionalAffineChart.schemeFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "04515d3ff7b9ae5af672f2f3c92d9f7b3c3c4e094ead85ccf0efe6b4ed1cac77",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction:473",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction:473"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Ampleness.ExceptionalPowerSections.0.OAI.PiExponentSeshadri.Geometry.powerSections",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalPowerSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "73cac839b5ec41c89cb1b9c51370f4414b8bc744135a9a09c5457359ac2da5a9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalPowerSections:4479",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalPowerSections:4479"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedOpaque.0.OAI.PiExponent.ExceptionalAffineChart.schemeFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedOpaque",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "69c31438936e839e098e8c7f27d15bb0c0f844a217122898f4cd8f8f0c8cc111",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedOpaque:332",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedOpaque:332"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedTransport.0.OAI.PiExponent.ExceptionalRepresentedTypes.schemeFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedTransport",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3913bb14fb691746d159425f81f51c1a5340aeb391e7a066afaa23428009eae3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedTransport:304",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedTransport:304"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Ampleness.FiniteReesComparison.0.OAI.PiExponent.GeometrySupport.ExceptionalRecoveryMap.intersection_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.FiniteReesComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "82ff8716c3fd4d918ea1bffde559547314671414bcd4ac351598b3a130281767",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.FiniteReesComparison:709",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.FiniteReesComparison:709"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Ampleness.FiniteReesComparison.0.OAI.PiExponent.GeometrySupport.ExceptionalRecoveryMap.intersection_two",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.FiniteReesComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5c38dff6b4a3e027a2a332eafe5141f167a4da26d057cbfbf6095727d8948dff",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.FiniteReesComparison:969",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.FiniteReesComparison:969"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_046.jsonl"
