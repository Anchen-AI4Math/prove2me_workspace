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
      sourceName := "OAI.PiExponentSiegel.W23.originalLocalCoefficientLocalEquiv_algebraMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4d63e3b349eb6c6669205d6a01195a908d4176957f2b9391d513118d1964da8b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:4051"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.parameterEquivImage_isPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "edae43c6d86b68ea4e6c1853ff57b4e4503bab2b9dda5de70f643094f21d58f2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:9320"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.parameterLocalQuotientForward",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "510c80ce3f40b7808d03dec5e29099452d7762eaca7da314bfc10d3965eb747e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:2651"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.parameterLocalQuotientReverse",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a8317471b7b9d5993b1ec7715cd81d8fa49e15218522d079712f7cb531e0375f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:4427"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.parameterLocalQuotientReverse_algebraMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f5ac8aedd7fba0d2b58e51fda26a76dcacf78426ef9350841b5c86d80e00e59b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:4788"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.parameterLocalQuotient_forward_reverse",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "35f9068a86527a16f5c6f551fa276f77ac082cf7a0f47d750fd5081762fe1020",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:5626"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.parameterLocalQuotient_reverse_forward",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5e23cd4d8471d53fa668b8bb300004ffc6052f408389dc0e6f4280522005d07e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:5074"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.parameterLocalizationMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a3a8c414e68d9a6b3f874dd445f205afbe515e7e82299f7e83f8abc73de087df",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:1459"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.parameterLocalizationMap_algebraMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "90a135a65cc5bcd2335c8ddfd9578108c897b41c3144eec21e847116b2309e10",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:1963"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.parameterLocalizedIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "63d2d7d8a53550d5155266d183b7d76eef4194813e022a215d0138e4231c8ee2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:1255"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.parameterLocalizedIdeal_le_ker",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "71b25a471d17b846eb2d796dd0cc01882daeba43f84b4934a9dddc532dedfd52",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:2257"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.parameterQuotientToLocalQuotient",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "765918af57a0b9d00f0688bf941ae810eadfc8a3f1bf66c273e8ebce968b90ac",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:3217"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.parameterQuotientToLocalQuotient_mk",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "750aa06322a35b38dfadbb3f3e55d7907eae6d0588b7a45943ada9e97cbb8d42",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:3556"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.parameterQuotientToLocalQuotient_units",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fded80f171b42788d0e511697d09b248b71aacf80e7aae7ca042751f5fde4dd8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:3802"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.quotientParameterPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7e4e0bddc95e979014702d1936bd9c36cc0ae69d10441f8c8d575ab09b0a537e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:352"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.quotientParameterPrime_isMaximal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1764f6cbde0995efdd77269e1fd39c44c77b981d8ff66c7d53c25aac262b1559",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:752"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.quotientParameterPrime_isPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0e424dfa48683932074860bd10204d06f57d82ae66fa88ea913e18922e61db9b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:466"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W58.conormalPairing",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.ConormalPairing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "893753096661f009eabbfb3bdb70a20dd50cd1da01536b7a78e9bed912927428",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.ConormalPairing",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.ConormalPairing:954"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.ResidueConormalPairing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ef660977ff90eccb343c6ea9c92ce221f986ecc310fad3449615415cb2a84db9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.ResidueConormalPairing",
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
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.ConormalPairing",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.ConormalPairing:284"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W58.normalRestriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.ConormalPairing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "548a422c1d865f20ba1c3a6d1fef893804bc32e64379ad2def0fac7d85a0563c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.ConormalPairing",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.ConormalPairing:503"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W58.normalRestriction_product_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.ConormalPairing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7fd2bf0d9155845400547cbabffb8bd84c17c793ab8eb479562964296689994e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.ConormalPairing",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.ConormalPairing:736"
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
      sourceName := "OAI.PiExponentSiegel.W58.residueConormalPairing",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.ResidueConormalPairing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "930c8a4d162fe7a77272d4b5904d41c230d4ee70459113967a3dc0701c4891d9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.ResidueConormalPairing",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.ResidueConormalPairing:355"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W09.CoefficientFractionField",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0c10e464383224cc41ab96148ed571324ecfdb428b8eb909f286fcd2655062ff",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization:383"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W09.CoefficientPolynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9eb520de303a53e6759177492c5f1d67b9f5ca6731160e6832140c8546f4ef4a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization:332"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W09.FractionCoefficientPolynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6dc2bd6820f1bd7580f1a38442ae0359729dc98b2b8e17e363cf526ff4d1f238",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization:461"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W09.PolynomialCoefficientLocalization",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f67554d2d58bd4068ce2b99a790a606f8f48f7d0f60bb1753d1d118a9638fc05",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization:744"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W09.SplitPolynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "02702aebe48ac3a2efd613bc24460ea91a8df89e512d359e4ad80f71129f47dc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization:278"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W09.coefficientDenominators",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0b9e2373504ac34a010ff58b496aab6caff86fa63d774c6b7655f94d2ebe3ba3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization:552"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W09.coefficientPolynomial_scalarTower",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "74ca9d53a57302ae9deddfee0665e80c21070e6b4081860c5622fec0604698c7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization:2306"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "def3b5f85fdf96fa2578fa3a20d8d77d1931686667f0c94a894fb53235a9979d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization:2947"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv_X_inl",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fe1b11592ac5c5db5f18c856ea9f7818b650db8c0c6fb2f8644bfe5a17486898",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization:3801"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv_X_inr",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eaf4fa8b7dbf3613a7fe0b9ec0481582e12a1ff2285cbd26171f4a16b65c3a11",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization:4198"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv_algebraMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6f837a7cdc4b4b995afd1a586d60d0971694d6e362563183334666b6832ac5ce",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization:3305"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv_coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "23a15c4bddeeabc29f1fdd3ee22c5443fda04b1556ed501b4045fef76afb61bd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization",
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
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization:1740"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W09.sumAlgEquiv_coefficientRename",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "83ab72322b82b20e40c459366cc91c935e8f0db5365671449fedb2252f1a2dde",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization:1381"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.chain_linear_comp_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0724c1bd150566aacb3038937ed6a444af802ba250c7e0cb731cf2abad2665bb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex:1165"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.comp_zero_of_range_eq_ker",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceResolution",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "95cf7ef8e42224015ceb3a6e93536b6a05c795d80e0394fa29ef748935280fd7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceResolution",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceResolution:1079"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.coneBottom",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceResolution",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cf707dd79aff3e8a7cd557fc104339b93da58cc65efa736d6fd43f53b2f47011",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceResolution",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceResolution:815"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.coneBottom_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b9551d002830a7524caa6d6982648ff967dca64f11cc9244a828ad1fc618cbbd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex:254"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.coneBottom_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceResolution",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bcc3afbda2625e0215afabeed9c85652dbc4e089e4219d2914997906f5d26041",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceResolution",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceResolution:3233"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.coneDifferential",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceResolution",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ef49aa0b99a68f054f3b7eeb69cff05dfb5c0d3c05adee6df371a29bd404ee9c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceResolution",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceResolution:418"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.coneDifferential_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceResolution",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "99bdc0e6a6cee0b5c9cc14e18c61d93fd4c9cce0f6401755c20397b1a7b82b63",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceResolution",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceResolution:1360"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.coneDifferential_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceResolution",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0a3504ea6b53f925a63d03779981deb0ac6eedc7d70ef8a198a73f843ef35c69",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceResolution",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceResolution:1886"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.coneQuotientAugmentation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeQuotientAugmentation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9f481de44027c4ef235a7cf098de48fd960b5515bcddb97d5cdf137324e3f9e6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeQuotientAugmentation",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeQuotientAugmentation:288"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.coneQuotientAugmentation_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeQuotientAugmentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5124019e6467026e1707deeffad9a62cafd4ec3133e76fa935083ddcc6afa731",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeQuotientAugmentation",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeQuotientAugmentation:427"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.coneQuotientAugmentation_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeQuotientAugmentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "37071f17f0a074347c3d02409d54ed88adcb22c9ea268cfe88f4423e4168612c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeQuotientAugmentation",
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
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualBottom",
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
      sourceName := "OAI.PiExponentSiegelAux.W30.dualConeDifferential",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualCone",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2cd1b7dd3e1fe34a07fd6e9d989c13c7ecf0fea6546386ccd47017d8fe240d5c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualCone",
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
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree:372"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.emptyKoszulObject",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4a0d59c8608cf56b8bfe3789f99e2ab4727dae9ea2b97fcca2afc8e46a617e0f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree",
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
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree:507"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.iterateScalarCones_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IteratedKoszulExactness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fc2fcb5807f5efce6d319fdbd1b62beba17cf43b25d8343671e07bc7d1f8de30",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IteratedKoszulExactness",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IteratedKoszulExactness:1382"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.iterateScalarCones_free",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4d87a498141c0907e6d56a827f520cf022630cfa43851c768fd9cfbeda183b45",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree:1562"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.regularSequenceComplex",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "92583dfcc428504861b842a92ba3a3e17559f653c552dce52a2b1a433fb445b8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree:702"
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
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IteratedKoszulExactness",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IteratedKoszulExactness:3852"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.regularSequenceComplex_free",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e04f6f7d2f931c567ca618170eb255f1a31dae6f0a173282021f9c26f4a2d1f7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree:2266"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.scalarConeComplex",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1613e01001989c2192b7ef5ce013cda07c3c2874acbcede53cc703940dd4e6c7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex:1871"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.scalarConeMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c002e086fb4361b6b9e4ab50d7be9196b9512ad0b57aabc1c88511ca361cc497",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex:870"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.scalarConeMap_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ab94807b035f689b0a649d26b906000ba101515456d9fc6d81c247f2133f0f93",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex:1439"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.scalarConeObject",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1528f60c53c57a966b2cb38d463ed23311a949962ca29501956072e53fa4da3b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex:711"
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
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulFiniteFree:830"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.scalarCone_interior_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "81d5c64267b51b2a8df4492ba74eebe8ceeac4b8cf6414104d5775e16aaf5ab5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex:2075"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W30.scalarCone_positive_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IteratedKoszulExactness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3eca91566d588b80722a02dea5f63500274056980e41ab1ef4e5a1e0ff1ff596",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IteratedKoszulExactness",
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
      sourceName := "OAI.PiExponentSiegelAux.W31.moduleFreeResolutionOfExact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFreeResolutionExt",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "17220b50a5f34600f15c43f0bcc1465eec974b61b8a4aeeccd27a175deae3f1e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFreeResolutionExt",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFreeResolutionExt:4244"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W31.module_exactAt_succ_of_range_eq_ker",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFreeResolutionExt",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e2acdbbecb0814833f08fa3a4ccc6a0c002d364bcab1e26ab2b755d1e62ec400",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFreeResolutionExt",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFreeResolutionExt:3108"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W31.projectiveResolutionOfExact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFreeResolutionExt",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "97c184e83f3e9acaaaf70487ef6c6b5c6d29a574d3dba43c0e33007e8f6a2da1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFreeResolutionExt",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFreeResolutionExt:490"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W31.regularSequenceAugmentation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExt",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9f5da1be57d9f6285a97582a611f088dde9de795c2e6ad8b315c40c622e661ee",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExt",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExt:436"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W31.regularSequenceAugmentation_spec",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExt",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8b20999d8597f83a7a7d596cd826ad798ea7b39e377cade1e30878c18ab36fa2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExt",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExt:667"
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
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExt",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExt:1191"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W31.scalarConeTopDualCoordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.KoszulTopDifferential",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "60c790b59c5e1a18ed1fd7661f4838905b5c43f6a6f9b9f097e308e7086aa935",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.KoszulTopDifferential",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.KoszulTopDifferential:640"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W31.scalarConeTopEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulTopTerm",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "90df04f3751bbc699301587f538706ab008c83dc4c958fe33cc54aa89deff47e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulTopTerm",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulTopTerm:265"
    },
    {
      sourceName := "OAI.PiExponentSiegelAux.W31.topDualCoordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.KoszulTopDifferential",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4f0e14f177c9f9221c52c44fbde3765352bdd5fef6359913c2418a1d20bee33d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.KoszulTopDifferential",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.KoszulTopDifferential:267"
    },
    {
      sourceName := "Transcendental.ne_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.VersionCompatibility",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "46d07dfaaa91713041389c3974760e7263c526a750a2e769ff97c9b79dfb9394",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.VersionCompatibility",
      commandUnit := "OAI.NumberTheory.PiExponent.VersionCompatibility:218"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite.0.OAI.PiExponent.CoherentAffineFinite.epi_iso_comp_iso",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2e7b933b89d977e3927823d0261f46902807882107814e3277b0be9dd9cb8d06",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite:215"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite.0.OAI.PiExponent.CoherentAffineFinite.finitePresentation_quasicoherent",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9c09d00f6e3124006c03f90a1698545af15e6f7d425d222a6464749261fb0b52",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite:430"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction.0.OAI.PiExponent.ExceptionalAffineChart.schemeFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "04515d3ff7b9ae5af672f2f3c92d9f7b3c3c4e094ead85ccf0efe6b4ed1cac77",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction:473"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Ampleness.ExceptionalPowerSections.0.OAI.PiExponentSeshadri.Geometry.powerSections",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalPowerSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "73cac839b5ec41c89cb1b9c51370f4414b8bc744135a9a09c5457359ac2da5a9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalPowerSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalPowerSections:4479"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedOpaque.0.OAI.PiExponent.ExceptionalAffineChart.schemeFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedOpaque",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "69c31438936e839e098e8c7f27d15bb0c0f844a217122898f4cd8f8f0c8cc111",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedOpaque",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedOpaque:332"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedTransport.0.OAI.PiExponent.ExceptionalRepresentedTypes.schemeFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedTransport",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3913bb14fb691746d159425f81f51c1a5340aeb391e7a066afaa23428009eae3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedTransport",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedTransport:304"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart.0.OAI.PiExponent.ReesFrozenChart.coordinateInv",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "59e175e7f8508cd454b9476711383f3043c49143314f1a240d158deb2ddd521b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart:1110"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart.0.OAI.PiExponent.ReesFrozenChart.coordinateSpec_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8e113b87ce695abaa39c8081b5e1c91211e17905963b307c2da9307befee1aa3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart:1621"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart.0.OAI.PiExponent.ReesProductPowerSections.instIsOpenImmersionFChartCover",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "955c95fd9066e86445583fa3de13222d483808e465ef36bb819b950b877241cb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart:1847"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Ampleness.ReesRelativeSections.0.OAI.PiExponentSeshadri.ReesGrading.map_comp_through",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesRelativeSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e41eb9a6c7f5e4896656b6b44bccb18b95e722c934fbb4471b96425c35993276",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesRelativeSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesRelativeSections:1961"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Ampleness.ReesRelativeSections.0.OAI.PiExponentSeshadri.ReesGrading.mono_inv_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesRelativeSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "249a64412eaf7f3e3a41e55bb4f81c45370b227773c8e0ade9d7650e2fadb825",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesRelativeSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesRelativeSections:1786"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Ampleness.ReesSectionInclusion.0.OAI.PiExponent.ReesSectionInclusion.chartMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesSectionInclusion",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6e7a18606ccaed5b5665b5c1f64ba96012db5ec389d0e522f195b8e8ad7871a4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesSectionInclusion",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesSectionInclusion:962"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Ampleness.ReesSectionInclusion.0.OAI.PiExponent.ReesSectionInclusion.chartOpenImmersion",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesSectionInclusion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "848c13b126f8db9f0d72c16973b9a821abb2382e26cbf75ce4b018707d94ad16",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesSectionInclusion",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesSectionInclusion:1144"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Ampleness.ReesSheafCanonicalValue.0.OAI.PiExponent.ReesSheafCechRecovery.chartMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesSheafCanonicalValue",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e480762d462723f93bdf9c9068f9837ee6d26e2493262baac3a7587998b5692e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesSheafCanonicalValue",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesSheafCanonicalValue:848"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Ampleness.ReesSheafCanonicalValue.0.OAI.PiExponent.ReesSheafCechRecovery.chartOpenImmersion",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesSheafCanonicalValue",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "579a0509bb8f817287a94eabad7c93590bd55a005f390e77b02d74e1be53ce93",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesSheafCanonicalValue",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesSheafCanonicalValue:1030"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer.0.OAI.PiExponent.ClosedImmersionSerreTransfer.schemeUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0844faf36b4b67df5a2d0deea10e16e922e2d1fbdfee0d90652eb83135e0a683",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer:404"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardAffine.0.OAI.PiExponent.ClosedPushforwardAffine.transportPresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardAffine",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8e43e4ea49ac095ba5643662c92dc415252524a4eda3f03df956d45770f3ba41",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardAffine",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardAffine:404"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardCoherent.0.OAI.PiExponentSeshadri.ClosedPushforward.presentation_transport",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardCoherent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5b5e5ee4b08f2771ee22ac6f812069cfa754c85b4f973acbd91340bc243170de",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardCoherent",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardCoherent:3628"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Approximation.CoherentCokernels.0.OAI.PiExponent.CoherentCokernels.presentationOfIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentCokernels",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "52d1adc8dfbabfb1e74036ee0a6c22db9283c416e9298eafd209650d9e2b7842",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentCokernels",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentCokernels:331"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation.0.OAI.PiExponentSeshadri.Geometry.modulePresheafTensorRestrict_natural_aux",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "17738fe6825a180d8176ed527b3d6d398ce9556a0b827eb280ab576a9766c277",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:6899"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation.0.OAI.PiExponentSeshadri.Geometry.tensorRestrict_natural",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c70e624057237b0d0413ab5a6fd04ae2fd3fdafdb426f1bdfd38bf39da1f02ca",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation:6100"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover.0.OAI.PiExponent.GeneratorsSectionCover.schemeFree",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3a2d3e6b0d8bde0bec8196518c2cc4d02ad9f6c1250fdaddecd4f4eacc993e26",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover:674"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover.0.OAI.PiExponent.GeneratorsSectionCover.schemeInclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7e01df56fed37ed2246deaca73525beb3bbb158799311c7693f4c868c43ad43e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover:773"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Approximation.InverseFrameRestriction.0.OAI.PiExponent.InverseFrames.restrictionMap_cycle",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.InverseFrameRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "058a4dddc8c9bd43224f81c0b1f3b1931286c2c4e1b51e8d89db36fc88c16836",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.InverseFrameRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.InverseFrameRestriction:2713"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Approximation.ModulePullbackCoherent.0.OAI.PiExponentSeshadri.Geometry.presentationOfIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ModulePullbackCoherent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "35f6c5128ba987c7b8f257139b497f4296014cb9bbfe1aef2b3b8f250b674399",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ModulePullbackCoherent",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ModulePullbackCoherent:342"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections.0.OAI.PiExponent.GeometrySupport.PushforwardOpenSections.schemeFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fac25b1df2bc4b51efb4d480f7af5a0e0910f633b2624ae8d461cdb39cd23c31",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections:409"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison.0.OAI.PiExponent.GeometrySupport.PushforwardOpenSections.schemeFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7b2bfa90ec69ade27586842ca4af39fdd136a78dfacee3d1683ad1325bd53797",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison:315"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Approximation.SerreAssembly.0.OAI.PiExponent.GeometrySupport.SerreAssembly.schemeUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SerreAssembly",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "705da5e183d412f09d961afd0f9e399eb51df0b1f52b308190681e9663d3d705",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SerreAssembly",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SerreAssembly:442"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Approximation.TensorPure.0.OAI.PiExponentSeshadri.TensorPure.sectionModule",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c673903c7bdb2df92335a58a3c08212fb769c304b75752d7e8e2a87bc7b889b9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:326"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Approximation.TwistPresentations.0.OAI.PiExponent.GeometrySupport.TwistPresentations.schemeUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "171be4bb8c831f1d388d810afbe69cdf2eada84a0f808805cb430fbc751ca041",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations:374"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair.0.OAI.PiExponent.NumericalAmpleness.CartierEulerPair.iso_middle_comm",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d00e6d7bfd526fb91978d17dac9c9167833e59e0f6b0e63cad55f4d184431793",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair:3435"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite.0.OAI.PiExponent.GeometrySupport.CechExtFinite.schemeFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7fc9703d08cbf36f1e4be8d68b3ff133bc544184d35314a68ebd43495053ef28",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:609"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.freeOpenHomAddCommGroup",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a0fab9aca4b6e7c7b7d56da18cf669e029753b7bda544d4577e098c96b52dc04",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:566"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.schemeFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4224c3b28974312e36fb3c35530b56b31e1b07c9bb09cf6225b5fc4cee0c3f95",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:359"
    },
    {
      sourceName := "_private.OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer.0.OAI.PiExponent.GeometrySupport.CechH1Transfer.schemeUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d98680d7ddf314cebe215b43eeddb2792bf80f506adefce64b1168ed3f42f248",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:467"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_034.jsonl"
