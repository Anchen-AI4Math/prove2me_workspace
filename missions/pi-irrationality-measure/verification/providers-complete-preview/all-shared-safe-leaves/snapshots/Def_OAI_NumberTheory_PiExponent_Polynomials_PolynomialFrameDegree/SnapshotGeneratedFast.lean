import Lean
import Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_PolynomialFrameDegree

open Lean Meta

namespace PiExponentInterfaceSnapshot

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

-- Keep binder information, constant names, universe levels and de Bruijn
-- indices. Binder display names and source metadata have no kernel meaning.
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

def exportSnapshot (names : Array Name) (output : String) : MetaM Unit := do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for name in names do
    let some ci := env.find? name | throwError "Missing interface declaration: {name}"
    if ci.type.hasMVar || ci.type.hasFVar then
      throwError "The exported declaration type is not closed: {name}"
    let value := match ci with
      | .defnInfo d => some d.value
      | .thmInfo _ => none
      | _ => none
    let typeText ← ppExpr ci.type
    rows := rows.push <| Json.mkObj [
      ("name", toJson name.toString),
      ("levelParams", toJson (ci.levelParams.map Name.toString)),
      ("type", exprJson ci.type),
      ("value", value.map exprJson |>.getD Json.null),
      ("prettyType", toJson typeText.pretty)]
  IO.FS.writeFile output (Json.arr rows |>.compress)

end PiExponentInterfaceSnapshot


namespace PiExponentProviderSnapshot

open Lean Meta

structure ProviderRequest where
  sourceGraphName : String
  expectedUserName : String
  expectedPublicName : String
  expectedModule : String
  expectedKind : String
  sourceWasPrivate : Bool
  commandUnit : String
  declGraphSha256 : String
  declGraphRowSha256 : String

def moduleFor? (env : Environment) (name : Name) : Option Name :=
  match env.getModuleIdxFor? name with
  | some idx => env.header.moduleNames[idx.toNat]?
  | none => none

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
  | .defnInfo d => Json.mkObj [("valueExported", toJson true), ("safety", toJson (reprStr d.safety))]
  | .axiomInfo a => Json.mkObj [("isUnsafe", toJson a.isUnsafe)]
  | .opaqueInfo o => Json.mkObj [("valueExported", toJson false), ("isUnsafe", toJson o.isUnsafe)]
  | .inductInfo i => Json.mkObj [("numParams", toJson i.numParams), ("numIndices", toJson i.numIndices),
      ("all", toJson (i.all.map Name.toString)), ("constructors", toJson (i.ctors.map Name.toString)),
      ("numNested", toJson i.numNested), ("isRecursive", toJson i.isRec),
      ("isUnsafe", toJson i.isUnsafe), ("isReflexive", toJson i.isReflexive)]
  | .ctorInfo c => Json.mkObj [("inductive", toJson c.induct.toString),
      ("constructorIndex", toJson c.cidx), ("numParams", toJson c.numParams),
      ("numFields", toJson c.numFields), ("isUnsafe", toJson c.isUnsafe)]
  | .recInfo r => Json.mkObj [("all", toJson (r.all.map Name.toString)),
      ("numParams", toJson r.numParams), ("numIndices", toJson r.numIndices),
      ("numMotives", toJson r.numMotives), ("numMinors", toJson r.numMinors),
      ("ruleConstructors", toJson (r.rules.map (fun rule => rule.ctor.toString))),
      ("supportsK", toJson r.k), ("isUnsafe", toJson r.isUnsafe)]
  | .quotInfo _ => Json.mkObj []

def isClosed (e : Expr) : Bool :=
  !e.hasMVar && !e.hasFVar && !e.hasLooseBVars

def ownedBy (env : Environment) (name : Name) (expected : String) : Bool :=
  match moduleFor? env name with
  | some moduleName => moduleName.toString == expected
  | none => false

def resolveRequest (env : Environment) (request : ProviderRequest) : MetaM Name := do
  if request.sourceWasPrivate then
    let mut candidates : Array Name := #[]
    for (actualName, _) in env.constants.toList do
      if ownedBy env actualName request.expectedModule then
        if request.sourceWasPrivate then
          if (Lean.privateToUserName? actualName).map Name.toString == some request.expectedUserName then
            candidates := candidates.push actualName
        else if actualName.toString == request.expectedPublicName then
          candidates := candidates.push actualName
    unless candidates.size == 1 do
      throwError "Expected one declaration for source={request.sourceGraphName}, user={request.expectedUserName}, module={request.expectedModule}; found {candidates.size}"
    return candidates[0]!
  else
    unless request.expectedKind == "def" || request.expectedKind == "theorem" do
      throwError "Fast public resolver requires an ordinary theorem or definition"
    let parts := request.expectedPublicName.splitOn "."
    unless parts.all (fun part => !part.isEmpty && part.toList.all (fun c =>
        (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
        (c >= '0' && c <= '9') || c == '_' || c == '\'')) do
      throwError "Fast public resolver rejects quoted or ambiguous names"
    let name := parts.foldl Name.str Name.anonymous
    unless name.toString == request.expectedPublicName do
      throwError "Fast public Name construction does not round-trip"
    unless (Lean.privateToUserName? name).isNone do
      throwError "Fast public resolver found a private kernel name"
    let some _ := env.find? name | throwError "Fast public declaration is absent: {name}"
    unless ownedBy env name request.expectedModule do
      throwError "Fast public declaration has a different actual module owner: {name}"
    return name

def exportProviderSnapshotJsonl (requests : Array ProviderRequest) (output : String) : MetaM Unit := do
  let env ← getEnv
  let handle ← IO.FS.Handle.mk output .write
  for request in requests do
    let name ← resolveRequest env request
    let some ci := env.find? name | throwError "Resolved declaration is absent: {name}"
    let actualKind := envKind ci
    unless actualKind == request.expectedKind do
      throwError "Declaration kind mismatch for {name}: expected={request.expectedKind}, actual={actualKind}"
    unless isClosed ci.type do
      throwError "Declaration type is not closed: {name}"
    let value := match ci with
      | .defnInfo d => some d.value
      | _ => none
    if let some v := value then
      unless isClosed v do
        throwError "Definition value is not closed: {name}"
    let axioms ← Lean.collectAxioms name
    let axiomNames := axioms.toList.map Name.toString
      |>.mergeSort (fun a b => compare a b == .lt)
    let row := Json.mkObj [
      ("schemaVersion", toJson 1),
      ("sourceGraphName", toJson request.sourceGraphName),
      ("resolvedName", toJson name.toString),
      ("resolvedUserName", toJson ((Lean.privateToUserName? name).getD name).toString),
      ("sourceWasPrivate", toJson request.sourceWasPrivate),
      ("resolvedViaPrivateUserNameAndModuleOwner", toJson request.sourceWasPrivate),
      ("module", toJson request.expectedModule),
      ("commandUnit", toJson request.commandUnit),
      ("declGraphSha256", toJson request.declGraphSha256),
      ("declGraphRowSha256", toJson request.declGraphRowSha256),
      ("envKind", toJson actualKind),
      ("levelParams", toJson (ci.levelParams.map Name.toString)),
      ("closedType", toJson true),
      ("closedValue", value.map (fun _ => toJson true) |>.getD Json.null),
      ("type", PiExponentInterfaceSnapshot.exprJson ci.type),
      ("value", value.map PiExponentInterfaceSnapshot.exprJson |>.getD Json.null),
      ("axioms", toJson axiomNames),
      ("kindMetadata", kindMetadata ci)]
    handle.putStrLn row.compress
  handle.flush

end PiExponentProviderSnapshot

open PiExponentProviderSnapshot

def providerRequests : Array ProviderRequest := #[
    { sourceGraphName := "OAI.PiExponentApprox.HasWeightedDegreeLE.mono", expectedUserName := "OAI.PiExponentApprox.HasWeightedDegreeLE.mono", expectedPublicName := "OAI.PiExponentApprox.HasWeightedDegreeLE.mono", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_PolynomialFrameDegree", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:1140", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "de87bff23abf78a87b11fbb58436e33bc87dbd45727852243952e3a9850d4148" },
    { sourceGraphName := "OAI.PiExponentApprox.HasWeightedDegreeLE.add", expectedUserName := "OAI.PiExponentApprox.HasWeightedDegreeLE.add", expectedPublicName := "OAI.PiExponentApprox.HasWeightedDegreeLE.add", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_PolynomialFrameDegree", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:1386", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "103a2bf3155dcd580208d6f8962ac658498056e4d926e0e44b486f3638eeeba4" },
    { sourceGraphName := "OAI.PiExponentApprox.monomialWeight", expectedUserName := "OAI.PiExponentApprox.monomialWeight", expectedPublicName := "OAI.PiExponentApprox.monomialWeight", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_PolynomialFrameDegree", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:174", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "01f36c75bdf6fe96787cba2023e52f0479a6f634b366d2f13e44d10c1c7da5cc" },
    { sourceGraphName := "OAI.PiExponentApprox.HasWeightedDegreeLE.sum", expectedUserName := "OAI.PiExponentApprox.HasWeightedDegreeLE.sum", expectedPublicName := "OAI.PiExponentApprox.HasWeightedDegreeLE.sum", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_PolynomialFrameDegree", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:1754", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "7db2c2a0cc1ed1d981bfcf01cbcfe4e1f3469e9d89a939a79a0885a6667e34a3" },
    { sourceGraphName := "OAI.PiExponentApprox.pderiv_support_shift", expectedUserName := "OAI.PiExponentApprox.pderiv_support_shift", expectedPublicName := "OAI.PiExponentApprox.pderiv_support_shift", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_PolynomialFrameDegree", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:2313", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "53db4743b7904a9d344f0b152696647c811da2f0649a09b2f8107edef92f198c" },
    { sourceGraphName := "OAI.PiExponentApprox.HasWeightedDegreeLE.pderiv", expectedUserName := "OAI.PiExponentApprox.HasWeightedDegreeLE.pderiv", expectedPublicName := "OAI.PiExponentApprox.HasWeightedDegreeLE.pderiv", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_PolynomialFrameDegree", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:2712", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "a7971ed83d60f91a0e034a3b00b4b1daab8a39e227e550671b335f8f5b243b1e" },
    { sourceGraphName := "OAI.PiExponentApprox.HasWeightedDegreeLE", expectedUserName := "OAI.PiExponentApprox.HasWeightedDegreeLE", expectedPublicName := "OAI.PiExponentApprox.HasWeightedDegreeLE", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_PolynomialFrameDegree", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:303", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "3362a18e5d51e6ddf686b09a93ebf6931988c7b35cf5775efb34c0c353216e69" },
    { sourceGraphName := "OAI.PiExponentApprox.HasWeightedDegreeLE.X_mul", expectedUserName := "OAI.PiExponentApprox.HasWeightedDegreeLE.X_mul", expectedPublicName := "OAI.PiExponentApprox.HasWeightedDegreeLE.X_mul", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_PolynomialFrameDegree", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:3146", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "4204ba343dc70a89f4bfb3c10568072d290ddf9f0c32afc73f86dd892c488add" },
    { sourceGraphName := "OAI.PiExponentApprox.HasWeightedDegreeLE.X_mul_pderiv", expectedUserName := "OAI.PiExponentApprox.HasWeightedDegreeLE.X_mul_pderiv", expectedPublicName := "OAI.PiExponentApprox.HasWeightedDegreeLE.X_mul_pderiv", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_PolynomialFrameDegree", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:3692", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "0907538fcbfd918f839157c57d341ae39ab4be378a0eeddc24c6d261a7b3bf61" },
    { sourceGraphName := "OAI.PiExponentApprox.HasWeightedDegreeLE.pderiv_preserves", expectedUserName := "OAI.PiExponentApprox.HasWeightedDegreeLE.pderiv_preserves", expectedPublicName := "OAI.PiExponentApprox.HasWeightedDegreeLE.pderiv_preserves", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_PolynomialFrameDegree", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:4016", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "95981be8a7715db650464fe1909f6e24d79667e6758da0588ff24e8a4864678c" },
    { sourceGraphName := "OAI.PiExponentApprox.monomialWeight_add", expectedUserName := "OAI.PiExponentApprox.monomialWeight_add", expectedPublicName := "OAI.PiExponentApprox.monomialWeight_add", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_PolynomialFrameDegree", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:477", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "4a01e6720c14b43b01d7176658132d60e089d1954571468873d509489497fd31" },
    { sourceGraphName := "OAI.PiExponentApprox.monomialWeight_single", expectedUserName := "OAI.PiExponentApprox.monomialWeight_single", expectedPublicName := "OAI.PiExponentApprox.monomialWeight_single", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_PolynomialFrameDegree", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:750", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "1e5c9f37295eaf2563b9544691aa44de00848fce4eb55c16c75372555547aabc" },
    { sourceGraphName := "OAI.PiExponentApprox.HasWeightedDegreeLE.zero", expectedUserName := "OAI.PiExponentApprox.HasWeightedDegreeLE.zero", expectedPublicName := "OAI.PiExponentApprox.HasWeightedDegreeLE.zero", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_PolynomialFrameDegree", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:954", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "29295d8889b92748852be70073e15298451c39c042e52c92d5b32208fedbd9f3" }
  ]

run_meta do
  exportProviderSnapshotJsonl providerRequests "missions/pi-irrationality-measure/verification/providers-complete-preview/all-shared-safe-leaves/snapshots/Def_OAI_NumberTheory_PiExponent_Polynomials_PolynomialFrameDegree/fast-generated.jsonl"
