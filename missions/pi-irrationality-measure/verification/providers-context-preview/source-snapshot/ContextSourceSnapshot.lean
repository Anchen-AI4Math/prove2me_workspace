import Lean
import OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame
import OAI.NumberTheory.PiExponent.Jets.JetGeometry
import OAI.NumberTheory.PiExponent.Jets.FormalJetDerivatives
import OAI.NumberTheory.PiExponent.Jets.FormalLogJet

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
    unless axiomNames.all (fun n => n == "propext" || n == "Classical.choice" || n == "Quot.sound") do
      throwError "Source-fast CI contains nonstandard axioms: {name}"
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
    { sourceGraphName := "OAI.PiExponentApprox.logarithmicDerivation_apply", expectedUserName := "OAI.PiExponentApprox.logarithmicDerivation_apply", expectedPublicName := "OAI.PiExponentApprox.logarithmicDerivation_apply", expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame:1247", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "44308d461dc12c26d81543e8361de71f41726114d908db62bf0b96b0583f882d" },
    { sourceGraphName := "OAI.PiExponentApprox.polynomialFrame_zero", expectedUserName := "OAI.PiExponentApprox.polynomialFrame_zero", expectedPublicName := "OAI.PiExponentApprox.polynomialFrame_zero", expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame:1619", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "5102f453d803051bfc1f7c2564095dd8b1d44bbea298b999fb5c9ad81b00d354" },
    { sourceGraphName := "OAI.PiExponentApprox.polynomialFrame_pos", expectedUserName := "OAI.PiExponentApprox.polynomialFrame_pos", expectedPublicName := "OAI.PiExponentApprox.polynomialFrame_pos", expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame:1769", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "874dc525cd8f3a3f800dcc303118b7d42d6b211c33107df999e0474625d20317" },
    { sourceGraphName := "OAI.PiExponentApprox.FramePolynomial", expectedUserName := "OAI.PiExponentApprox.FramePolynomial", expectedPublicName := "OAI.PiExponentApprox.FramePolynomial", expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame:251", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "d88fadc83b3ac8ead76e1aff1472aa2752c2a572d8d01766f330be8a2af8e327" },
    { sourceGraphName := "OAI.PiExponentApprox.logarithmicDerivation", expectedUserName := "OAI.PiExponentApprox.logarithmicDerivation", expectedPublicName := "OAI.PiExponentApprox.logarithmicDerivation", expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame:321", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "fce7b3723cd7851ac8c95509a236c0370596ceb10d3d35eceb636b1d4ccccd2d" },
    { sourceGraphName := "OAI.PiExponentApprox.HasWeightedDegreeLE.logarithmicDerivation", expectedUserName := "OAI.PiExponentApprox.HasWeightedDegreeLE.logarithmicDerivation", expectedPublicName := "OAI.PiExponentApprox.HasWeightedDegreeLE.logarithmicDerivation", expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame:4904", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "2233f4681383889a2b8dc3605e4c7e0f4181afb66f47f3d265ef3f42e1cbc84a" },
    { sourceGraphName := "OAI.PiExponentApprox.HasWeightedDegreeLE.polynomialFrame", expectedUserName := "OAI.PiExponentApprox.HasWeightedDegreeLE.polynomialFrame", expectedPublicName := "OAI.PiExponentApprox.HasWeightedDegreeLE.polynomialFrame", expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame:5349", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "d268c61710b80ca9c77d4f64ec28f9804572b5e4933188e87a3cb8a3982f0ca1" },
    { sourceGraphName := "OAI.PiExponentApprox.polynomialFrameWord", expectedUserName := "OAI.PiExponentApprox.polynomialFrameWord", expectedPublicName := "OAI.PiExponentApprox.polynomialFrameWord", expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame:5814", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "fb40371d38df407c3065224bf9705ad4f52f6d2e088eb1274cadbb4f084d67d7" },
    { sourceGraphName := "OAI.PiExponentApprox.polynomialFrame", expectedUserName := "OAI.PiExponentApprox.polynomialFrame", expectedPublicName := "OAI.PiExponentApprox.polynomialFrame", expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame:601", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "4fce4c5386239239ef3c8e18c9f6fe72406fc4ce79b0b88769ea2d9d88f9ca1f" },
    { sourceGraphName := "OAI.PiExponentApprox.HasWeightedDegreeLE.polynomialFrameWord", expectedUserName := "OAI.PiExponentApprox.HasWeightedDegreeLE.polynomialFrameWord", expectedPublicName := "OAI.PiExponentApprox.HasWeightedDegreeLE.polynomialFrameWord", expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame:6761", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "4147ad07ab40f8b23f07588be788c83977c31e39767e6728e8f8629cf62c3d87" },
    { sourceGraphName := "OAI.PiExponentApprox.derivation_finset_sum_apply", expectedUserName := "OAI.PiExponentApprox.derivation_finset_sum_apply", expectedPublicName := "OAI.PiExponentApprox.derivation_finset_sum_apply", expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame:785", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "0395f07cd3bc4210efafa19ac17b4937adcfc3669bd3b53a8ffa316c5a2d9c1c" },
    { sourceGraphName := "OAI.PiExponent.JetGeometry.weightedIdeal_mul_le", expectedUserName := "OAI.PiExponent.JetGeometry.weightedIdeal_mul_le", expectedPublicName := "OAI.PiExponent.JetGeometry.weightedIdeal_mul_le", expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetGeometry", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:1210", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "7b28b25164269ba9da07688fa8f7f6924c579c837cd203342102db1b73a85109" },
    { sourceGraphName := "OAI.PiExponent.JetGeometry.ideal_pow_le_weightedIdeal", expectedUserName := "OAI.PiExponent.JetGeometry.ideal_pow_le_weightedIdeal", expectedPublicName := "OAI.PiExponent.JetGeometry.ideal_pow_le_weightedIdeal", expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetGeometry", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:1576", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "bad24716e0a034c49b54be6f2762c3f73e93ea0d27285741e6698f6347e99ded" },
    { sourceGraphName := "OAI.PiExponent.JetGeometry.coordinatePowerIdeal", expectedUserName := "OAI.PiExponent.JetGeometry.coordinatePowerIdeal", expectedPublicName := "OAI.PiExponent.JetGeometry.coordinatePowerIdeal", expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetGeometry", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:2101", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "a575c534cf80c72e21edf89cc1a60779c22fbe299dc74757e16986cb381a2837" },
    { sourceGraphName := "OAI.PiExponent.JetGeometry.weightedIdeal", expectedUserName := "OAI.PiExponent.JetGeometry.weightedIdeal", expectedPublicName := "OAI.PiExponent.JetGeometry.weightedIdeal", expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetGeometry", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:242", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "8cb1a802cafb0361ff351c30d8a45bdc4f5754650412adba9ab385e0e0c77dfe" },
    { sourceGraphName := "OAI.PiExponent.JetGeometry.rational_weight_nonneg", expectedUserName := "OAI.PiExponent.JetGeometry.rational_weight_nonneg", expectedPublicName := "OAI.PiExponent.JetGeometry.rational_weight_nonneg", expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetGeometry", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:5300", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "145957c9d66989b99ab728b31a34ee27799f9bb04055753d99285b284d44e7a5" },
    { sourceGraphName := "OAI.PiExponent.JetGeometry.rationalWeightedIdeal", expectedUserName := "OAI.PiExponent.JetGeometry.rationalWeightedIdeal", expectedPublicName := "OAI.PiExponent.JetGeometry.rationalWeightedIdeal", expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetGeometry", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:5541", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "32e325a1c11e414b39019959f83051c27016287422cee716bcace50a5a3535ab" },
    { sourceGraphName := "OAI.PiExponent.JetGeometry.rationalWeightedIdeal_mul_le", expectedUserName := "OAI.PiExponent.JetGeometry.rationalWeightedIdeal_mul_le", expectedPublicName := "OAI.PiExponent.JetGeometry.rationalWeightedIdeal_mul_le", expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetGeometry", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:6508", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "c7a70188525fc890c67a077bfec446ceb268773749dff6cd2e91ee7fb209a3cf" },
    { sourceGraphName := "OAI.PiExponent.JetGeometry.ideal_pow_le_rationalWeightedIdeal", expectedUserName := "OAI.PiExponent.JetGeometry.ideal_pow_le_rationalWeightedIdeal", expectedPublicName := "OAI.PiExponent.JetGeometry.ideal_pow_le_rationalWeightedIdeal", expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetGeometry", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:7291", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "c640e38a19b84b7b3073d3f47da7aa8542cba885f95fceac250dc1233cb68f87" },
    { sourceGraphName := "OAI.PiExponent.JetGeometry.mem_weightedIdeal_iff", expectedUserName := "OAI.PiExponent.JetGeometry.mem_weightedIdeal_iff", expectedPublicName := "OAI.PiExponent.JetGeometry.mem_weightedIdeal_iff", expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetGeometry", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:794", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "adfff4f12f12cf3f5cee56068b4704be75f9f9d863f85129bad549fe61295ba7" },
    { sourceGraphName := "OAI.PiExponent.JetGeometry.RationalCoefficientPacket", expectedUserName := "OAI.PiExponent.JetGeometry.RationalCoefficientPacket", expectedPublicName := "OAI.PiExponent.JetGeometry.RationalCoefficientPacket", expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetGeometry", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:8569", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "f2f3b033afc8e54fd7366ac8149e75168d90ecc52f2f99aeadf8bba381de2d7a" },
    { sourceGraphName := "OAI.PiExponent.JetGeometry.rationalCoefficientPacket", expectedUserName := "OAI.PiExponent.JetGeometry.rationalCoefficientPacket", expectedPublicName := "OAI.PiExponent.JetGeometry.rationalCoefficientPacket", expectedModule := "OAI.NumberTheory.PiExponent.Jets.JetGeometry", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:8687", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "6b635bdb7ffbabfba37e1000b5b0da03e349af14fddea2ed72f868e90c7ed5f9" },
    { sourceGraphName := "OAI.PiExponent.FormalJetDerivatives.jetFrame", expectedUserName := "OAI.PiExponent.FormalJetDerivatives.jetFrame", expectedPublicName := "OAI.PiExponent.FormalJetDerivatives.jetFrame", expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalJetDerivatives", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalJetDerivatives:1003", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "69d22f80d0373ed91875fd9062279eb13aceab9353cc5f492ebf3081d03cce78" },
    { sourceGraphName := "OAI.PiExponent.FormalJetDerivatives.jetFrameWord", expectedUserName := "OAI.PiExponent.FormalJetDerivatives.jetFrameWord", expectedPublicName := "OAI.PiExponent.FormalJetDerivatives.jetFrameWord", expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalJetDerivatives", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalJetDerivatives:2119", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "2bf100fb2298682e249db7e647067b8668cf7effcca018cd1e6a769c85021fac" },
    { sourceGraphName := "OAI.PiExponent.FormalJetDerivatives.pderiv_mem_rationalWeightedIdeal", expectedUserName := "OAI.PiExponent.FormalJetDerivatives.pderiv_mem_rationalWeightedIdeal", expectedPublicName := "OAI.PiExponent.FormalJetDerivatives.pderiv_mem_rationalWeightedIdeal", expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalJetDerivatives", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalJetDerivatives:280", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "6bbc08cb3b07ef810e780ea3526c5498617bfccf8ba6c2b1cb81620451714aff" },
    { sourceGraphName := "OAI.PiExponent.FormalLogJet.liftSeries_C", expectedUserName := "OAI.PiExponent.FormalLogJet.liftSeries_C", expectedPublicName := "OAI.PiExponent.FormalLogJet.liftSeries_C", expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:1031", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "5532c15f572e4e5aa6efde29940601a0e38868f153a9d37b554a318dc51d7710" },
    { sourceGraphName := "OAI.PiExponent.FormalLogJet.formalLog", expectedUserName := "OAI.PiExponent.FormalLogJet.formalLog", expectedPublicName := "OAI.PiExponent.FormalLogJet.formalLog", expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:1982", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "63502c455521d85d296e3e9e61cfd7decd76e44f78e2d20f99cc1048af622a7b" },
    { sourceGraphName := "OAI.PiExponent.FormalLogJet.formalJet", expectedUserName := "OAI.PiExponent.FormalLogJet.formalJet", expectedPublicName := "OAI.PiExponent.FormalLogJet.formalJet", expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:2786", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "171b0c4d75d407c80819c4737daad61a712e62bd5bf260ac9e7b941171b54fb9" },
    { sourceGraphName := "OAI.PiExponent.FormalLogJet.formalJet_Y", expectedUserName := "OAI.PiExponent.FormalLogJet.formalJet_Y", expectedPublicName := "OAI.PiExponent.FormalLogJet.formalJet_Y", expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:3013", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "921a3d169bc527cc431cf0eed2574d0759406fc8764c43c864cefc954aca4dde" },
    { sourceGraphName := "OAI.PiExponent.FormalLogJet.formalJet_X", expectedUserName := "OAI.PiExponent.FormalLogJet.formalJet_X", expectedPublicName := "OAI.PiExponent.FormalLogJet.formalJet_X", expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:3162", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "847ff6491bd29f9061cfa764c38ee17dcc639c7f72d47d23142cef3f44d36a98" },
    { sourceGraphName := "OAI.PiExponent.FormalLogJet.derivation_map_of_X", expectedUserName := "OAI.PiExponent.FormalLogJet.derivation_map_of_X", expectedPublicName := "OAI.PiExponent.FormalLogJet.derivation_map_of_X", expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:3339", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "7f997864ee5ad1d8bd66e3df918209e6abba85b46fae9c1652262ff9161e3d95" },
    { sourceGraphName := "OAI.PiExponent.FormalLogJet.liftSeries", expectedUserName := "OAI.PiExponent.FormalLogJet.liftSeries", expectedPublicName := "OAI.PiExponent.FormalLogJet.liftSeries", expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:351", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "f29ece8d37a43165610bdfd424af8f4c2f667a36b3035f9fd25dd2b41d0414c8" },
    { sourceGraphName := "OAI.PiExponent.FormalLogJet.coeff_liftSeries", expectedUserName := "OAI.PiExponent.FormalLogJet.coeff_liftSeries", expectedPublicName := "OAI.PiExponent.FormalLogJet.coeff_liftSeries", expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:510", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "5560967cec68f7f9c092c7e4ed7087899f373d4825682acff8398b22372c7dfe" },
    { sourceGraphName := "OAI.PiExponent.FormalLogJet.liftSeries_X", expectedUserName := "OAI.PiExponent.FormalLogJet.liftSeries_X", expectedPublicName := "OAI.PiExponent.FormalLogJet.liftSeries_X", expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:880", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "429172ec6e26020e5e4e3f3ac1013fd520ce54b7cc7c8eb5743bd13d76865d95" }
  ]

run_meta do
  exportProviderSnapshotJsonl providerRequests "missions/pi-irrationality-measure/verification/providers-context-preview/source-snapshot/source.jsonl"
