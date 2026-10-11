import Lean
import OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame

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
    { sourceGraphName := "OAI.PiExponentApprox.derivation_finset_sum_apply", expectedUserName := "OAI.PiExponentApprox.derivation_finset_sum_apply", expectedPublicName := "OAI.PiExponentApprox.derivation_finset_sum_apply", expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame:785", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "0395f07cd3bc4210efafa19ac17b4937adcfc3669bd3b53a8ffa316c5a2d9c1c" }
  ]

run_meta do
  exportProviderSnapshotJsonl providerRequests "missions/pi-irrationality-measure/verification/providers-context-preview/namespace-context/snapshots/Def_OAI_NumberTheory_PiExponent_Polynomials_PolynomialFrame/original.jsonl"
