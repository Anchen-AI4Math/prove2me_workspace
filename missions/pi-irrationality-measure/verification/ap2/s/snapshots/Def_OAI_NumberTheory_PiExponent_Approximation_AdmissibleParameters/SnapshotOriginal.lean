import Lean
import OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters

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
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.arithmeticError", expectedUserName := "OAI.PiExponent.AdmissibleParameters.arithmeticError", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.arithmeticError", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:12604", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "9e6fd74814be14863914b39dd84fffc1e4ab4051d81cb843514da48b6ad5c745" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.translationError", expectedUserName := "OAI.PiExponent.AdmissibleParameters.translationError", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.translationError", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:12784", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "70234677172bb5396274cd862433b32d475989035953d9b17e0af072b4ed5e79" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.holomorphicError", expectedUserName := "OAI.PiExponent.AdmissibleParameters.holomorphicError", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.holomorphicError", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:12936", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "3c7589e8562d6a358c2a9d587332bee9e8ae29cd0c6d9350d0b8d55bba0971d6" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.analyticError", expectedUserName := "OAI.PiExponent.AdmissibleParameters.analyticError", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.analyticError", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:13093", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "6626569054afa61ec0dc987e8a284cc42620986dc77cb84acb5baed854680a41" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.x_one_le", expectedUserName := "OAI.PiExponent.AdmissibleParameters.x_one_le", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.x_one_le", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "60716a30d4c06faa34f980b218a5b69cefe2538b9fd24218ab7f730572c2f912" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.x_log", expectedUserName := "OAI.PiExponent.AdmissibleParameters.x_log", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.x_log", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "b91a285cb298905184148e0e3eec7df492fb5ad914a0c0df2a8b915d6783e61b" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.K", expectedUserName := "OAI.PiExponent.AdmissibleParameters.K", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.K", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "2c50c7f2a73bb2f01dd7ee4d82c998476d96cdf82131cccbaa649a9563a1a536" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.m", expectedUserName := "OAI.PiExponent.AdmissibleParameters.m", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.m", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "d4e9015c664f68ec0c8f884e95478c645cc4ef2efa5bd838abfe68a26fd517b2" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.sigma_volume", expectedUserName := "OAI.PiExponent.AdmissibleParameters.sigma_volume", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.sigma_volume", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "50b588c2a26c3cf930f6a70903644004bcf3249dc762be28e6b93facf61e72a2" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.epsilon", expectedUserName := "OAI.PiExponent.AdmissibleParameters.epsilon", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.epsilon", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "997dda484fc9c6c4df59258ead4b0ff48858ffe1475a073e41c0cd72252b4f58" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.wstar_attained", expectedUserName := "OAI.PiExponent.AdmissibleParameters.wstar_attained", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.wstar_attained", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "ae3b89dd0a91d663f9c7c60d7a9ad66729ca607ed5ec6ab7d7d8a5ce15495f9d" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.x", expectedUserName := "OAI.PiExponent.AdmissibleParameters.x", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.x", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "3d2fb4c0ac87c30c17e50e74f7a3511ca4fc004fa976b575df9c80edccd60540" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.sigma_centers", expectedUserName := "OAI.PiExponent.AdmissibleParameters.sigma_centers", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.sigma_centers", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "49aab0fe8796f41c5417ffe2d03b4acfb3c47412d09c32ea7dd8446a040c1923" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.rec", expectedUserName := "OAI.PiExponent.AdmissibleParameters.rec", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.rec", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "rec", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "461cc675fd598d7e69d803076ca99f3af3bef39f77604eef020d5756f667f3cb" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.sigma", expectedUserName := "OAI.PiExponent.AdmissibleParameters.sigma", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.sigma", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "62d01aef6f0c6b7ee934e98163dce70b2e73f7d31d485b9c49c9629d032228b2" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.mk.noConfusion", expectedUserName := "OAI.PiExponent.AdmissibleParameters.mk.noConfusion", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.mk.noConfusion", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "f0a96c772cb0ab288855a6f878530c95d700c41b0512fb76e1fa67a2353ab193" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.volume_eq", expectedUserName := "OAI.PiExponent.AdmissibleParameters.volume_eq", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.volume_eq", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "b694ea149bbe3bbd21c7c0714a8a75bea8ab7fb0097b3903b89be3d065b42684" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.w0", expectedUserName := "OAI.PiExponent.AdmissibleParameters.w0", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.w0", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "cbfb437ac6f8bf3a8b1bb4d016b3f1e7d32ee189902b03e47a98de53c350476a" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.initial_margin", expectedUserName := "OAI.PiExponent.AdmissibleParameters.initial_margin", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.initial_margin", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "f4484806a112aacdf4dab4967f6b000a7d9903322fc1701926a072aec2a7d0ac" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.recOn", expectedUserName := "OAI.PiExponent.AdmissibleParameters.recOn", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.recOn", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "a2cb066747349fec5c889a6cd3cca90bc9336979714dc20a5b940f39fc13cab9" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.collision_margin", expectedUserName := "OAI.PiExponent.AdmissibleParameters.collision_margin", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.collision_margin", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "84bfa8e68dd1fbbf7f77c61a6f9bce064330677ec6dab08880f47f592dd34a85" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.approximations", expectedUserName := "OAI.PiExponent.AdmissibleParameters.approximations", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.approximations", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "aaf73660ca7aea3de373bc2aea43f228eb9b222afa662a5985f31ad91181d76f" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.F0", expectedUserName := "OAI.PiExponent.AdmissibleParameters.F0", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.F0", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "6e07a788a03a732dc4d1e040955770fd5dce26eb544acb52f9d2baf8fd80b4e9" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.w0_eq", expectedUserName := "OAI.PiExponent.AdmissibleParameters.w0_eq", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.w0_eq", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "e5ed5c83295b807cc0fff10f1627802ebb10e8dafed9b9f98a17a4d8e667f1f9" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters", expectedUserName := "OAI.PiExponent.AdmissibleParameters", expectedPublicName := "OAI.PiExponent.AdmissibleParameters", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "inductive", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "0fe91777471b27fdcbaa7b95e79c76540e1450df365beac95969f9a316b777a4" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.w0_pos", expectedUserName := "OAI.PiExponent.AdmissibleParameters.w0_pos", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.w0_pos", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "4327cae9ef0fec5683a994f6356f67d795d6d4037e20fc0600a3777b20dc027e" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.q", expectedUserName := "OAI.PiExponent.AdmissibleParameters.q", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.q", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "8a274dd3132e9589f81d6918a3b40b4f60926b66d529ff5a107c6f86e86cc07e" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.wstar", expectedUserName := "OAI.PiExponent.AdmissibleParameters.wstar", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.wstar", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "f46018696e8cc4bb9d9fa60c4bfe11903d42a69bc02a72a9f6cae52ec6585737" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.p", expectedUserName := "OAI.PiExponent.AdmissibleParameters.p", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.p", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "24ae95a144f64ded836576d32841423aed8e60ca95849a20a64a4cf3510d88a5" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.sigma_theta", expectedUserName := "OAI.PiExponent.AdmissibleParameters.sigma_theta", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.sigma_theta", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "0226d22e7ed13f7ef3eba3181f4e544bef4747356320d6208f56550107d4d475" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.volume_lt_one", expectedUserName := "OAI.PiExponent.AdmissibleParameters.volume_lt_one", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.volume_lt_one", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "fc991d23bfad19356d4212f994b5c778a3d378a0321ce6707b77e9bfbe4eb29a" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.weight_growth", expectedUserName := "OAI.PiExponent.AdmissibleParameters.weight_growth", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.weight_growth", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "b70db00109afdf3108de8a0373186561041683d8a5f744aabb9227dd5fb30c10" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.F0_pos", expectedUserName := "OAI.PiExponent.AdmissibleParameters.F0_pos", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.F0_pos", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "553f377f8fd6260a4647d1fde5b80befc341fd529bd0639649274dea377aee03" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.wstar_lower", expectedUserName := "OAI.PiExponent.AdmissibleParameters.wstar_lower", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.wstar_lower", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "b8962fd7410292f589961d06a99202a07da45f196583ee3ec28702888ddba6ff" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.K_pos", expectedUserName := "OAI.PiExponent.AdmissibleParameters.K_pos", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.K_pos", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "216944eb3c56c3614cd00d008cd63591465c2efce4e273c78b5076f0942d0c1d" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.v0_eq", expectedUserName := "OAI.PiExponent.AdmissibleParameters.v0_eq", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.v0_eq", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "b12ef1a233b168f1cb12db4527acbdf2645a6262ff279decefee033976ee5eba" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.v0_pos", expectedUserName := "OAI.PiExponent.AdmissibleParameters.v0_pos", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.v0_pos", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "8bf95ea99a27be454eaa8d8814c0764bb6889a9de310911208f5afe60f297f00" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.epsilon_lt_gap", expectedUserName := "OAI.PiExponent.AdmissibleParameters.epsilon_lt_gap", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.epsilon_lt_gap", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "7a52307cc27628e9b08d4d04119a3177104542c20f1044410cc57345606b7659" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.epsilon_pos", expectedUserName := "OAI.PiExponent.AdmissibleParameters.epsilon_pos", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.epsilon_pos", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "5f557f266f5920f3d5fc0707f350aeb0a5b3efe05f752ec73db0e8bb017a5ad0" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.x_zero", expectedUserName := "OAI.PiExponent.AdmissibleParameters.x_zero", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.x_zero", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "1a3642ca8c261b85a664a129811d130c65c7971b4d5820ce584f94db33942d69" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.K_eq", expectedUserName := "OAI.PiExponent.AdmissibleParameters.K_eq", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.K_eq", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "d833b53cf385eb31443810a0560999e1cbd3b2b4d9cb974dc64ca988f3f85ad1" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.base", expectedUserName := "OAI.PiExponent.AdmissibleParameters.base", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.base", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "0870767dac60e9e015d91e1c6914268fc5a75193947844383f584e4e3c3db6ff" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.noConfusion", expectedUserName := "OAI.PiExponent.AdmissibleParameters.noConfusion", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.noConfusion", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "aa7fdd7013b61ead06aac1f276f8e2efdbdd2de06fe6888ea9736f5c2e4b165c" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.F0_large", expectedUserName := "OAI.PiExponent.AdmissibleParameters.F0_large", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.F0_large", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "a63277f0cc4969bcdeddd96ec0aff89d63ec48e4c08b128d189d4f479de88688" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.dimension_margin", expectedUserName := "OAI.PiExponent.AdmissibleParameters.dimension_margin", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.dimension_margin", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "3d7c12295ae9dd15a57f1098be6fa89b7e2e995b6f2a9f9de6dfedcc5e05272e" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.casesOn", expectedUserName := "OAI.PiExponent.AdmissibleParameters.casesOn", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.casesOn", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "fb122f4f0b80a12f44aed313a371e2c56be9d5ba5dc4d3df903cf2b680cfc844" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.sigma_pos", expectedUserName := "OAI.PiExponent.AdmissibleParameters.sigma_pos", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.sigma_pos", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "fe2038c34541e78771cb77ebb9e21ea1241e5739b2fa077d48e26c0a59439612" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.weight_margin", expectedUserName := "OAI.PiExponent.AdmissibleParameters.weight_margin", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.weight_margin", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "82ff198ada4b33c69b15be674e29b6cc3b960abfb7cafcf500ca829c8f75cd48" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.wstar_pos", expectedUserName := "OAI.PiExponent.AdmissibleParameters.wstar_pos", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.wstar_pos", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "c303662deee1ea3a9d16246be9f19130a51f8b418777f342701cdd4714d76697" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.epsilon_le_half", expectedUserName := "OAI.PiExponent.AdmissibleParameters.epsilon_le_half", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.epsilon_le_half", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "756dbf6888b3abca3143363014fc938bd426f0f2868d9a863a1aed944a8c038d" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.mk", expectedUserName := "OAI.PiExponent.AdmissibleParameters.mk", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.mk", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "ctor", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "b6aa2511d0b6f5dbb66c13f080c9c0590a22109e32b6e0247172b69926d230d0" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.m_pos", expectedUserName := "OAI.PiExponent.AdmissibleParameters.m_pos", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.m_pos", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "e49fec9450acb197928cf9bc6fca97d2cb0d30e439d5535a37dcbaf14688fe15" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.v0", expectedUserName := "OAI.PiExponent.AdmissibleParameters.v0", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.v0", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:2327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "32e60970381f16d5084a46d2a82245aae8f8d640737814caf25112d4313e4eef" },
    { sourceGraphName := "OAI.PiExponent.interpolationSeparationConstant", expectedUserName := "OAI.PiExponent.interpolationSeparationConstant", expectedPublicName := "OAI.PiExponent.interpolationSeparationConstant", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:552", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "4f5a507b47c8d9b0742c774a1b9da1545a4d1829a09979bbdad51ebc5971c23e" },
    { sourceGraphName := "OAI.PiExponent.weightErrorCoefficient", expectedUserName := "OAI.PiExponent.weightErrorCoefficient", expectedPublicName := "OAI.PiExponent.weightErrorCoefficient", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:939", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "322c4bc9061dd34804a634f9cd9814ce4f61a73741c1d6b5beef10ae5177516f" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.rationalWeight", expectedUserName := "OAI.PiExponent.AdmissibleParameters.rationalWeight", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.rationalWeight", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:9489", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "de156a5d629cdbd7e50f5c436de7976a71426c3bdd035e645d3d20b0f2c399e6" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.cast_rationalWeight", expectedUserName := "OAI.PiExponent.AdmissibleParameters.cast_rationalWeight", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.cast_rationalWeight", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:9601", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "97c9500758cc1b110964abd42b4db9ecccf610b3a8c7cfc58cb103c980de8070" },
    { sourceGraphName := "OAI.PiExponent.AdmissibleParameters.rationalWeight_pos", expectedUserName := "OAI.PiExponent.AdmissibleParameters.rationalWeight_pos", expectedPublicName := "OAI.PiExponent.AdmissibleParameters.rationalWeight_pos", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters:9818", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "4d0a71c146240aa0a6593fa4f4ea014db8eff3be5ae0bac80bfd0f9b878bc95d" }
  ]

run_meta do
  exportProviderSnapshotJsonl providerRequests "missions/pi-irrationality-measure/verification/ap2/s/snapshots/Def_OAI_NumberTheory_PiExponent_Approximation_AdmissibleParameters/original.jsonl"
