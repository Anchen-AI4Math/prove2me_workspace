import Lean
import OAI.NumberTheory.PiExponent.Approximation.Parameters

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
    { sourceGraphName := "OAI.PiExponent.Parameters.approximation_gap", expectedUserName := "OAI.PiExponent.Parameters.approximation_gap", expectedPublicName := "OAI.PiExponent.Parameters.approximation_gap", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "fd561b73e671cc3c7dec530c3242cbcd45a158917a9a2427bfb700951d1a8206" },
    { sourceGraphName := "OAI.PiExponent.Parameters.one_lt_C", expectedUserName := "OAI.PiExponent.Parameters.one_lt_C", expectedPublicName := "OAI.PiExponent.Parameters.one_lt_C", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "08c66cfec231332f79f5b9beafcd9b4ea3c7a3cae7659f61081d63a749aa054b" },
    { sourceGraphName := "OAI.PiExponent.Parameters.C", expectedUserName := "OAI.PiExponent.Parameters.C", expectedPublicName := "OAI.PiExponent.Parameters.C", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "78f8bfd96546f52acaa6ecc5403daacbd937489beb030bcd3667d170ea4230c9" },
    { sourceGraphName := "OAI.PiExponent.Parameters.mk", expectedUserName := "OAI.PiExponent.Parameters.mk", expectedPublicName := "OAI.PiExponent.Parameters.mk", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters", expectedKind := "ctor", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "96d047fab06b0c5b26def512360adacb9bb5b285bede888273d0adac5e69b4c8" },
    { sourceGraphName := "OAI.PiExponent.Parameters.B_lt_C_theta", expectedUserName := "OAI.PiExponent.Parameters.B_lt_C_theta", expectedPublicName := "OAI.PiExponent.Parameters.B_lt_C_theta", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "8321e192bb45c64f18380c423651fdaf474e0ebcc1e0d827e539199d8c59592f" },
    { sourceGraphName := "OAI.PiExponent.Parameters.eta", expectedUserName := "OAI.PiExponent.Parameters.eta", expectedPublicName := "OAI.PiExponent.Parameters.eta", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "91809a058c30f17b25f47973836bfcb627bbf45aa2b5d7a58df2b495bc848f0a" },
    { sourceGraphName := "OAI.PiExponent.Parameters.B", expectedUserName := "OAI.PiExponent.Parameters.B", expectedPublicName := "OAI.PiExponent.Parameters.B", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "ce4bf30b3ed54f9be5151c2a8405547f6049288790361cbc1dcbf2fca8ece291" },
    { sourceGraphName := "OAI.PiExponent.Parameters.B_lt_inv_C", expectedUserName := "OAI.PiExponent.Parameters.B_lt_inv_C", expectedPublicName := "OAI.PiExponent.Parameters.B_lt_inv_C", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "93c64801fdd7a5307b83f52be8c091143d8da52d2d5b9011a879767655e555c1" },
    { sourceGraphName := "OAI.PiExponent.Parameters.eta_pos", expectedUserName := "OAI.PiExponent.Parameters.eta_pos", expectedPublicName := "OAI.PiExponent.Parameters.eta_pos", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "b7ad4122c2a230b73caa0b6389cc6104fb061ab5dfefa3e9b39bc3605a8f3628" },
    { sourceGraphName := "OAI.PiExponent.Parameters.rec", expectedUserName := "OAI.PiExponent.Parameters.rec", expectedPublicName := "OAI.PiExponent.Parameters.rec", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters", expectedKind := "rec", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "2bc2f50c6fc2cd9b3b010eb22618c5ccda2dbeb9f070da768579876195eebb37" },
    { sourceGraphName := "OAI.PiExponent.Parameters", expectedUserName := "OAI.PiExponent.Parameters", expectedPublicName := "OAI.PiExponent.Parameters", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters", expectedKind := "inductive", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "1959ebb3f2aea65f610a6dccebb1d76370724d77f59615a8613f6fde38207407" },
    { sourceGraphName := "OAI.PiExponent.Parameters.recOn", expectedUserName := "OAI.PiExponent.Parameters.recOn", expectedPublicName := "OAI.PiExponent.Parameters.recOn", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "55b2878abd89a225fa453669d093e9984dc054e329e650f35e579ed91ebc1c53" },
    { sourceGraphName := "OAI.PiExponent.Parameters.casesOn", expectedUserName := "OAI.PiExponent.Parameters.casesOn", expectedPublicName := "OAI.PiExponent.Parameters.casesOn", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "414e266917c5ab0795344618c5171503fbe89f8fd4de3f4c795e862355a05d13" },
    { sourceGraphName := "OAI.PiExponent.Parameters.eta_lt_one", expectedUserName := "OAI.PiExponent.Parameters.eta_lt_one", expectedPublicName := "OAI.PiExponent.Parameters.eta_lt_one", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "083f67995d6b489dd477f85539829ae0f909e017b7b2ae98d79c97d17bc86a1b" },
    { sourceGraphName := "OAI.PiExponent.Parameters.A_lt_B", expectedUserName := "OAI.PiExponent.Parameters.A_lt_B", expectedPublicName := "OAI.PiExponent.Parameters.A_lt_B", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "104640a061689cc71fe999651e3c55424ecf9a4e77ecd24cc21c0769b0f4970c" },
    { sourceGraphName := "OAI.PiExponent.Parameters.noConfusion", expectedUserName := "OAI.PiExponent.Parameters.noConfusion", expectedPublicName := "OAI.PiExponent.Parameters.noConfusion", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "ca392e756dc60c8923068c5514391b33470b162a7fa98ddc6dfc600189b73e01" },
    { sourceGraphName := "OAI.PiExponent.Parameters.C_theta_lt_one", expectedUserName := "OAI.PiExponent.Parameters.C_theta_lt_one", expectedPublicName := "OAI.PiExponent.Parameters.C_theta_lt_one", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "9c1e892f80d53d1583368c914bd05959fba4da7100a7c59b921c4ed990099270" },
    { sourceGraphName := "OAI.PiExponent.Parameters.theta_pos", expectedUserName := "OAI.PiExponent.Parameters.theta_pos", expectedPublicName := "OAI.PiExponent.Parameters.theta_pos", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "72465333cd1627e9ed4b04f240468bea82c752fa5eef9be02d37292c22a7a2bf" },
    { sourceGraphName := "OAI.PiExponent.Parameters.A", expectedUserName := "OAI.PiExponent.Parameters.A", expectedPublicName := "OAI.PiExponent.Parameters.A", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "a4b59a8b4862dd1436e6b185c6ad40d37c8a10bf6b7128048cbdff8c4ba8d1c5" },
    { sourceGraphName := "OAI.PiExponent.Parameters.gap_pos", expectedUserName := "OAI.PiExponent.Parameters.gap_pos", expectedPublicName := "OAI.PiExponent.Parameters.gap_pos", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "df664f2d63b6b8c38fc17236e4ce5feafffd4c8434f85135c3d44d2f63d9c3e3" },
    { sourceGraphName := "OAI.PiExponent.Parameters.theta_lt_A", expectedUserName := "OAI.PiExponent.Parameters.theta_lt_A", expectedPublicName := "OAI.PiExponent.Parameters.theta_lt_A", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "d4abb8c9fb3d254317e4b080b65a01f32f13042a1beccbbb9bc66c8dbe48cac3" },
    { sourceGraphName := "OAI.PiExponent.Parameters.theta", expectedUserName := "OAI.PiExponent.Parameters.theta", expectedPublicName := "OAI.PiExponent.Parameters.theta", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "31398ad0ca6bea5cd9f9a5281e73a6e514e34bfa9d100ab9b0137324edb592a5" },
    { sourceGraphName := "OAI.PiExponent.Parameters.B_lt_one", expectedUserName := "OAI.PiExponent.Parameters.B_lt_one", expectedPublicName := "OAI.PiExponent.Parameters.B_lt_one", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "692e10f8930e2164c2799f0e0b4727a1fee6feb0770a8ec33e6bf53ca834a61f" },
    { sourceGraphName := "OAI.PiExponent.Parameters.mk.noConfusion", expectedUserName := "OAI.PiExponent.Parameters.mk.noConfusion", expectedPublicName := "OAI.PiExponent.Parameters.mk.noConfusion", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "5117ffeec9d4cc0dc67cba1eee378f06f6fd17e0dd45e3de66fac5f2bedb08eb" },
    { sourceGraphName := "OAI.PiExponent.Parameters.A_pos", expectedUserName := "OAI.PiExponent.Parameters.A_pos", expectedPublicName := "OAI.PiExponent.Parameters.A_pos", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:5380", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "e48c067080464a6cdb88ca55f08a0eb904b2d7cc9fe26638ff1062af38950cb6" }
  ]

run_meta do
  exportProviderSnapshotJsonl providerRequests "missions/pi-irrationality-measure/verification/providers-complete-preview/all-shared-safe-leaves/snapshots/Def_OAI_NumberTheory_PiExponent_Approximation_Parameters/original.jsonl"
