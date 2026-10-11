import Lean
import OAI.NumberTheory.PiExponent.Approximation.RowTranslation

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
    { sourceGraphName := "OAI.PiExponent.RowTranslation.shiftCoefficient", expectedUserName := "OAI.PiExponent.RowTranslation.shiftCoefficient", expectedPublicName := "OAI.PiExponent.RowTranslation.shiftCoefficient", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:1019", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "c3966b6cd9032c86c56f70ab19acc6bf3d3c0c8a08f1a44f609b7caccc3bb5f2" },
    { sourceGraphName := "OAI.PiExponent.RowTranslation.RowChoices", expectedUserName := "OAI.PiExponent.RowTranslation.RowChoices", expectedPublicName := "OAI.PiExponent.RowTranslation.RowChoices", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:10668", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "98def1acefd799e100d4889e9d9f1fa635991d2726dd3f4bfa52ea6ce4936bfb" },
    { sourceGraphName := "OAI.PiExponent.RowTranslation.tail", expectedUserName := "OAI.PiExponent.RowTranslation.tail", expectedPublicName := "OAI.PiExponent.RowTranslation.tail", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:12851", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "864a826c6d1078095926e1c88bdca809500d27fb0702b18adfd18fc633157061" },
    { sourceGraphName := "OAI.PiExponent.RowTranslation.shift", expectedUserName := "OAI.PiExponent.RowTranslation.shift", expectedPublicName := "OAI.PiExponent.RowTranslation.shift", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:222", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "f7078d28ae849daef40dc4a03ab4592117179dd459496aa8eeb2dbd42b4cd106" },
    { sourceGraphName := "OAI.PiExponent.RowTranslation.multiIndex", expectedUserName := "OAI.PiExponent.RowTranslation.multiIndex", expectedPublicName := "OAI.PiExponent.RowTranslation.multiIndex", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:2296", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "b3aac1c3795f11100810fae4a6d0bfd4e6c7efc3cbbe706511f311ab771405c9" },
    { sourceGraphName := "OAI.PiExponent.RowTranslation.multiIndex_apply", expectedUserName := "OAI.PiExponent.RowTranslation.multiIndex_apply", expectedPublicName := "OAI.PiExponent.RowTranslation.multiIndex_apply", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:2396", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "c820b4360b0e8d00e40d8222918477c6530194930ff925a074714056d161c597" },
    { sourceGraphName := "OAI.PiExponent.RowTranslation.shifted_X_pow", expectedUserName := "OAI.PiExponent.RowTranslation.shifted_X_pow", expectedPublicName := "OAI.PiExponent.RowTranslation.shifted_X_pow", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:2534", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "96caa63129aa32a4292905db84200c2e679999cad15955051dfe14c684955b4a" },
    { sourceGraphName := "OAI.PiExponent.RowTranslation.shifted_product_expansion", expectedUserName := "OAI.PiExponent.RowTranslation.shifted_product_expansion", expectedPublicName := "OAI.PiExponent.RowTranslation.shifted_product_expansion", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:2894", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "67570c22c7b300f23abea8f4bbe57becc5c3f7b67f02f63d86589ab4e62225d6" },
    { sourceGraphName := "OAI.PiExponent.RowTranslation.shift_monomial_one", expectedUserName := "OAI.PiExponent.RowTranslation.shift_monomial_one", expectedPublicName := "OAI.PiExponent.RowTranslation.shift_monomial_one", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:3500", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "ba2d43d79652ded0c7412096358354b21e5f5f5506923adb7859913aebd19793" },
    { sourceGraphName := "OAI.PiExponent.RowTranslation.shiftCoefficient_eq", expectedUserName := "OAI.PiExponent.RowTranslation.shiftCoefficient_eq", expectedPublicName := "OAI.PiExponent.RowTranslation.shiftCoefficient_eq", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:3766", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "3cd7188363c947a1ed33d6f8e58710b3e7481b4de0fd7e7e9cb6e64df316c17b" },
    { sourceGraphName := "OAI.PiExponent.RowTranslation.rowScalar", expectedUserName := "OAI.PiExponent.RowTranslation.rowScalar", expectedPublicName := "OAI.PiExponent.RowTranslation.rowScalar", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:7272", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "25e6fd5a6123637169e5cbf6ce748019c0a0e5bae583742016ef7ce609548f84" }
  ]

run_meta do
  exportProviderSnapshotJsonl providerRequests "missions/pi-irrationality-measure/verification/providers-preview/all-shared-safe-leaves/snapshots/Def_OAI_NumberTheory_PiExponent_Approximation_RowTranslation/original.jsonl"
