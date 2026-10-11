import Lean
import Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexUnweighted

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
    { sourceGraphName := "OAI.PiExponent.unweightedSimplex", expectedUserName := "OAI.PiExponent.unweightedSimplex", expectedPublicName := "OAI.PiExponent.unweightedSimplex", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexUnweighted", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted:168", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "038ab30ff7c2537f5dbb153ad137d4922b0bcdd3e92eaaa581ef2a4303a968ab" },
    { sourceGraphName := "OAI.PiExponent.tendsto_choose_normalized", expectedUserName := "OAI.PiExponent.tendsto_choose_normalized", expectedPublicName := "OAI.PiExponent.tendsto_choose_normalized", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexUnweighted", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted:2321", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "2bc3f7569452caa6d03f6293b22fedece8d6b13903a9e0ab03a5dcbee8eae397" },
    { sourceGraphName := "OAI.PiExponent.tendsto_choose_add_normalized", expectedUserName := "OAI.PiExponent.tendsto_choose_add_normalized", expectedPublicName := "OAI.PiExponent.tendsto_choose_add_normalized", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexUnweighted", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted:2924", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "f3154e730a3708ea4887f24837dff71fb9b443a979db28c15dfaa5f549aec9d5" },
    { sourceGraphName := "OAI.PiExponent.mem_unweightedSimplex", expectedUserName := "OAI.PiExponent.mem_unweightedSimplex", expectedPublicName := "OAI.PiExponent.mem_unweightedSimplex", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexUnweighted", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted:327", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "f7ba98b1b9326590a091f40cfbb36e0b9173df80973b96c35decac1b5aa471b8" },
    { sourceGraphName := "OAI.PiExponent.tendsto_card_unweightedSimplex", expectedUserName := "OAI.PiExponent.tendsto_card_unweightedSimplex", expectedPublicName := "OAI.PiExponent.tendsto_card_unweightedSimplex", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexUnweighted", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted:3702", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "17367159d1d669fdcb3048f40adc9a3c33be399837c0dd543c17787fcdb6ea89" },
    { sourceGraphName := "OAI.PiExponent.tendsto_card_unweightedSimplex_add", expectedUserName := "OAI.PiExponent.tendsto_card_unweightedSimplex_add", expectedPublicName := "OAI.PiExponent.tendsto_card_unweightedSimplex_add", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexUnweighted", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted:3970", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "9d0d7cae99aac1178dbcce1f818f7d9cf238d7e183f7f3d70ac51e58cd8c1bb0" },
    { sourceGraphName := "OAI.PiExponent.card_unweightedSimplex", expectedUserName := "OAI.PiExponent.card_unweightedSimplex", expectedPublicName := "OAI.PiExponent.card_unweightedSimplex", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexUnweighted", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted:751", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "7512611b07e6fe56eb9839dcf211cce5ccab3676a47790ddbc0e29c05ba8177a" }
  ]

run_meta do
  exportProviderSnapshotJsonl providerRequests "missions/pi-irrationality-measure/verification/providers-complete-preview/all-shared-safe-leaves/snapshots/Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexUnweighted/fast-generated.jsonl"
