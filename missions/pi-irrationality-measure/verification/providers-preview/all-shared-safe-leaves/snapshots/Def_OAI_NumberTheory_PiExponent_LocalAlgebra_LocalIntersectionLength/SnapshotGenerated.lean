import Lean
import Definitions.Def_OAI_NumberTheory_PiExponent_LocalAlgebra_LocalIntersectionLength

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
    { sourceGraphName := "OAI.PiExponentJets.W28.LocalIntersection.quotientMul", expectedUserName := "OAI.PiExponentJets.W28.LocalIntersection.quotientMul", expectedPublicName := "OAI.PiExponentJets.W28.LocalIntersection.quotientMul", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_LocalAlgebra_LocalIntersectionLength", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength:1447", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "11c0f5d2ee74e4fba60c2ff063dfc3f4356591d511034f9e03c948534904a28f" },
    { sourceGraphName := "OAI.PiExponentJets.W28.LocalIntersection.quotientMul_mk", expectedUserName := "OAI.PiExponentJets.W28.LocalIntersection.quotientMul_mk", expectedPublicName := "OAI.PiExponentJets.W28.LocalIntersection.quotientMul_mk", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_LocalAlgebra_LocalIntersectionLength", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength:1660", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "f76ac134d87cb139be125d17ee74e0effe119a6de3dd901672618806ac1cd8fa" },
    { sourceGraphName := "OAI.PiExponentJets.W28.LocalIntersection.quotientMul_kernel", expectedUserName := "OAI.PiExponentJets.W28.LocalIntersection.quotientMul_kernel", expectedPublicName := "OAI.PiExponentJets.W28.LocalIntersection.quotientMul_kernel", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_LocalAlgebra_LocalIntersectionLength", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength:1943", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "b5c5250ec09cdf2654d47b1f23aefb627c1448307afc9cf83364506cb0015a3c" },
    { sourceGraphName := "OAI.PiExponentJets.W28.LocalIntersection.colonQuotientEquivKernel", expectedUserName := "OAI.PiExponentJets.W28.LocalIntersection.colonQuotientEquivKernel", expectedPublicName := "OAI.PiExponentJets.W28.LocalIntersection.colonQuotientEquivKernel", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_LocalAlgebra_LocalIntersectionLength", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength:2733", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "6c9bb117a5611c213f6426bbb55bb9bc2b9e4190c9e099532002b930b379980d" },
    { sourceGraphName := "OAI.PiExponentJets.W28.LocalIntersection.quotientMul_range", expectedUserName := "OAI.PiExponentJets.W28.LocalIntersection.quotientMul_range", expectedPublicName := "OAI.PiExponentJets.W28.LocalIntersection.quotientMul_range", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_LocalAlgebra_LocalIntersectionLength", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength:3019", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "b1e6a1fc6a16ce2fba2d8c2259420d86fd122c1a38d35497689f821abc0a0c16" },
    { sourceGraphName := "OAI.PiExponentJets.W28.LocalIntersection.cokernelEquivCut", expectedUserName := "OAI.PiExponentJets.W28.LocalIntersection.cokernelEquivCut", expectedPublicName := "OAI.PiExponentJets.W28.LocalIntersection.cokernelEquivCut", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_LocalAlgebra_LocalIntersectionLength", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength:3554", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "94e5b144edd8ae25c84140a3611bea78fe7e62801233a522494d873468ea20e9" },
    { sourceGraphName := "OAI.PiExponentJets.W28.LocalIntersection.kernel_length_eq_colon", expectedUserName := "OAI.PiExponentJets.W28.LocalIntersection.kernel_length_eq_colon", expectedPublicName := "OAI.PiExponentJets.W28.LocalIntersection.kernel_length_eq_colon", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_LocalAlgebra_LocalIntersectionLength", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength:3852", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "2fb0ecce1e247cc2015b89982fe773aa9aa3cd9e3c12cac3e21d6a6b09e9e9f9" },
    { sourceGraphName := "OAI.PiExponentJets.W28.LocalIntersection.cokernel_length_eq_cut", expectedUserName := "OAI.PiExponentJets.W28.LocalIntersection.cokernel_length_eq_cut", expectedPublicName := "OAI.PiExponentJets.W28.LocalIntersection.cokernel_length_eq_cut", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_LocalAlgebra_LocalIntersectionLength", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength:4090", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "fa83b47067c2f90c23f141f249e98790c90a71ac188c03e05e2270efe9dd81b8" }
  ]

run_meta do
  exportProviderSnapshotJsonl providerRequests "missions/pi-irrationality-measure/verification/providers-preview/all-shared-safe-leaves/snapshots/Def_OAI_NumberTheory_PiExponent_LocalAlgebra_LocalIntersectionLength/generated.jsonl"
