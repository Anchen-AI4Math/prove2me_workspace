import Lean
import Definitions.Def_OAI_NumberTheory_PiExponent_Jets_JetGeometry

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
    { sourceGraphName := "OAI.PiExponent.JetGeometry.weightedIdeal_mul_le", expectedUserName := "OAI.PiExponent.JetGeometry.weightedIdeal_mul_le", expectedPublicName := "OAI.PiExponent.JetGeometry.weightedIdeal_mul_le", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Jets_JetGeometry", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:1210", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "7b28b25164269ba9da07688fa8f7f6924c579c837cd203342102db1b73a85109" },
    { sourceGraphName := "OAI.PiExponent.JetGeometry.ideal_pow_le_weightedIdeal", expectedUserName := "OAI.PiExponent.JetGeometry.ideal_pow_le_weightedIdeal", expectedPublicName := "OAI.PiExponent.JetGeometry.ideal_pow_le_weightedIdeal", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Jets_JetGeometry", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:1576", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "bad24716e0a034c49b54be6f2762c3f73e93ea0d27285741e6698f6347e99ded" },
    { sourceGraphName := "OAI.PiExponent.JetGeometry.coordinatePowerIdeal", expectedUserName := "OAI.PiExponent.JetGeometry.coordinatePowerIdeal", expectedPublicName := "OAI.PiExponent.JetGeometry.coordinatePowerIdeal", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Jets_JetGeometry", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:2101", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "a575c534cf80c72e21edf89cc1a60779c22fbe299dc74757e16986cb381a2837" },
    { sourceGraphName := "OAI.PiExponent.JetGeometry.weightedIdeal", expectedUserName := "OAI.PiExponent.JetGeometry.weightedIdeal", expectedPublicName := "OAI.PiExponent.JetGeometry.weightedIdeal", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Jets_JetGeometry", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:242", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "8cb1a802cafb0361ff351c30d8a45bdc4f5754650412adba9ab385e0e0c77dfe" },
    { sourceGraphName := "OAI.PiExponent.JetGeometry.rational_weight_nonneg", expectedUserName := "OAI.PiExponent.JetGeometry.rational_weight_nonneg", expectedPublicName := "OAI.PiExponent.JetGeometry.rational_weight_nonneg", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Jets_JetGeometry", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:5300", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "145957c9d66989b99ab728b31a34ee27799f9bb04055753d99285b284d44e7a5" },
    { sourceGraphName := "OAI.PiExponent.JetGeometry.rationalWeightedIdeal", expectedUserName := "OAI.PiExponent.JetGeometry.rationalWeightedIdeal", expectedPublicName := "OAI.PiExponent.JetGeometry.rationalWeightedIdeal", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Jets_JetGeometry", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:5541", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "32e325a1c11e414b39019959f83051c27016287422cee716bcace50a5a3535ab" },
    { sourceGraphName := "OAI.PiExponent.JetGeometry.rationalWeightedIdeal_mul_le", expectedUserName := "OAI.PiExponent.JetGeometry.rationalWeightedIdeal_mul_le", expectedPublicName := "OAI.PiExponent.JetGeometry.rationalWeightedIdeal_mul_le", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Jets_JetGeometry", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:6508", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "c7a70188525fc890c67a077bfec446ceb268773749dff6cd2e91ee7fb209a3cf" },
    { sourceGraphName := "OAI.PiExponent.JetGeometry.ideal_pow_le_rationalWeightedIdeal", expectedUserName := "OAI.PiExponent.JetGeometry.ideal_pow_le_rationalWeightedIdeal", expectedPublicName := "OAI.PiExponent.JetGeometry.ideal_pow_le_rationalWeightedIdeal", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Jets_JetGeometry", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:7291", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "c640e38a19b84b7b3073d3f47da7aa8542cba885f95fceac250dc1233cb68f87" },
    { sourceGraphName := "OAI.PiExponent.JetGeometry.mem_weightedIdeal_iff", expectedUserName := "OAI.PiExponent.JetGeometry.mem_weightedIdeal_iff", expectedPublicName := "OAI.PiExponent.JetGeometry.mem_weightedIdeal_iff", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Jets_JetGeometry", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:794", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "adfff4f12f12cf3f5cee56068b4704be75f9f9d863f85129bad549fe61295ba7" },
    { sourceGraphName := "OAI.PiExponent.JetGeometry.RationalCoefficientPacket", expectedUserName := "OAI.PiExponent.JetGeometry.RationalCoefficientPacket", expectedPublicName := "OAI.PiExponent.JetGeometry.RationalCoefficientPacket", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Jets_JetGeometry", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:8569", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "f2f3b033afc8e54fd7366ac8149e75168d90ecc52f2f99aeadf8bba381de2d7a" },
    { sourceGraphName := "OAI.PiExponent.JetGeometry.rationalCoefficientPacket", expectedUserName := "OAI.PiExponent.JetGeometry.rationalCoefficientPacket", expectedPublicName := "OAI.PiExponent.JetGeometry.rationalCoefficientPacket", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Jets_JetGeometry", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Jets.JetGeometry:8687", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "6b635bdb7ffbabfba37e1000b5b0da03e349af14fddea2ed72f868e90c7ed5f9" }
  ]

run_meta do
  exportProviderSnapshotJsonl providerRequests "missions/pi-irrationality-measure/verification/providers-context-preview/namespace-context/snapshots/Def_OAI_NumberTheory_PiExponent_Jets_JetGeometry/generated.jsonl"
