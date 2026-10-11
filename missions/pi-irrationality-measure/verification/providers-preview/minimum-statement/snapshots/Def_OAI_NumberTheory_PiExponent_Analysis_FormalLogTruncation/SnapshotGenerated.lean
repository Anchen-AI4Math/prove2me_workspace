import Lean
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_FormalLogTruncation

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
    { sourceGraphName := "OAI.PiExponent.FormalLogTruncation.logTail", expectedUserName := "OAI.PiExponent.FormalLogTruncation.logTail", expectedPublicName := "OAI.PiExponent.FormalLogTruncation.logTail", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_FormalLogTruncation", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:12228", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "7059cab353e93dad43da92d68b12ca3340ad8cdd10ff085bf7f7cb6fd63896a2" },
    { sourceGraphName := "OAI.PiExponent.FormalLogTruncation.logTail_constantCoeff", expectedUserName := "OAI.PiExponent.FormalLogTruncation.logTail_constantCoeff", expectedPublicName := "OAI.PiExponent.FormalLogTruncation.logTail_constantCoeff", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_FormalLogTruncation", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:12375", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "6a2bec2a33cdf922bc0d9b4cd39d652b5078be38d988829848c1e38d318233c0" },
    { sourceGraphName := "OAI.PiExponent.FormalLogTruncation.coeff_logTail_eq_zero", expectedUserName := "OAI.PiExponent.FormalLogTruncation.coeff_logTail_eq_zero", expectedPublicName := "OAI.PiExponent.FormalLogTruncation.coeff_logTail_eq_zero", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_FormalLogTruncation", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:12577", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "f7ff2343de0159bbe6f7c9ce66c06cf7e3d930a1233a4f353754eb006f06a802" },
    { sourceGraphName := "OAI.PiExponent.FormalLogTruncation.truncatedFormalJet", expectedUserName := "OAI.PiExponent.FormalLogTruncation.truncatedFormalJet", expectedPublicName := "OAI.PiExponent.FormalLogTruncation.truncatedFormalJet", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_FormalLogTruncation", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:13808", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "db33108348d20b5b45e87b9d8562e28fba263be2e4a9e3cd5457a3b411dcb6f9" },
    { sourceGraphName := "OAI.PiExponent.FormalLogTruncation.shiftVars", expectedUserName := "OAI.PiExponent.FormalLogTruncation.shiftVars", expectedPublicName := "OAI.PiExponent.FormalLogTruncation.shiftVars", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_FormalLogTruncation", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:1560", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "b3ef70191454e1517227942e8a21eb5ef62eb87a92b55433d62b15511677feaa" },
    { sourceGraphName := "OAI.PiExponent.FormalLogTruncation.shiftVars_hasSubst", expectedUserName := "OAI.PiExponent.FormalLogTruncation.shiftVars_hasSubst", expectedPublicName := "OAI.PiExponent.FormalLogTruncation.shiftVars_hasSubst", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_FormalLogTruncation", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:1754", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "ad59535979bf669ba282d2622e0a8aa8eb1a059831af188918af89bedbe6278f" },
    { sourceGraphName := "OAI.PiExponent.FormalLogTruncation.shiftMap", expectedUserName := "OAI.PiExponent.FormalLogTruncation.shiftMap", expectedPublicName := "OAI.PiExponent.FormalLogTruncation.shiftMap", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_FormalLogTruncation", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:2212", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "2d67a334735de0ce0cbd5ed424e3ab1712706a26c4f53aed8d8b814d651a4780" },
    { sourceGraphName := "OAI.PiExponent.FormalLogTruncation.shiftMap_X_zero", expectedUserName := "OAI.PiExponent.FormalLogTruncation.shiftMap_X_zero", expectedPublicName := "OAI.PiExponent.FormalLogTruncation.shiftMap_X_zero", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_FormalLogTruncation", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:2463", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "c77127ce9c1356f570e6db1fed914bff084236e58727dac2d3128c25409bed3b" },
    { sourceGraphName := "OAI.PiExponent.FormalLogTruncation.shiftMap_X_succ", expectedUserName := "OAI.PiExponent.FormalLogTruncation.shiftMap_X_succ", expectedPublicName := "OAI.PiExponent.FormalLogTruncation.shiftMap_X_succ", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_FormalLogTruncation", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:2680", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "8794b72880dfe300220df557d61ea2c43e35837f6a08fc634ceae06c9edcecef" },
    { sourceGraphName := "OAI.PiExponent.FormalLogTruncation.shiftMap_toMvPowerSeries", expectedUserName := "OAI.PiExponent.FormalLogTruncation.shiftMap_toMvPowerSeries", expectedPublicName := "OAI.PiExponent.FormalLogTruncation.shiftMap_toMvPowerSeries", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_FormalLogTruncation", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:2948", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "94254c5f5ca9b475c60da1226d1e961ebe8e37c57b3ddb143359a4909edf78d0" },
    { sourceGraphName := "OAI.PiExponent.FormalLogTruncation.shiftMap_apply", expectedUserName := "OAI.PiExponent.FormalLogTruncation.shiftMap_apply", expectedPublicName := "OAI.PiExponent.FormalLogTruncation.shiftMap_apply", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_FormalLogTruncation", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:3738", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "2af74c3d76107dbed36459dde797b8e5de723b838f089697160be4dcfe8239f8" },
    { sourceGraphName := "OAI.PiExponent.FormalLogTruncation.shiftMap_inverse", expectedUserName := "OAI.PiExponent.FormalLogTruncation.shiftMap_inverse", expectedPublicName := "OAI.PiExponent.FormalLogTruncation.shiftMap_inverse", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_FormalLogTruncation", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:3955", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "c00a365b065dc7b70a52037b49a0b2c46ec40e5c40edd78d97890cd122885cf2" },
    { sourceGraphName := "OAI.PiExponent.FormalLogTruncation.shiftEquiv", expectedUserName := "OAI.PiExponent.FormalLogTruncation.shiftEquiv", expectedPublicName := "OAI.PiExponent.FormalLogTruncation.shiftEquiv", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_FormalLogTruncation", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:4823", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "8cb02284393971870cf7f485d61e89645f85e1c3985fc20701eaa3f6d04e665e" },
    { sourceGraphName := "OAI.PiExponent.FormalLogTruncation.rationalWeightedIdeal_prod", expectedUserName := "OAI.PiExponent.FormalLogTruncation.rationalWeightedIdeal_prod", expectedPublicName := "OAI.PiExponent.FormalLogTruncation.rationalWeightedIdeal_prod", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_FormalLogTruncation", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:5661", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "f33b3cab9cc487d18eade93b242ccbb9a27f685ca1af3c659db52c244d47eb10" },
    { sourceGraphName := "OAI.PiExponent.FormalLogTruncation.subst_mem_rationalWeightedIdeal", expectedUserName := "OAI.PiExponent.FormalLogTruncation.subst_mem_rationalWeightedIdeal", expectedPublicName := "OAI.PiExponent.FormalLogTruncation.subst_mem_rationalWeightedIdeal", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_FormalLogTruncation", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:6447", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "1bf053ca81251ec2cbf33428c957a43265d3deb25aac9046cadcf4ee2f5de964" },
    { sourceGraphName := "OAI.PiExponent.FormalLogTruncation.X_mem_rationalWeightedIdeal", expectedUserName := "OAI.PiExponent.FormalLogTruncation.X_mem_rationalWeightedIdeal", expectedPublicName := "OAI.PiExponent.FormalLogTruncation.X_mem_rationalWeightedIdeal", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_FormalLogTruncation", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:7566", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "ab939267d023965bb36e7cd46023573b53f8fe31d471f942e24afd72ff915e73" },
    { sourceGraphName := "OAI.PiExponent.FormalLogTruncation.shiftMap_mem_rationalWeightedIdeal", expectedUserName := "OAI.PiExponent.FormalLogTruncation.shiftMap_mem_rationalWeightedIdeal", expectedPublicName := "OAI.PiExponent.FormalLogTruncation.shiftMap_mem_rationalWeightedIdeal", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_FormalLogTruncation", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:7928", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "09b3ae79cd663ff613fba39d696d837f7ebfdc2235baa115eb917706a55ec6e2" },
    { sourceGraphName := "OAI.PiExponent.FormalLogTruncation.rationalCoefficientPacket_eq_iff", expectedUserName := "OAI.PiExponent.FormalLogTruncation.rationalCoefficientPacket_eq_iff", expectedPublicName := "OAI.PiExponent.FormalLogTruncation.rationalCoefficientPacket_eq_iff", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_FormalLogTruncation", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:8700", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "ca72225d9e769499eb473f5b1d87137d10704a15162224da79bd2ddafe35b19a" }
  ]

run_meta do
  exportProviderSnapshotJsonl providerRequests "missions/pi-irrationality-measure/verification/providers-preview/minimum-statement/snapshots/Def_OAI_NumberTheory_PiExponent_Analysis_FormalLogTruncation/generated.jsonl"
