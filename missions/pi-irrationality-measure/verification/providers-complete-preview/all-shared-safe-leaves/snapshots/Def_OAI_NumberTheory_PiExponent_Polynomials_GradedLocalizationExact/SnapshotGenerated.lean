import Lean
import Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_GradedLocalizationExact

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
    { sourceGraphName := "OAI.PiExponent.GradedLocalizationExact.fraction_zero", expectedUserName := "OAI.PiExponent.GradedLocalizationExact.fraction_zero", expectedPublicName := "OAI.PiExponent.GradedLocalizationExact.fraction_zero", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_GradedLocalizationExact", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:1105", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "a2c711541849b7ec7560f1ae9ee5607b8495b2e1cadd3a60e74d7a3f606763e2" },
    { sourceGraphName := "OAI.PiExponent.GradedLocalizationExact.fraction_neg", expectedUserName := "OAI.PiExponent.GradedLocalizationExact.fraction_neg", expectedPublicName := "OAI.PiExponent.GradedLocalizationExact.fraction_neg", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_GradedLocalizationExact", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:1215", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "68d39e482ad1af38056654b59fef938cb388414c4e0114514996471a9bf69ef0" },
    { sourceGraphName := "OAI.PiExponent.GradedLocalizationExact.fraction_add", expectedUserName := "OAI.PiExponent.GradedLocalizationExact.fraction_add", expectedPublicName := "OAI.PiExponent.GradedLocalizationExact.fraction_add", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_GradedLocalizationExact", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:1342", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "691b36136f71ac7be7c3ccaa841e247715a9c4448afc1088843f2c328d5b531f" },
    { sourceGraphName := "OAI.PiExponent.GradedLocalizationExact.fraction_cancel", expectedUserName := "OAI.PiExponent.GradedLocalizationExact.fraction_cancel", expectedPublicName := "OAI.PiExponent.GradedLocalizationExact.fraction_cancel", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_GradedLocalizationExact", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:1620", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "b16ad0f130cce54138ea87efe5d4cb860e203304fda5f001fcdd2f1b4d854046" },
    { sourceGraphName := "OAI.PiExponent.GradedLocalizationExact.fraction_eq_zero", expectedUserName := "OAI.PiExponent.GradedLocalizationExact.fraction_eq_zero", expectedPublicName := "OAI.PiExponent.GradedLocalizationExact.fraction_eq_zero", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_GradedLocalizationExact", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:1930", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "c0561d93d158c5bb45fd84c53fcfdea9e6791e33672aba0908b6e48c154e2e0e" },
    { sourceGraphName := "OAI.PiExponent.GradedLocalizationExact.power_smul_mem", expectedUserName := "OAI.PiExponent.GradedLocalizationExact.power_smul_mem", expectedPublicName := "OAI.PiExponent.GradedLocalizationExact.power_smul_mem", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_GradedLocalizationExact", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:2560", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "2b5da4e0f3678eb22435353cf29bab6f35badf5af174698f9880d50285846d74" },
    { sourceGraphName := "OAI.PiExponent.GradedLocalizationExact.degreePiece", expectedUserName := "OAI.PiExponent.GradedLocalizationExact.degreePiece", expectedPublicName := "OAI.PiExponent.GradedLocalizationExact.degreePiece", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_GradedLocalizationExact", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:2871", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "a54578ff0ab0d19c621acd35323cb5cfa82f2f0d7812309e9538777cba79fc3c" },
    { sourceGraphName := "OAI.PiExponent.GradedLocalizationExact.localizedMap", expectedUserName := "OAI.PiExponent.GradedLocalizationExact.localizedMap", expectedPublicName := "OAI.PiExponent.GradedLocalizationExact.localizedMap", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_GradedLocalizationExact", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:3872", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "b68a7f3ca999331e50dfac88fc1c8da68823ded075d3cbf5b23aac7f041e6e32" },
    { sourceGraphName := "OAI.PiExponent.GradedLocalizationExact.localizedMap_fraction", expectedUserName := "OAI.PiExponent.GradedLocalizationExact.localizedMap_fraction", expectedPublicName := "OAI.PiExponent.GradedLocalizationExact.localizedMap_fraction", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_GradedLocalizationExact", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:4131", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "4cc54ea8f9b7c0ab2de68a42716d825614cd40deb5d87c3f7e983ed526910d90" },
    { sourceGraphName := "OAI.PiExponent.GradedLocalizationExact.pieceMap", expectedUserName := "OAI.PiExponent.GradedLocalizationExact.pieceMap", expectedPublicName := "OAI.PiExponent.GradedLocalizationExact.pieceMap", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_GradedLocalizationExact", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:4389", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "7badd76a902d54ea4eb2221d0222ebf92ce294edf959d5968836728af9d6626f" },
    { sourceGraphName := "OAI.PiExponent.GradedLocalizationExact.powerDenominator", expectedUserName := "OAI.PiExponent.GradedLocalizationExact.powerDenominator", expectedPublicName := "OAI.PiExponent.GradedLocalizationExact.powerDenominator", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_GradedLocalizationExact", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:458", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "2cf016b70e320088e230e6340f68ffb81e0d6c03b84a1e37c6a1e5c24007ef0d" },
    { sourceGraphName := "OAI.PiExponent.GradedLocalizationExact.preserves_of_compatible", expectedUserName := "OAI.PiExponent.GradedLocalizationExact.preserves_of_compatible", expectedPublicName := "OAI.PiExponent.GradedLocalizationExact.preserves_of_compatible", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_GradedLocalizationExact", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:5164", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "fb7dc3e85b8ed2c021bc3f8bff0807eafe71b5b6bd010b3d740474cddfe7086d" },
    { sourceGraphName := "OAI.PiExponent.GradedLocalizationExact.homogeneous_preimage", expectedUserName := "OAI.PiExponent.GradedLocalizationExact.homogeneous_preimage", expectedPublicName := "OAI.PiExponent.GradedLocalizationExact.homogeneous_preimage", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_GradedLocalizationExact", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:5532", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "42fcb10eb4563b2dd980a2fd8e3b437d776c25a0327febec7c15249072256ca7" },
    { sourceGraphName := "OAI.PiExponent.GradedLocalizationExact.pieceMap_surjective", expectedUserName := "OAI.PiExponent.GradedLocalizationExact.pieceMap_surjective", expectedPublicName := "OAI.PiExponent.GradedLocalizationExact.pieceMap_surjective", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_GradedLocalizationExact", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:5995", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "fa5059970225ff45296405f944062d74e6bf5d7420e05cec84116a6a5075eb92" },
    { sourceGraphName := "OAI.PiExponent.GradedLocalizationExact.powerDenominator_zero", expectedUserName := "OAI.PiExponent.GradedLocalizationExact.powerDenominator_zero", expectedPublicName := "OAI.PiExponent.GradedLocalizationExact.powerDenominator_zero", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_GradedLocalizationExact", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:660", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "413593ee3cc1ee67489fd73ab91aa25fcd8399e9e8036b643aaac958eff28b0b" },
    { sourceGraphName := "OAI.PiExponent.GradedLocalizationExact.pieceMap_exact", expectedUserName := "OAI.PiExponent.GradedLocalizationExact.pieceMap_exact", expectedPublicName := "OAI.PiExponent.GradedLocalizationExact.pieceMap_exact", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_GradedLocalizationExact", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:6712", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "413ffb6dc95c27521bf127df71ca4af6dee7c115c10541d165c5bb7c8d0385ed" },
    { sourceGraphName := "OAI.PiExponent.GradedLocalizationExact.powerDenominator_add", expectedUserName := "OAI.PiExponent.GradedLocalizationExact.powerDenominator_add", expectedPublicName := "OAI.PiExponent.GradedLocalizationExact.powerDenominator_add", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_GradedLocalizationExact", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:790", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "b11da4ff7156778f2b5da57e601fd1d3d7e7f77a3319d296c1e852f9e0eb48bb" },
    { sourceGraphName := "OAI.PiExponent.GradedLocalizationExact.fraction", expectedUserName := "OAI.PiExponent.GradedLocalizationExact.fraction", expectedPublicName := "OAI.PiExponent.GradedLocalizationExact.fraction", expectedModule := "Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_GradedLocalizationExact", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:972", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "1c87890a204b3afd977205b2ab8be54c59304c00d44d96bd6bdc4095abf51849" }
  ]

run_meta do
  exportProviderSnapshotJsonl providerRequests "missions/pi-irrationality-measure/verification/providers-complete-preview/all-shared-safe-leaves/snapshots/Def_OAI_NumberTheory_PiExponent_Polynomials_GradedLocalizationExact/generated.jsonl"
