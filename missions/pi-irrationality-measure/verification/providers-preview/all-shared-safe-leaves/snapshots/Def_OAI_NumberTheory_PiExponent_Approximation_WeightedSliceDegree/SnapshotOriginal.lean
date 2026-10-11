import Lean
import OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree

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
    { sourceGraphName := "OAI.PiExponent.WeightedSliceDegree.SupportBound.add", expectedUserName := "OAI.PiExponent.WeightedSliceDegree.SupportBound.add", expectedPublicName := "OAI.PiExponent.WeightedSliceDegree.SupportBound.add", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:1211", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "12264e03d7a97585309f8454bb60de1cb4ad76d12a210377c9990606fb7d4fd7" },
    { sourceGraphName := "OAI.PiExponent.WeightedSliceDegree.SupportBound.mul", expectedUserName := "OAI.PiExponent.WeightedSliceDegree.SupportBound.mul", expectedPublicName := "OAI.PiExponent.WeightedSliceDegree.SupportBound.mul", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:1522", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "9eb83a1842149e2279d017be1fe850b96d1e554ae1e029c8ff5507429d752251" },
    { sourceGraphName := "OAI.PiExponent.WeightedSliceDegree.SupportBound.pow", expectedUserName := "OAI.PiExponent.WeightedSliceDegree.SupportBound.pow", expectedPublicName := "OAI.PiExponent.WeightedSliceDegree.SupportBound.pow", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:1882", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "fac29544e4ccdb74d1a3d9c6894026eae8f50cb74258f5ee5a735ae2e007c951" },
    { sourceGraphName := "OAI.PiExponent.WeightedSliceDegree.SupportBound", expectedUserName := "OAI.PiExponent.WeightedSliceDegree.SupportBound", expectedPublicName := "OAI.PiExponent.WeightedSliceDegree.SupportBound", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:218", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "6214bed6f843cacdf9117a847141081453666ff41e11a73761f369e71917cb1b" },
    { sourceGraphName := "OAI.PiExponent.WeightedSliceDegree.supportBound_prod", expectedUserName := "OAI.PiExponent.WeightedSliceDegree.supportBound_prod", expectedPublicName := "OAI.PiExponent.WeightedSliceDegree.supportBound_prod", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:2289", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "a3c68dfda46fad9a86de3ae9a672a4aff8c5573ae3f72c5bc9b691b82c1b1f5f" },
    { sourceGraphName := "OAI.PiExponent.WeightedSliceDegree.supportBound_sum", expectedUserName := "OAI.PiExponent.WeightedSliceDegree.supportBound_sum", expectedPublicName := "OAI.PiExponent.WeightedSliceDegree.supportBound_sum", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:2902", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "815c4bfeb3cac70ded83f97a7f73516f4ea665ef70ff5559305bfffe9aeb0159" },
    { sourceGraphName := "OAI.PiExponent.WeightedSliceDegree.supportBound_aeval_monomial", expectedUserName := "OAI.PiExponent.WeightedSliceDegree.supportBound_aeval_monomial", expectedPublicName := "OAI.PiExponent.WeightedSliceDegree.supportBound_aeval_monomial", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:3416", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "116b2949783f6e85b7835c933588a5557eecfeaff570ed29ca9bb4af1653be1a" },
    { sourceGraphName := "OAI.PiExponent.WeightedSliceDegree.SupportBound.mono", expectedUserName := "OAI.PiExponent.WeightedSliceDegree.SupportBound.mono", expectedPublicName := "OAI.PiExponent.WeightedSliceDegree.SupportBound.mono", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:350", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "83ad989a532e2f03f34123bee9ba926ddf25d97fd7d3d0d4f2be1c3851c341d2" },
    { sourceGraphName := "OAI.PiExponent.WeightedSliceDegree.supportBound_aeval", expectedUserName := "OAI.PiExponent.WeightedSliceDegree.supportBound_aeval", expectedPublicName := "OAI.PiExponent.WeightedSliceDegree.supportBound_aeval", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:4123", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "c69ecfcabf3011e35eec8d7aa451b14971d4f7c23938c0a689fab48ef4e3f6f6" },
    { sourceGraphName := "OAI.PiExponent.WeightedSliceDegree.sliceMap", expectedUserName := "OAI.PiExponent.WeightedSliceDegree.sliceMap", expectedPublicName := "OAI.PiExponent.WeightedSliceDegree.sliceMap", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:4618", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "f7c34deff4197e19a4dc504251cb8c7e18198281c161a8c1c2c13726e5dc91d2" },
    { sourceGraphName := "OAI.PiExponent.WeightedSliceDegree.supportBound_zero", expectedUserName := "OAI.PiExponent.WeightedSliceDegree.supportBound_zero", expectedPublicName := "OAI.PiExponent.WeightedSliceDegree.supportBound_zero", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:541", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "dc441061a873843e7f236da8a53a943be85bb5945bc66072859af8a02aebf90c" },
    { sourceGraphName := "OAI.PiExponent.WeightedSliceDegree.supportBound_C", expectedUserName := "OAI.PiExponent.WeightedSliceDegree.supportBound_C", expectedPublicName := "OAI.PiExponent.WeightedSliceDegree.supportBound_C", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:681", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "fa34c21af3357b4f45ec908a088d1f69bfa72532546a75ec3fbda4e4cd622bd9" },
    { sourceGraphName := "OAI.PiExponent.WeightedSliceDegree.enumeratedSliceMap", expectedUserName := "OAI.PiExponent.WeightedSliceDegree.enumeratedSliceMap", expectedPublicName := "OAI.PiExponent.WeightedSliceDegree.enumeratedSliceMap", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree", expectedKind := "def", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:7687", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "3ff12dc9ca0b977a5200e3434b009b70e1710b00d2893d88c4da20528dd94220" },
    { sourceGraphName := "OAI.PiExponent.WeightedSliceDegree.supportBound_X", expectedUserName := "OAI.PiExponent.WeightedSliceDegree.supportBound_X", expectedPublicName := "OAI.PiExponent.WeightedSliceDegree.supportBound_X", expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree", expectedKind := "theorem", sourceWasPrivate := false, commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:904", declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4", declGraphRowSha256 := "2699342205e057af34d3335b2de8e35a9af01d1632b928dfe0c7928f60d2445c" }
  ]

run_meta do
  exportProviderSnapshotJsonl providerRequests "missions/pi-irrationality-measure/verification/providers-preview/all-shared-safe-leaves/snapshots/Def_OAI_NumberTheory_PiExponent_Approximation_WeightedSliceDegree/original.jsonl"
