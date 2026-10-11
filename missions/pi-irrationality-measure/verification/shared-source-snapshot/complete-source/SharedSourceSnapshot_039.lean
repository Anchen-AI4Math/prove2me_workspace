import Lean
import OAI.NumberTheory.PiExponent.Main

open Lean Meta

namespace PiExponentSharedSourceSnapshot

/- A request is text-backed on purpose.  The exporter resolves sourceName by
walking Environment.constants and retaining the actual Name object.  In
particular, private numeric Name components are never reconstructed from a
printed string. -/
structure SourceRequest where
  sourceName : String
  expectedModule : String
  graphKind : String
  declGraphSha256 : String
  declGraphRowSha256 : String
  ownerKind : String
  ownerId : String
  commandUnit : String

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

-- This is the same kernel-relevant Expr encoding used by TypedSnapshotCore.
-- Binder display names and source metadata intentionally do not occur in it.
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
  | .defnInfo d => Json.mkObj [
      ("valueExported", toJson true),
      ("safety", toJson (reprStr d.safety))]
  | .axiomInfo a => Json.mkObj [("isUnsafe", toJson a.isUnsafe)]
  | .opaqueInfo o => Json.mkObj [
      ("valueExported", toJson false),
      ("isUnsafe", toJson o.isUnsafe)]
  | .inductInfo i => Json.mkObj [
      ("numParams", toJson i.numParams),
      ("numIndices", toJson i.numIndices),
      ("all", toJson (i.all.map Name.toString)),
      ("constructors", toJson (i.ctors.map Name.toString)),
      ("numNested", toJson i.numNested),
      ("isRecursive", toJson i.isRec),
      ("isUnsafe", toJson i.isUnsafe),
      ("isReflexive", toJson i.isReflexive)]
  | .ctorInfo c => Json.mkObj [
      ("inductive", toJson c.induct.toString),
      ("constructorIndex", toJson c.cidx),
      ("numParams", toJson c.numParams),
      ("numFields", toJson c.numFields),
      ("isUnsafe", toJson c.isUnsafe)]
  | .recInfo r => Json.mkObj [
      ("all", toJson (r.all.map Name.toString)),
      ("numParams", toJson r.numParams),
      ("numIndices", toJson r.numIndices),
      ("numMotives", toJson r.numMotives),
      ("numMinors", toJson r.numMinors),
      ("ruleConstructors", toJson (r.rules.map (fun rule => rule.ctor.toString))),
      ("supportsK", toJson r.k),
      ("isUnsafe", toJson r.isUnsafe)]
  | .quotInfo _ => Json.mkObj []

def moduleFor? (env : Environment) (name : Name) : Option Name :=
  match env.getModuleIdxFor? name with
  | some idx => env.header.moduleNames[idx.toNat]?
  | none => none

def isClosed (e : Expr) : Bool :=
  !e.hasMVar && !e.hasFVar && !e.hasLooseBVars

def actualNameIndex (env : Environment) : MetaM (Std.HashMap String Name) := do
  let mut index : Std.HashMap String Name := {}
  for (name, _) in env.constants.toList do
    let key := name.toString
    if let some prior := index.get? key then
      unless prior == name do
        throwError "Environment Name.toString collision: {key}"
    else
      index := index.insert key name
  return index

/- Stream one compact object per line.  Only DefinitionVal values are emitted.
Theorem proof terms are deliberately absent; theorem rows certify their types,
module ownership, kinds and axioms. -/
def exportSourceSnapshotJsonl (requests : Array SourceRequest) (output : String) : MetaM Unit := do
  let env ← getEnv
  let index ← actualNameIndex env
  let handle ← IO.FS.Handle.mk output .write
  for request in requests do
    let some name := index.get? request.sourceName
      | throwError "Source declaration string is absent from Environment.constants: {request.sourceName}"
    let some ci := env.find? name
      | throwError "Resolved source declaration is absent from the environment: {name}"
    let some actualModule := moduleFor? env name
      | throwError "Source declaration has no imported module owner: {name}"
    unless actualModule.toString == request.expectedModule do
      throwError "Source module mismatch for {name}: graph={request.expectedModule}, env={actualModule}"
    let actualKind := envKind ci
    unless actualKind == request.graphKind do
      throwError "Source kind mismatch for {name}: graph={request.graphKind}, env={actualKind}"
    unless isClosed ci.type do
      throwError "Source declaration type is not closed: {name}"
    let value := match ci with
      | .defnInfo d => some d.value
      | _ => none
    if let some v := value then
      unless isClosed v do
        throwError "Source definition value is not closed: {name}"
    let axioms ← Lean.collectAxioms name
    let axiomNames := axioms.toList.map Name.toString
      |>.mergeSort (fun a b => compare a b == .lt)
    let row := Json.mkObj [
      ("schemaVersion", toJson 1),
      ("sourceName", toJson name.toString),
      ("sourceModule", toJson actualModule.toString),
      ("declGraphSha256", toJson request.declGraphSha256),
      ("declGraphRowSha256", toJson request.declGraphRowSha256),
      ("graphKind", toJson request.graphKind),
      ("envKind", toJson actualKind),
      ("ownerKind", toJson request.ownerKind),
      ("ownerId", toJson request.ownerId),
      ("commandUnit", toJson request.commandUnit),
      ("levelParams", toJson (ci.levelParams.map Name.toString)),
      ("closedType", toJson true),
      ("closedValue", value.map (fun _ => toJson true) |>.getD Json.null),
      ("type", exprJson ci.type),
      ("value", value.map exprJson |>.getD Json.null),
      ("axioms", toJson axiomNames),
      ("kindMetadata", kindMetadata ci)]
    handle.putStrLn row.compress
  handle.flush

end PiExponentSharedSourceSnapshot

open PiExponentSharedSourceSnapshot

def sharedSourceRequests : Array SourceRequest := #[
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.sectionOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "221226c2452294698d178816b11a34d9a05afbe1198596ae9918ec01996eb227",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:1070",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:1070"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.sectionOpen_le_powerSection",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPowerRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "702c930bbfebdf29060d845c096306af43d9f5106318791a6ffc8de7425e53a6",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPowerRestriction:3112",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPowerRestriction:3112"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.sectionOpen_pullbackPowerSection",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "432fca446780031ae030102e749655acc288a906f243aacd7a66faffa82b2a83",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleRestriction:1827",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleRestriction:1827"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.section_eq_zero_of_local_restrictions",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionDivision",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "96b0cfc16c6a766734bf5211e76ada1d3cf6c7a93c1bac6d1974af2287d7df1a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionDivision:1183",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionDivision:1183"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.section_eq_zero_of_top_value",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionDivision",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "48388eeaf1501859fcca5c5b4939954d8822aea37547b3190f0d79780d334a5b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionDivision:761",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionDivision:761"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.section_value_naturality",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionDivision",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8e38deb5d6ecbce7cbad0f77eba765212b1b95cc1c73039411e457774e91c85a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionDivision:293",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionDivision:293"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.sheafComplexLinear",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fc7eb98fb9ada35753c4f9ea4ba29177652440a8cfd0a5230e75e36cefeffc9e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact:6884",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact:6884"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.sheafHomModule",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0cf16f544c2dda4098064f86c536cd249df88b26e73fcf9b339f2241c2514f4a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler:2050",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler:2050"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.sheafHomSMul",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d5cf8efc8818f5228cfa86f9611577297ec0195e8bbbea80e57847aa5d0850cc",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler:776",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler:776"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.sheafLinear",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4abbb4bace4e237630700ccab3605c106197caa183f12db735c9c6304c347320",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler:3046",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler:3046"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.sheafificationTensorLeft",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "78c52fd6adb54d779aaaf3fcf5e24f8eca6c5d0e0e5f25c65c62d039753f9ed6",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws:7536",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws:7536"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.sheafificationTensorLeftLinePair",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ModuleLinePowerLaws",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f693d9fe8774f5d64069de89fa4d692f2f6e15b57a526afea1104e5b447e589e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ModuleLinePowerLaws:5175",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ModuleLinePowerLaws:5175"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.sheafificationTensorRight",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "22a04107f548dda9e1965a4099b339586044e02f1bb5ba19b0dba7de1b8cc67a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws:6565",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws:6565"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.sheafification_tensor_left_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "46e3e42d8d026a174d493aa3351236a74421de09b7b2bfbf9455665c9c49f520",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws:5289",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws:5289"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.sheafification_tensor_left_line_unit_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ModuleLinePowerLaws",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "57314d7e71fe89d5fd845aa02e8bcacbc364f0e77be4c183635d0e4d7fe11049",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ModuleLinePowerLaws:2475",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ModuleLinePowerLaws:2475"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.sheafification_tensor_right_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b61057edea13c4de40d116f179ea1aa90dcc0ff75016fe95b93a95814298e9a8",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws:2124",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws:2124"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.sheafification_unit_isIso_of_iso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SheafificationUnitIso",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ea54fcd18839ee6d2af437eb69c6085ca78414f2bb2848e46052dd16239a2b12",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SheafificationUnitIso:419",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SheafificationUnitIso:419"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.structuralStalkAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "369389d315ff6f3265558ef8485c555db28521e2b9e8ccabbcdb17e02f4c183d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros:7331",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros:7331"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.structureSheaf",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "69a07d1e79854697dae1044ff14b8737e8f3e02fa902c3f12316211815e79c4d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:931",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:931"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.subscheme_surjective_of_fullSupport",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedThickeningSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e6b7401d77cffcfe0311f7238ca0188c6f6a10daf7dd8e74cb2d75dd96ba3067",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedThickeningSections:1987",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedThickeningSections:1987"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.support_comap_ne_top_of_open",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e96395e50a42ea9a69ef65b2774a8b85a16cfd1d3dbf72491088f8d79b359da8",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:7431",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:7431"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.tensorFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "90b17f65c70d5a6977c19a2b7e95ce7bb9331b410118021aa2ff400067a9a29f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen:450",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen:450"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.tensorInclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TensorIdealInclusion",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "57f11ea7ca5f617c343cb139fc05961ed0dfcbe5843878c34d67da4b6c67ac5e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TensorIdealInclusion:952",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TensorIdealInclusion:952"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.tensorInclusion_mono",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TensorIdealInclusion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8915012b7b471f3c4f7dd79a101071f121bbd8cba91090b2d0a1cc5d7814e971",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TensorIdealInclusion:4932",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TensorIdealInclusion:4932"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.tensorUnitTwist",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TensorIdealInclusion",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "61f32564f0da58af068e6fbee75fccd495d7502b12d49db2dd1a3cb6a2486171",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TensorIdealInclusion:410",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TensorIdealInclusion:410"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.tensor_inclusion_framed",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TensorIdealInclusion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f278cd24d136fc71b90b9625b5eda3af2c8c8dbe8fd6dfed65daba68e634f475",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TensorIdealInclusion:2219",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TensorIdealInclusion:2219"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.tensor_inclusion_ideal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TensorIdealInclusion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "14c30d2baf6703abd5b861dac26235b0c560821054253174b794a150a6e62557",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TensorIdealInclusion:5959",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TensorIdealInclusion:5959"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.tensor_unit_end",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameTensorPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5643d470c8902a1e1717f2a8df93e6b249ec706de68250aea161bb23b5688cde",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameTensorPowers:308",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameTensorPowers:308"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.trivialModule_restriction_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.IntegralLineSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "db301cdef594158a5c73920a56fcbd0f2bdc263cf9d29e6ff026a83e7a8a7186",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.IntegralLineSections:271",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.IntegralLineSections:271"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.twoAffineCohomologyOne",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c9a06f5c2aaa6ec034a223e8bd853be3ab8ad5ac4bb13f742aab0a72ece33d80",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech:7381",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech:7381"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.twoAffineUnionExtOne",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7c947fc42d2eeba59b1e747eaf06c8c9d67587743757875088c181e10577a5b8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech:5560",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech:5560"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.twoChartImage",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "912bf596f2f9bd287a78175e5acc004a6fda6c5806e451f56b61067e8a2a62cf",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech:2703",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech:2703"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.twoChartImage_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "119c4207e6e393c2f48fb63b53bc9517e679d6b9f00468ba16c5c755bd51b3ca",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech:2952",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech:2952"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.unitPowerIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d8caee0700b9ac7559a943834f04b42c22c63c449213361115296f444bff10c2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:12933",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:12933"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.closedInclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "80a037704bbaf18f979212bd81d9509520e0cb90951e9065d5cb4c9e5c05fab6",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:3071",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:3071"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.closedInclusion_mono",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "66d9549027f7544de84e8daa91c81a71336ada548796f72b42be3111e6879cf1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:541",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:541"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.closedInclusion_structureMap_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "53a9a7646620022a8dae7f63fdc83cbb60f8e80a30e5a45c88469e93055b4f05",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:679",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:679"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.closedMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "897de68c12d70c916ff3b37ca9c76d1a5d9c06a063c912c251948aadb29008c1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:1348",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:1348"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.closedMap_inclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f68fb0a70e0f432622e6d17c5e9c64aeb84875e78eb4a90dc60c878e8ee26228",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:1553",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:1553"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.closedMap_inclusion_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d7437d0683fbb6f429eca81f3edf1f5eaba10a58319a5a9bc543d2bd640cc546",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:1553",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:1553"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.closedMap_mono",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5f447d25bd5304b0ad594f59a16b1c8be2ca2685121061af3117d01ec4affe05",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:1732",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:1732"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.closedModule",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ed783f691834d38ef11e1e38eb819065a693638a7faa676e01ac58dbea0012e2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:2987",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:2987"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.closedModuleRestrictIso",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6d7b9792f1d09df8ca2ab0f82febbebcc2de52ea636d6120e5038a3e7f2e3b02",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction:2777",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction:2777"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.closedModuleRestrictIso_naturality",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e17935ca67423ac68b6b8792f36ebbb97d139036442673615f2174d5687318e4",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction:2963",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction:2963"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.closedModule_bot_isZero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eea58df58bb4b332b4b560fad0d2fd38bfa0e099e95f1df6bb7d27bc06851d1c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:3183",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:3183"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.closedModule_isFinitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7ed9c700a02f5b5dbcb6e1590f87409a749030726471ff26ede962507b234721",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:3666",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:3666"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.closedQuotientCongr",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1cb1ad7c7a838e6c4573896a5cd479cd49b604eca521b071479d695b7dfd83e8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction:750",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction:750"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.closedQuotientRestrictIso",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "45cc9782c604ad0dae61097d9de00932d7e09efcf916dcd7b74acdbfc4ccd321",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction:308",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction:308"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.closedSequence_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a44f57b1839069e0a02ded883bf728b7d640115c059cfd366bcd3579c178e662",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:9417",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:9417"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.closed_image",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0602ae8f45df3542cb4ac9ff15ecb30fc6c93a1e24551921ab4772d95ebd7fe4",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:3175",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:3175"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.descendedPowerLayer",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerDescent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "76d8b81bf91ff9bf4f095b8b2c4596d14e1cd2dccd3a8f09b830ba5f620fb9fb",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerDescent:743",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerDescent:743"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.descendedPowerLayer_isFinitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerDescent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1952651a025c89ad883804196b9f257d85774a9c99a65dcb36d39306960bb360",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerDescent:892",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerDescent:892"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.equationToIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "70b0e067c2aa2fe06cde2b963d7fd57c51d8707e6492eabde355439f2ff4d755",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:5265",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:5265"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.equationToIdeal_app",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "183fa9d6e36e0b9a2c86d0a1723c50ebdca58d424382577ffc8bd068e6c919e1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:5662",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:5662"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.equationToIdeal_inclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3d036d8a27326c7f6798a609b2f841f2c3517cf2cc946bbf00a49cdf2c1e1a75",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:5457",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:5457"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.equationToIdeal_inclusion_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f8933a00c55d902844607b4b988fafb552011e932f2c2e528106508b2956f49c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:5457",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:5457"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.eventual_ideal_twist_vanishing_of_layers",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.IdealPowerCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3d992fcfdf761df982a5d6aad8965120962d64527d066941cd8d7f9361a43b27",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.IdealPowerCohomology:2743",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.IdealPowerCohomology:2743"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.ext_eq_zero_of_isZero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.IdealPowerCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "175fd6e3c4f4167b8e6647c059f68baa0460c0d00e8a9987c98d9b6ac6ca4b81",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.IdealPowerCohomology:512",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.IdealPowerCohomology:512"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.frameOnRange",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "97590e3324712e7ddc9122b8758dd9ce660195d37997a3c4849b4206a66f5dab",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:8211",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:8211"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.frame_restriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "182d361dfcbf77bab03d5fe1968660e876d2a580fe6f694a22022b7f16f70cc5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:7009",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:7009"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.fromSection",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b95175cc5132e958715200526b0cb39392f13638e7ca6e3ff650e35c94348e82",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:1877",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:1877"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.fromSection_app",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "63f3fe925d55c76ceb52666fd701ad8a8df771fa8cf71e7417db9d430c186456",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:1988",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:1988"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.fromSection_inclusion_app",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "89ea5c09f078203c43681ce62e9da9bf8b0fddd87020dadd43a77fe10957bb7d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:2180",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:2180"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.hom_ext_affine",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6fb6bf6eae7524317299f2bc012a721ca4d103270a75d89ff1196b8c7a72e7c3",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator:362",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator:362"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.idealModule",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e1578b22f93ca39b05bda48bd21ddcbbcf35c0b60fd44a94abb410d4c4423277",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:792",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:792"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.image_eq_ideal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1c38d8528f383b8a7e48f410c053f08dc633f31f68dc9bc6e53ee2bc942c1a2e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:2679",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:2679"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.image_eq_kernel",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e176fad2b00f71b01460598b74c69ea7742ce275324bed8bf5ab5f1544ca047e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:2064",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:2064"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.inclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "62bfbb95c4d51adace1a7e3f7cd42aa787032a9e77ccfcdf463cf72aea9a47a0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:850",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:850"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.instHasExtModules_oAI",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.IdealPowerCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "40dd8f77e3a38d30a072a5859c64482c1277fea368343990c64082f1a747461e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.IdealPowerCohomology:450",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.IdealPowerCohomology:450"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.instMonoModulesInclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1c519f9d616a57d574b8b323648f8325410646fcb20ac655443769065277f7a1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:927",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:927"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.isIso_equationToIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a26cb2006728912ceb398afaac99ea299d43397aa7072a9390a32ace6ca0c1a0",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:5991",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:5991"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.isIso_fromSection",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cef9519d3de1d0dbcd115e6fc9f9068fd0882ecb84ca224e1c95e9f0a71484db",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:3098",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:3098"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.isIso_of_affine_app",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ac5cdb4af86d6b7dae105acfb0c3ea609b0cde524cd737c6128159ce7b9069b1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:3412",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:3412"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.ker_appTop_subscheme_morphismRestrict",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "31cd56983570c967b3838224b316d3dc683ec3ff574323c3feb0a027611a9711",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction:2701",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction:2701"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.ker_subscheme_morphismRestrict",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fd3b9bff166f2e9981c59f9a3e341825a3b59c8b31a0f7bb00b63bc97db8163b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction:2276",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction:2276"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.multiply",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b61818884efc9e90b847f792c79056f19d4df2d1cc35a3a239f14ebc9957de5f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:3993",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:3993"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.multiplyToNextPower",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "26e60ae4076dc2f31d88b5ee155f89c7482a1cc9e8885d5debc1b7febbb4cec0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator:2115",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator:2115"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.multiplyToNextPower_inclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fe7ff867a175683b4ba1dba248ae73722ad192583ed0a16083746a87285d1e21",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator:2426",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator:2426"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.multiplyToNextPower_inclusion_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f4e106a360512788386b5fdc628eaebd3b52a5f56f611a2ade1b50b4ea24e035",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator:2426",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator:2426"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.multiplyToNextPower_powerMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e70532e6159b2818170039f2e7620271a07ec7055e87b727160341158019102d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator:2702",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator:2702"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.multiply_structure_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ec083c5d313035fcb31fb9f08904c48bcbf90ab64aa13d0f90d15446d31ac8d7",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:4787",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:4787"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.powerLayer",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7c3dcf9bab1c7b24944320e791f7d51bf3f126cf08e6bd2b89af7c3d3c1b56d8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:2631",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:2631"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.powerLayerPushforwardIso",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerDescent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5485af9e5f8bde57c6fa456ab7b685b4828be62cdcb6b10a9ba08f2c39a5d165",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerDescent:1179",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerDescent:1179"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.powerLayerRestrictIso",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3fe3dc33024e243099c92d34f570703af4754ec394909ea7274549edb025ba4a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction:975",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction:975"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.powerLayer_isFinitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e9a6df64dae93e2fcedcb86e3b5a5f166a9c84e09557bc5ac0fdc27e0cd9e113",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:4443",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:4443"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.powerLayer_locallyAnnihilated",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerDescent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a64d1fb5fe71710412c1a9ef8f8162cb92e0b7a1a6c178b615f5ae57c17741d8",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerDescent:481",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerDescent:481"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.powerLayer_restrict_kernel_smul_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ec93a07d2bf8c11bc2026ccfc67eb2b157b3c73585004a929a327a34864b680e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction:3278",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction:3278"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.powerLayer_restrict_smul_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f36574cfc2206e2595f581b66339c7343e9437c79e0709b06e8b9a2b8ac897ec",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction:1329",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction:1329"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.powerLayer_smul_id_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "55ac715024749a3acd6f308fe553be9cedda89b8150fda85cff7a45f7474a821",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator:3352",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator:3352"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.powerMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4f805df10914b5bc6d0871454b6319a8bed040f418fd82a728bf0539c9561dc8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:2363",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:2363"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.powerMap_mono",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c34a270ff5b62bf2046886286844805b8e97232af899cbe7950a7b8cbe9388bc",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:2527",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:2527"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.powerModule_eventually_isZero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a78f3b3f1d0ba07dc6316f1afe4d7018a351963a19954dd1f814e0072bfcc5b4",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:4959",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:4959"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.powerModule_ext_zero_of_layers",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.IdealPowerCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "634eb1f5882c7bf9bc7446c989ef13147917621a6f1b5b5120ca6f4a649eb501",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.IdealPowerCohomology:2115",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.IdealPowerCohomology:2115"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.powerModule_twist_ext_zero_of_layers",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.IdealPowerCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a7b2270c3522886fb39df4ec7450341975b67c6d781de7fb508ce20be0f6ccbf",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.IdealPowerCohomology:760",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.IdealPowerCohomology:760"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.powerSequence",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d0fe64f25ebc6ae3a616f429bbee6bc4db7a8cfc9f3bef94c4b705b8a7d7ff6e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:2721",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:2721"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.powerSequence_shortExact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2490ddfbb56f108bc817a9bbe0e3a2d1c26534f52a7fb2e4d2c4f962bd537580",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:2889",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:2889"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.regular_map_flat",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7a881a5fba77d1b357a458280b0b06850bb1012f2bf9f717d921d960327f059e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:7721",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:7721"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.restrictedInclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d85cb2e9067e196b5128a74e1550a2aee3d5bb818781aaaa7d599d2f1c947cae",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:4698",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:4698"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.restrictedInclusion_app",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ea2c5a1ce0d49c46d1510a26c2bc75a93c6fe1a9e88f99024fd8f3f394f2cdd0",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:5469",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:5469"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.restrictedInclusion_mono",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "18f7ccfd6309d4bb02b15595d3498db8faf208d24b44fe6a5a5d676577cf519e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:4941",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:4941"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.restrictedInclusion_structureMap_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "85c6f5f99187dfb8f1ebb050fd052d61541fca63a3b4c522acabd149b7b986b6",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction:335",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction:335"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.restrictedToClosed",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8ada359ae42bbde1eb0d5a8d3fd2ce264ed1e4b7aa8b873c9588878a5dec70f7",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction:776",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction:776"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.restrictedToClosed_inclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "37d2f479b5a7d1b785d416b94349cad79c08b0143dbc23dbbdbe30a9d652c77b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction:1058",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction:1058"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.restrictedToClosed_inclusion_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7daea03a1404da374f35d18dbe410096b48afc6c7e9e2699387300d6af7f9ee0",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction:1058",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction:1058"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.restrictedToClosed_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dbab76eb1983ba5909a31ddf0ad31053e3725d18c8762930abced7ae7b2eb476",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction:1299",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction:1299"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.restricted_image",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2bc6ecd9bb7013cb41de9faf5bf30e1176cc909eab525b945cd51b48755e5d79",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:5751",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:5751"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.restriction_mem_ideal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "68c1201aa00bea08559f778a7112a2e3448983068b190133f4772be3973b94a7",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator:794",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator:794"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.restriction_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cb5faf6b510a698fed573b8b614feb2cff86d823aef91d0ac6460f4951c75927",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:8173",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:8173"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.sectionFamily",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "55abb19102d8efaa7c910c9a6a11d80daa31d2b6dfc84f6d1ff6e47799e1fff8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:1586",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:1586"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.sectionsKernelIso",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dad03163dca198d3bc42c64a2abb199f230c019bfce875e967deda3ef0e18b02",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:1015",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:1015"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.sectionsKernelIso_inclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dfd52d64352079e3e4ff1301bb0fe0cf1ed480d827a77f1fc014e53d85bdc1fe",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:1389",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:1389"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.smul_closedInclusion_structureMap_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e17661ddeca917d82e22c2db9875bfc5e98fbb08a6861e9f0b4d669eb654e9e2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator:1334",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator:1334"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.structureMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "697b9f61477cc7b7c320e145b2b593e220a955b6429fca41cab26db3d1ba819c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:517",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:517"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.structureMap_epi",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fb25f3df985bd6c819fb3f1e7c94779fc14038d190546e4f9bc953152e27042a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:8672",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:8672"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.unit",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "303e3971907b7aa2b876564821211d130662483998f81740524c27d8c6a363ea",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:438",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:438"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealPullback.comap_ideal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c18da3ad866866a5955544536bc728e29de76c7974031b51a611efc7d14ad3e4",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:11216",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:11216"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealPullback.comap_isoSpec_inv",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a8b9c2f978db248ee48167dae0447be2f6b70e9f497d56b8dd8d363dcc11e123",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing:1133",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing:1133"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealPullback.comap_pow",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.IdealSheafPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a2ebc79a69471f2d2cc51ae48edb7690d393dec3fae80c650521853dc100d06f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.IdealSheafPowers:227",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.IdealSheafPowers:227"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealPullback.comap_top",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1c07e5a04b5c3f9c8efcf0cfc9c37705d585322c0698e84f323ead7a74ce8466",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:9079",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:9079"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealPullback.comap_\u03b9_top",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f489b82b8fe1fe9dbbeac3c78e78b28e7a981ca0276a044ec43c4827b1bd62e1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:10754",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:10754"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealPullback.map_top",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b654d4dcb63b3ffece1bf334d1fc987636a71f235d681476e1ac4a311fd75d6d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:8833",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:8833"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealPullback.specIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7cd970f36be9c2a49f64aa0cadbe30ff43bc114fb269972c889968ea1ff40408",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:9933",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:9933"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealPullback.specIdeal_comap",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c1cfd0eb429581e9f5660088e5382f75605034f1f3cacf276952681cc65fc729",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:10289",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:10289"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealPullback.specIdeal_comap_toSpec",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a06e1de7c1dde3777ef66d791236567fa4a0f23605bd48b38ac879860f07bf2e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing:669",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing:669"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealPullback.specIdeal_coordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AffineBlowupUniversal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "90fc65db3218508075df359edf6fd6f74899c9a45a0c97994f8c3e2e8b7fcaf9",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AffineBlowupUniversal:379",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AffineBlowupUniversal:379"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealPullback.specIdeal_pow",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.IdealSheafPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "24af392c7eb14a39d541a16c9596be84fb5c8e7158d2ff4eceec76f803d32dc7",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.IdealSheafPowers:1110",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.IdealSheafPowers:1110"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealPullback.specIdeal_top",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "183a58f0c517f7e0c296541a18ab7608310b28de1fca1777c74d8dd11ebc1df6",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:10100",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:10100"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InjectiveRange.injective_of_retract",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6860f9407634fdcc821e72e2c5a054a63ef688b6ec46ab5b223d23edf09581f9",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:5043",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:5043"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_039.jsonl"
