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
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.rec",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "rec",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "55c3c981d36ac89f91a97b3b7335ba956e9a21971d89dde4cf1545837d253ad9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:396",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:396"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.recOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0631d668a773d6a928d5fc0970c94a553365f4e7978ec6feb289435d37391217",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:396",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:396"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4d40b29596fafca965564d7e7e0e5cb32fa9d576ca8cb652fa0c200c522fb66b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:1046",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:1046"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.restrict_sections_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.IntegralLineSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c2cfba5acfecd95624d62e52d4a4721a4969dd25afb1b2c93954d833de5d3814",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.IntegralLineSections:8299",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.IntegralLineSections:8299"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.restricted_coefficient_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.IntegralLineSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "41a06c36bfa1b039c7128c3359b37c5b154f4f55a432735ab413e20876c2446d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.IntegralLineSections:8894",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.IntegralLineSections:8894"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.restriction_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.IntegralLineSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5f73662dfaeb7e10f8eb6b0336be7abfdea696f02b5e3c5d79b1546b19c8591b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.IntegralLineSections:953",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.IntegralLineSections:953"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.sectionOpen_power",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerOpens",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "74e0a2fb213a8de9fbbbd8f12ba44e7cf538c0cc4f3b16fa048a46be366ff006",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerOpens:2252",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerOpens:2252"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.section_basicOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleFromCover",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0e29727d4d8eecf647e1396ae75b5c09377b1d8b27ab54f42833018a279ddde6",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleFromCover:396",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleFromCover:396"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.section_restriction_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.IntegralLineSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "74f229fffbd0d9a5465f6e3571525366d0025c59c80079559565a280d9d90db5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.IntegralLineSections:2597",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.IntegralLineSections:2597"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.sheaf",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6fb21670f6e87a959a4274eb924917deadff1de2c8ab73ef9d15efa010e3c47c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:396",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:396"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.tensor",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleProduct",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bf424bf1560e288ba46877fa48c8c56fd9cc1e6c19eb07ff5b965c49b9c7c2d3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleProduct:982",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleProduct:982"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.OpenSections",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aa6b78c19ccaa2fc855f86ca8f77eaeb6413c791aee1cf410b0a2ac41b491dbc",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:1890",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:1890"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.PresentsPullbackIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c2e5f842868a7ce2289ae36b04d82167001177156bbfde479ad89f4414928075",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:704",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:704"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.affineIdeal_isNilpotent_of_fullSupport",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FullSupportNilpotence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d51c1da2212b7c5ba803ef39865a0464b0d986b3aa8e48894544b8639175f4c5",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FullSupportNilpotence:619",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FullSupportNilpotence:619"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.affineMapCoefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealTensorPowers",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a6942a978f69eacf58a4d795eb5b2dd3346f1d42a76b481dd5dc3797ab92c389",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealTensorPowers:1228",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealTensorPowers:1228"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.affineMapCoefficient_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealTensorPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5a60e1b4f9c890141ff91122d1fc26850988085dbaa99e5834b3ac6189eee7bf",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealTensorPowers:1516",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealTensorPowers:1516"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.affineSpecSections",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2ed05ad4ee38727ca287cfba5b1e3e682facd0dd6a6f9311809f430725ed5cc1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:5292",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:5292"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.affineToSpecModule",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aa345050b0ed4335994e452e60fa2439f9d6cb30c97e6ae582ea5a6d2b34a340",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:4652",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:4652"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.affineToSpecModule_quasicoherent",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d5b8630fdd7c2ed4aa4e75e8bb85a6f9b6b8f182da686707f32e45f7d5f68cb2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:4762",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:4762"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.affine_closed_pushforward_ext_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedSupportedSerre",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c9c55dbc6811e47d00d7faa4dc0c12649fbc7f8b17eb2694ba978e7e44c4cd7a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedSupportedSerre:888",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedSupportedSerre:888"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.affine_coordinate_generators",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3a3879f3aadcbba912891a27247f2097014a00d0f67ad7d94f18c2ba9cb6b7b6",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:9870",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:9870"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.affine_eulerCharacteristic",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5999201f28c2349177eb172a8369f37e162a327136eeefd827f05ce1574dd1fd",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler:6019",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler:6019"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.affine_function_denom",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PowerSectionExtension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0467eee3e5bb20bb93c0424f9231ef0211a496479057ab630dc628674ff576f0",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PowerSectionExtension:786",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PowerSectionExtension:786"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.affine_openRestriction_localize",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dec6cf7fc96e954bb215a3448c9c32f2721ab90f10487b1e6823b5bf5fc8e2e2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:7046",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:7046"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.affine_sections_localize",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4fc1155312e1b86bad2a839eafca7e4b4927911ab306e0854ff1ea322baa19aa",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:4950",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:4950"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.ampleInverseTwistCancel",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleGeneratedTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "47aad4f75ecf7286142acbb339ac84a212f6f19522ccf2cdc236262605272175",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleGeneratedTensor:2464",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleGeneratedTensor:2464"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.appTop_reflects_isUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AffineThickeningCriterion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "34a69cafeed53a0bafc657a13eaf3c4dd4bb3904bbb2d2d9fecf4073496717fc",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AffineThickeningCriterion:456",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AffineThickeningCriterion:456"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.baseScalars",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6c6c928bcb9de31b1578ac69383426d73221e3cc3ae8389d7be40697c2952a5f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler:3551",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler:3551"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.centreComplement",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4c118b8b0c165339180f9577da11a95452732f4d3fa1778bee3d025d4df58f81",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:3485",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:3485"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.chartModuleEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3a0c74b6874929c06e78cb77dd2e41a19d01bcacc79df793b308a937cfb58320",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts:7170",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts:7170"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.chartModuleMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "81ea66fdb05c900fd807cbc4fafe1e1495350300ea03dba33d947e9cfb9397c6",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts:7788",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts:7788"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.chartModuleMap_localize",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f326236fa7c73b415cd0fd52f149705c013bdb5891d878bfb685344642bcf5b9",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts:8244",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts:8244"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.closedImmersion_of_source_charts",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b09fbcff7ee9eeb1ac63d094349222b0c1d31f4410e6cd2fff6a3ac1f5f12b00",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:3553",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:3553"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.closedLineQuotientIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedUnitKernel",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9ee9c43db50b26a7e42c737e7da4956fda64a6470e40fa86f48f530e0b970208",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedUnitKernel:454",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedUnitKernel:454"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.closedLineQuotientIso_map",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedUnitKernel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b096d2f98a8432a9991b235b62d516fe4ea078b1877e56cf1e5a468bb35657c4",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedUnitKernel:821",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedUnitKernel:821"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.closedLineUnitKernelIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedUnitKernel",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fae286b1dea40d54333ebffcd91cfb1aa298611a5d6b4b0e87d59ccac24131b0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedUnitKernel:2097",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedUnitKernel:2097"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.closed_appTop_surjective_of_ext_one_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedThickeningSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "32129766fd4efc5209d806cd41592e5a8d430161bb820b7c3fad08c236728568",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedThickeningSections:1177",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedThickeningSections:1177"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.closed_line_unit_epi",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedSectionLifting",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e0e1d8aa52703163dcf8cf9630ef65fb77cd66ff058bbf300d53c1969f1c2144",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedSectionLifting:420",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedSectionLifting:420"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.coefficient_pullback",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionPullback",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2d85da946aa2ebbf9e7cf6d36997b067fb34962ab4e243202d4ff99cc91f7f8c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionPullback:1642",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionPullback:1642"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.coefficient_ratio",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleProjectiveSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "37cc06a2ef932484578c5dd811171670f07dcebabdbecf8b2c8a3858f20bafdb",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleProjectiveSections:1503",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleProjectiveSections:1503"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.cohomology",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e31aef1840df1ca029c0e170a417bf587575e913c23d3d02bbceb2518cd1c3db",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler:3866",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler:3866"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.cohomologyDimension",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "264c65e1b42944edbd249b08330b5e9d9baabc3c5602d22582dd10a57fbf1d52",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler:3984",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler:3984"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.cohomologyDimension_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6b565efb450701330d4934db6bf0c1b46b8d5e7625d7113af75bb8a73d9b69fd",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler:5594",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler:5594"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.cohomologyIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CohomologyIso",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "977429a3cc508294b5018c276a9b007db7c5eeadbdba9f4f1ae0a92df64ebad2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CohomologyIso:230",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CohomologyIso:230"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.cohomologyZeroSections",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c0721bb2f2cff4f7089be7a4974d973f20818eb2b44e971299ca559afee6b495",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler:4953",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler:4953"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.common_affine_frames",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleProduct",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d66652e15abcea5042074b78534cbe04cf71457e232c1ae7e165fbf5e05fbe63",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleProduct:346",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleProduct:346"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.complement_nonempty",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6aea318f18e7c7df8794f5f9ccef81cda6f6717dcd2a5b51f917467f21db3cb6",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:3858",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:3858"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.complexExtModule",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "622435fc542d955800a7132275fbb81af9b69a9b22a93be8574a315b16a30865",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact:7313",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact:7313"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.complexExtModule_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f2659658c3bf73b081d6a517a54085db7a4a55cf2e294a75b022165a97e5d17a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact:7468",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact:7468"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.coordinatePowerFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerFrames",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "54dd71016be615e6db8c0a70eab4639a123bfe906dedcb7dc8cfefd94dfbc9c6",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerFrames:2073",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerFrames:2073"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.coordinatePowerFrame_coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "48ba7f6bd0a8c86ca2ecc8497ace30de7ae034ec4eb273606811a6c85e8649e1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerFrames:2353",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerFrames:2353"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.coordinatePowerFrame_frameChange",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e86c538a778c16a261c61fa1ffba38db2c2f291b9643f3e6ba4209411259ae97",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerFrames:4439",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerFrames:4439"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.coordinatePowerFrame_normalized",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "686f32a47ad4c475a9223bd7ee38978331979a9d89292cd4f1f12aebf12926bc",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerFrames:2908",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerFrames:2908"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.disjointSupportCoverEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteSupportLocalIso",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ca1d1e77fb4d06ff2fdc78e560ed8b227191d33e43cbfc30bc13ac6d881facfc",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteSupportLocalIso:867",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteSupportLocalIso:867"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.endPower",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameTensorPowers",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "17a8bbf03f9240cb12afa3d6e1131e17398200b7789ed5e173701432a5560aa7",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameTensorPowers:2205",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameTensorPowers:2205"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.endValue_conjugation",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FramedPullback",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9f62a1b1f709c021738a670f09a15733206dfa2a0eab8c67351940db9fa29204",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FramedPullback:288",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FramedPullback:288"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.endValue_endPower",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameTensorPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "02b33621011673a915ba357706817d1820b99e02bb21ac52d3001979e456378c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameTensorPowers:2365",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameTensorPowers:2365"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.eulerCharacteristic",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ffbb95321a49183b97908386bf36c557de63581ddd5ef2d3cc138bee708fb0e1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler:4222",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler:4222"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.eulerCharacteristic_add",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bb21a30c9ae1fc222e79f6afe5fa9cda9afe9f1b7fe23e0f53dd0888e0c5eb87",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact:8221",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact:8221"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.eulerCharacteristic_eq_extEuler",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "daf06daf8a572877e4a8ecdecb3e2b11f718da7d87b45c0082a6f7dbe90fb76c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact:7809",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.EulerExact:7809"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.eulerCharacteristic_iso",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CohomologyIso",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5f29b1093c0831ffe0ba4e17b7a8c1c918efe9a0dd4da45e37e0e17dedee365f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CohomologyIso:1434",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CohomologyIso:1434"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.eventual_twist_ext_zero_of_closed_pushforward",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedSupportedSerre",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0d947e24dbc9ca5f21ed81547900073ac123a711572dbaaf2a2b0b4336e8fe20",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedSupportedSerre:1442",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedSupportedSerre:1442"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.exists_frame_natIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FramedPullback",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0e164065c6ef3c51b1221afad47efc43f8bd42c689e66a3d7f2eb664faa39592",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FramedPullback:730",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FramedPullback:730"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.exists_pos_pow_eq_bot_of_fullSupport",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FullSupportNilpotence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "43c82bad71e2bb0d710e7545233dcee304f7f5daf8d39684e32342940577272c",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FullSupportNilpotence:990",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FullSupportNilpotence:990"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.exists_restricted_pullback_frame",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FramedPullback",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8154f1256e81529400d08575854c2e49ad23de7a2ccaf48c11aa7976aed694b4",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FramedPullback:2299",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FramedPullback:2299"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.exists_restricted_pullback_frame_all",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectivePullbackFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "32ffe8ed644a467a501a3e494c009eb2c9760e67b3326fca4a63115bc72d6320",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectivePullbackFrames:3776",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectivePullbackFrames:3776"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.exists_restricted_pullback_frame_all_of_factor",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectivePullbackFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "12da1d10b0119c085a686c6e96b93e5b0747b80ec7d6613c66117a64799ffccb",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectivePullbackFrames:938",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectivePullbackFrames:938"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.extSourceIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "55445b771da136416da639ef92610ca590a18fdaa15755f9905713ac42d7536f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech:6650",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech:6650"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.ext_zero_of_moduleIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedSupportedSerre",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2b753f4346bbd1b7f5b575b2bb1f8cefb363c105137c40748958441f72534b1e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedSupportedSerre:497",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedSupportedSerre:497"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.finiteSupportLocallyIsoGlobal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteSupportLocalIso",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2274ffa0de9f968c3b999690b2fe5e01c4c364d3efc36b9a99d3b40b768d68ad",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteSupportLocalIso:3359",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteSupportLocalIso:3359"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.finiteType_coordinates",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "45262f1b05c770ce16d161cc9c47599631c97f1b84ecdb3fc7cf5f12cb164901",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:9196",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:9196"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.finite_pencil_H0_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "02ef8c322fb2f761d4ae827fca25efa82e0f9c0fa4732dd2ec750b4a7f6a9c78",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomology:7928",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomology:7928"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.finite_pencil_H1_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f2110c0434c6371a932bb4472840a0caa7d5ce1a4ab3376356a40099d60c2ba2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomology:12792",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomology:12792"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.finite_subscheme_of_curve",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c9b8d3b53ced638549f38a2234981579c55b19dcb81683120db94b9fbc8e47b2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros:5965",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros:5965"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.framed_local_division",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionDivision",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8153a3eea95ca1e17a0fba91ac95cb56713d498dd479841201acfe743cc3cb1d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionDivision:3444",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionDivision:3444"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.framed_section_range",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalPowerSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "20f1b62834addc40a620db8a28f7fb121c890f2172f7b220d032896a0b0b17a1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalPowerSections:2434",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalPowerSections:2434"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.freeOpenLinearEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "06907634da88aacaae93c8b59ea17abdd2e36493a25c785131d97d8b72a86c22",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:2680",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:2680"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.freeOpenLinearEquiv_naturality",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "52267a45d4e6a7c6a1bd602f5f62678847762c320eb8fbf0c522cd5dce60cb94",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:3513",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:3513"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.fullSupport_eventual_ideal_twist_ext_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.NilpotentIdealVanishing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d941a1192a7c71bc01a5486aad2fffc1bac4aa1b0b34146d9e71d578ca858dea",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.NilpotentIdealVanishing:2041",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.NilpotentIdealVanishing:2041"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.fullSupport_eventual_powerSection_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NilpotentAmpleDescent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "177617801c40f45f3c7b30a537e59062d341aba6022a66ba30bbb0494352a943",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NilpotentAmpleDescent:1386",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NilpotentAmpleDescent:1386"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.fullSupport_ideal_ext_zero_of_isAffine",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.NilpotentIdealVanishing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c1e58445eb7bae49fa0d2c01fa63a10ec28ffe077ebfb77eba98d94e1e883018",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.NilpotentIdealVanishing:571",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.NilpotentIdealVanishing:571"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.globalHomLinearEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f45f181ba0f710b131c7bd989866d99361b70bfe6e06a91f1b80721f72390822",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler:4518",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveEuler:4518"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.globalPowerFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameTensorPowers",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "82f706f361a2aa8547934f3b928a9a8ef73a63b9346f5d1c4761f139dfcd7efd",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameTensorPowers:5987",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameTensorPowers:5987"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.globalSections_surjective_of_ext_one_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedThickeningSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0bd44fb09a4ed293606f308b51b9a468f75bcdc15f15caa05f1c611f56e21022",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedThickeningSections:615",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedThickeningSections:615"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.global_division_of_local_lifts",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionDivision",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1e095187c1ef18118d943fb23cb53d7cff7d2a62204d524834241d5652d2df8c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionDivision:2450",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionDivision:2450"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.idealLineBundle",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aa24612e5cf1c697dc868b825bfc731813ef2b6ede0168305932e7e0ec6927a3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:3283",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:3283"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.idealPowerFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealTensorPowers",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8c8153bca7a74bb728a39ccc1d30744b924eb98fb1ab54a707805ae3c58adb6e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealTensorPowers:943",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealTensorPowers:943"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.idealPowerInclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealTensorPowers",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d90016b3c17fc1f969390c90f1a39b615fd2feb98375f783bf3eaf06333a1908",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealTensorPowers:340",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealTensorPowers:340"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.idealPowerInclusion_ideal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealTensorPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "79f0512416a5b17be0a47c74d62cbec26969e66cf0523bb286dbdd2243899d41",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealTensorPowers:2328",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealTensorPowers:2328"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.idealPowerInclusion_mono",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealTensorPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "af924ba159c8f6d53730b3e413d14554053afe7af7b4dd880ae26da12075dd9c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealTensorPowers:544",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealTensorPowers:544"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.idealPowerSectionsEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalPowerSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f0b5e5256b4b1dcc82b88ef0edfe2a03c4915127a50538abde4dd828c928fdd6",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalPowerSections:4644",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalPowerSections:4644"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.idealPower_restricted_range",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalPowerSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "10baaf9dfada7221321e4fc0d9ba7eb5d5fa30eba84b948f66b76408187f1c8c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalPowerSections:3223",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalPowerSections:3223"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.idealSheaf_le_nilradical_of_fullSupport",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FullSupportNilpotence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4a01873059b5632970a7a39de66c4fa98b98c6dc085a09d20b8a70453fc64b51",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FullSupportNilpotence:306",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FullSupportNilpotence:306"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.instAddCommGroupCarrierOpenSections",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7f24d980ffdad3b1a7eca3b4d12c0081a607d8bfd70cac202a6bd81c5f6693a2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:1949",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:1949"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.instHasExtModules_oAI",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedThickeningSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ac8bf03aaada6fae6fb8f3e3699126e9b7e5f15af6ca16d17bd4894c5d6267c7",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedThickeningSections:536",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedThickeningSections:536"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.instHasExtModules_oAI_1",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedPowerSectionLifting",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "53ff2d645a9ef5a84a2b7bb901f55b0dd933ca164cb848206c22e44aa1633920",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedPowerSectionLifting:454",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedPowerSectionLifting:454"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.instHasExtSheafOfModulesOpensCarrierCarrierCommRingCatRingCatSheaf_oAI",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "254fd91684ae0d70a80c88c300901f80c129dbb27b0d60de13298250544ab485",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech:2232",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech:2232"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.instIsOpenImmersionComplementLift",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8e64cf4fd4d56b058bcdbaa6b05caae49b9506f58a3cfc1ff6be33b8f859405f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:4665",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:4665"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.instLinearCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopSheafOfModulesRingCatSheaf_oAI",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b12e7b7d78dbb0bf15fa7c2f46a5b268940f5bce5d2376de89e251a77c2cedc8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech:2148",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech:2148"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopCarrierOpenSections",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9d1c3d1e6a352d65b6d448fe4dd8303ea9606aa40af7cb9aca164a0c79479903",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:2068",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:2068"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomSheafOfModulesRingCatSheafFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3a3d9a75128b38ded5921886e40cda34e7a1f5ff67056848373947cf741b9687",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:2550",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:2550"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.integral_scheme_image",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImageBase",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8ceb6931046bf94d6e2583f42b0549d4e51538db4e6a07cb4c3f930f400b75d1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImageBase:363",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImageBase:363"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.invertible_top",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupComplement",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1391d7bca5d886e9dd37aa8f10f17ac1306667eb24a8232bd008282a15113a9f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupComplement:278",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupComplement:278"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.isAffineOpen_basicOpen_of_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AffineThickeningCriterion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7d0efa7c0e5f79ad41e6cfe006d140e1397c012ff629acc009f5d0e7589ac509",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AffineThickeningCriterion:842",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AffineThickeningCriterion:842"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.isAffineOpen_of_fullSupport_preimage",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NilpotentAmpleDescent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ab34c40bc350833f669a0cfa56392ec48a08eafe186febffd1ab96ee35c46b44",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NilpotentAmpleDescent:431",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NilpotentAmpleDescent:431"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.isAffine_of_fullSupport",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.NilpotentIdealVanishing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c7f61c7d80efe97d1e19eb6a247ec4f38a9a67c071c9764fbeba8beb490024cd",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.NilpotentIdealVanishing:1780",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.NilpotentIdealVanishing:1780"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.isAffine_of_fullSupport_of_ideal_ext_one_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ClosedThickeningSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "19224591529d9bc49e64a50d8a7445538d4c34448b509a9ca68758b4b0b86f6d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ClosedThickeningSections:2196",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ClosedThickeningSections:2196"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.isAffine_of_surjective_appTop",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AffineThickeningCriterion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "08d97a41dd2bef75f79a95e72985ce8ac7885b4f9bb89b6012fbbb5a3bfe4fad",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AffineThickeningCriterion:1151",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AffineThickeningCriterion:1151"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.isBlowup_id",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupComplement",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9e353ac0a89d5ccc8c35f126312d701441ee30cdff43d14d5ccdc7eb269c084c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupComplement:598",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupComplement:598"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.isIso_restricted_section",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleProjectiveSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c704fc1a99f674917993fe78ba7a9433408350b85949acd0e7d85b85e717b396",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleProjectiveSections:474",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleProjectiveSections:474"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.isUnit_of_basicOpen_eq_top",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AffineThickeningCriterion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "51774bd9275e4ab60cdd043c37427f506bfd71ec390f381a8ce9aaac681614bf",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AffineThickeningCriterion:226",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AffineThickeningCriterion:226"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.lineBundleOfCover",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ab0448896991fa660a0d0b3dc4483a7027f3df60f41994765bbaa2bab4ef26a2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:2933",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:2933"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.linePowerAdd",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b04ecc0696f813711bd3e2aa91e1c81f4438f7cf6102b1e5f4c0763fcde56c3d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws:9085",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws:9085"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.linePowerMul",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3a1719cd2a7339f25d1b182077d8a4ad197aafa53d1247683edbe6aedd423b54",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws:9547",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws:9547"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.lineTensorAssoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c94825aaad90fabf9f955d68a16c9a23ad50053c2ff328812ca3626d45f6ca73",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws:8505",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws:8505"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.lineTensorInverseIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleInverse",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "76c3343a59e122b7bf4c9f474043befaa76e096574587c7d588306f3af9911c3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleInverse:1229",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleInverse:1229"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.lineTensorPow",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.LineAmpleOperations",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3347648072cb22affc0ac83a14a47b2253ad52cbf83db4cb11a7b8ec133f49f5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.LineAmpleOperations:415",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.LineAmpleOperations:415"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.lineTensorPresheafRestrictFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ModuleLinePowerLaws",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a68806b035f33a0de89949dd2751f8eda9881da8ca4f65b4fb55b79066e3a99c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ModuleLinePowerLaws:407",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ModuleLinePowerLaws:407"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.lineTensorPresheaf_unit_restrict_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ModuleLinePowerLaws",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a4559ade64c11b79a457ad442ffe5936e6c1800a3c996d800ac8842188c1c754",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ModuleLinePowerLaws:1141",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ModuleLinePowerLaws:1141"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.localPowerFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerOpens",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "548c2d4d32f19d466517d288892d76d403af4dd97f83b02d22ae67ddf0799af2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerOpens:736",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerOpens:736"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.local_affine_mixed_extension",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MixedSectionExtension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d5bfdfae7689720f832a0e7cc2e313e5c75ee389f234246726b07c62849cfdb2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MixedSectionExtension:401",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MixedSectionExtension:401"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.local_affine_power_extension",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PowerSectionExtension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2d63e4fd71f954ba2762a5ffdc77f053b6fbe36bdce2b36430befdf0af1660e1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PowerSectionExtension:1374",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PowerSectionExtension:1374"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.local_powerSection_coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerOpens",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8e764e5d43e805da91f982e8383369b83b682db9c06f76fee5fe4f42a66ae321",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerOpens:983",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerOpens:983"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.local_powerSection_coefficient_unit",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerOpens",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "189f6d890feebc93173ec58262915570120fd02d96cdc5ed1f61b8597fe246f0",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerOpens:1994",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionPowerOpens:1994"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.local_twist_extension",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TwistLocalExtension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d04a1494118a40f0c410f075224c870d8e95b3db421c89a912136689b4a42c6b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TwistLocalExtension:400",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TwistLocalExtension:400"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.local_twist_extension_section",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TwistLocalExtension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8ceca41937e4508e1a188c5378dcd5af0e51dfa6f798168e85a995ebe1e4ff3d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TwistLocalExtension:1657",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TwistLocalExtension:1657"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleIsoSections",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "20e857e1ad57e357800ae1461aec9feea3fd2808be45b42c78ef7de856c7a159",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:12350",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:12350"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.moduleLineTensorAssoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.ModuleLinePowerLaws",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cf6858bd716d33549bb0b1af23ff8a39c8723e6456d1cb13b903ab5f004903b7",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.ModuleLinePowerLaws:6020",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.ModuleLinePowerLaws:6020"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_037.jsonl"
