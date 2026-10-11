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
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.chart_generator_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d4a01ef9a1396344f405e50d39af592e37d3ca38de2b5c291eefb8fd5203612d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:11925"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.chart_scheme_ext",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "35d18e33ab114ff5f2e0b4168122986460bb20ac641c064429972df855f19b3c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:5573"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.component",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0e44eb048ab1f5a3ecab0f5add3af107f4cdd01951a3778e0f540caeb85ba3f6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:830"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.components",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7ce9fd26113231f0b322ffba05988df6ee6e0532a536e7ff0ecfb89abc6021ff",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:1162"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.componentsAdd",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6da215f2f04f7bc004b2388c3c671a45bc13614d552a2d45c0df0193c3756e79",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:1689"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.components_of_piece",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "90b2b425aa5de17029032df07720fd22ab53c57294ad6c47f7a6e5440907893c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:2299"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.evaluation",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4f29a3e2fba50c4381506cc32392b51368fdab1e8caeadf46ce90be39cad4dc6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:6749"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.evaluation_generator",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e0a853e0ab9fdfd39be061992ab72080d1f1602b2f75cb5c6e91fb11ac178249",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:6859"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.evaluation_piece",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b504d7589626c8d4f6e3692408e014a97bb1946d0352a2020f94423f49da6ff8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:6971"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.exceptionalIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b37b3044836892b4cd0b1b39f49fd83aeb4674991b691d6094cd36434a347795",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:3949"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4a74970e849397bdedc1646c4b75554ecfbf640d51498f96ba981b090f48a97c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:5196"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3f4a5916869eb3b92a9367dc94751e7dcc1b45f1db916880387f650fb29185b4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:5351"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.exceptionalLineBundle",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6e9e57049d95008f4d2c386566a82bac7684327c31bd573a68d15dce6a71806c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:4990"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.exceptionalLineBundle_sheaf_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptionalSheaf",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "76efb8bb20b47e53c873170fceb7844bcdc5bd4d84d32eaefc5a837ea4ccc0a7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptionalSheaf",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptionalSheaf:196"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.exceptional_chart",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e5ea9a8e8bc2c2ca853ea32191fbf517b0b172d6aedc07a0ec3ad30116dab7f0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:4208"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.exceptional_invertible",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8acec447a8d2d5bf5ee267045754c08d4d9d8451c1c7ef213fc32557842c749f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:5969"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.exceptional_presents",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7e05ff957acd6a790fe7a51fba51941911d8c19127d8cb7230cd5d77dac0672f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:5520"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.ext_of_unit_generator",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "37eb9751a058b01d886b59368e04e445053eb9effe588d595f68daaf1c3bd98c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:6081"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.ext_of_unit_ideal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "baac9454e39e06d4a51fc80fe26f96ca114dfcc6acf4ba7e179892e2c758721f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:9257"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.ext_on_generator_open",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f8935376f5e49869fd2cf4e4a6f40d88498a3cc4cf8f13edfdf015bf4945adff",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:8653"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.generator",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5f45560abfcfaf29c673940dacbc562cf85014eeed72a266aee9bf1ccbbdbceb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:6444"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.generator_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4ce8c89818adb3b275229ed20f0d67e298d227529de22f714cb51cb00d63a442",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:6662"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.generator_val",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "077246a13396f16fd8b1ed2689e41f879ecff3aabdb0649551011faedad1799d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:6567"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.generators_adjoin",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3262f39e39137553f3932728fa991a47a82abb8e2aeb95ad22196aeaeeb45b7c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:344"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.generators_adjoin_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8c7aa8305ffb0bddd245b0d85c4f35c9f36cc9dde6013ee998363c9fcd649c33",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:980"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.gradedMonoid",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4a83d2580e5f7c636ae9d770397ac85f23f1cc97badf0cb30ecdbdf584d2995a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:3952"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.grading",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "71b1ae2a1d5b8268435dca2b0f40830f1813ee6909fbdaa783cafb0351b1afe1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:4277"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.iSup_generator_basicOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9ed093ca9bffeead786807ea89b83692b5039e098cdfa1bf1fcc2ebfa8497d70",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:1549"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.instFiniteTypeSubtypePolynomialMemSubalgebraReesAlgebraSubmodulePieceOfNatNatOfIsNoetherianRing",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6d861c182d3c82c7d71504a1a549a7497ffb194a367a02eb9bc680a14f94422e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:5782"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.instIsScalarTowerSubtypePolynomialMemSubalgebraReesAlgebraSubmodulePieceOfNatNat",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "df5c9af6af024773e7f899c46b189fcfb9e9b1e3dbe57565e1cf2306fde10560",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:5620"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.invertible_unique",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AffineBlowupUniversal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "346dcb47fee744866bcd114088c691ea0113d682e1b28ca25bcafa52e24caa18",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AffineBlowupUniversal",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AffineBlowupUniversal:934"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.local_lift",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AffineBlowupUniversal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6fbd648a894a81516f90d8a7a6386f53ec3d16200556a0e495b987d357535aeb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AffineBlowupUniversal",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AffineBlowupUniversal:1615"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.map_ideal_principal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bc3b79f511a605ef80ce32894b072aa408aba93396ad1092846e4d3b3447ad82",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:10894"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.mem_piece",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4153900075c8fe406c1e98cb4f85f6c49144fe5bcbeba12624bbe30b6eff223c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:698"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.piece",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "08d53696c6c5877142aae051f3bb724f874818c1882ac2f7a28b8eb492e35221",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:272"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.piece_coeff_ne",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "57122a7b9909bb398df6be7514f7b4f12affb4963366fd5d05b27868e236d667",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:2105"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a23ff5fdef52c2bf7cbf385b4e767a63caa1d4788ccd85395362a776a17aefe2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:5622"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.principalLocalization_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b6665f8d9ba35e26c4edc5d092a2d4bcfac3a916492f90290e0d2a5559852445",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:3830"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.principalMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0974f4f7b2b026f5891aca6172f6fc4445d113824421936f50bbd77d72cca58d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:4045"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.principalMap_base",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "49905e889e5ed5f4ff375feb63e6ea0b0195002c1d2a6547277dfa0d9fc8f606",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:5310"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.principalMap_generator",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c798346e6d3480f2d4b68f93cf61f4808edfde109fdad6e0af353514dec92269",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:5524"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.principalMap_irrelevant",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "46da5d3e4223c78025a852848549ae66a7f67956e3f17c71195408dd087f779b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:5761"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.principalMap_spec",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c9959a1291a90e01a8d3d4f207f47302bceaacf9dd27f3a1f072b7a49b7666ce",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:5080"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.principalScheme",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d99f287d707e9aef45f05a950321d56bcf3bf4a3a5142a7e2e19905a90269623",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:6442"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.principalScheme_preimage",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "758ea981465e1a911e117aa4fbf68a1d8e89e4ac3fead04ef516155214b030a4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:7891"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.principalScheme_projection",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bd456ab5c8b1295f45bc6fa9c16553f8f111aac606aaa7be47465090c31daeab",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:6600"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.principalScheme_projection_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "296a8b8e913d22300ed7418c70f091b8a53fa6f0be1652a1b81da985b36ecf8a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:6600"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.principalToLocalization",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a7a5fa4b7585a38681e97cd179805315a9c008d7b27cd522699fd5b52ccc0a12",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:1839"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.principalToLocalization_base",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a97071a11e4e219f17c46cd73b6712babe4facc146ffa82f7cbde46418d08f16",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:2064"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.principalToLocalization_generator",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bca39e6b2c1ff240948a7b7fe252065231356954942ed22f9cf2a7b1e0b8327f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:2270"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.principalToLocalization_range",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ebb0c4a8f8463c31f4a574f7ca3d3e832bbb0a0906590cd5e30aea5ac41e8f50",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPrincipalLift:2984"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.principal_basicOpen_unit_ideal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0c8c446d145053e348368e6f3efc7812c7ca732ff395ac207269773044222a7e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:9821"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.principal_unique",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "adfae9861682d5a4f28b6ff96adbac42e22379c47b6847c769f71537f63e7fba",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:10372"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.projection",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a25faf5d1ed6c3a45d178505fe920eccd3dc0acaabac5f8d972bd147443f76c5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:5496"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.projection_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fad80e54c52071626a439ea35034577b8ea3348c9efa4a7338f0453a7adf3a20",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:3563"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.projection_preimage",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "896499c9c2044ae36df83a3b070ee4b4e2d1b1697d9dc2ec576321850c837932",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:3864"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.projection_preimage_le_chart",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a4bd8871b957fd84ce5e9b51a62cc0e2920f165a3cc5ea60673dffacec71817e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:4382"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.projection_proper",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9e149cc93710b5ac701223e9bf298ea5dc2aa529a13811d491c0487405c42c77",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:5949"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.projection_separated",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a6d8e8e2935527400e6295d4932944684e05f71da9714d6fac9edaef32225be4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:3296"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.ratio",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a4997a3394758124b013af02b80a43e267e3092c29dd5246da99c374be3746bb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:10133"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.recompose_components",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "10d25cef803405bc9547d08ba92dae49e761c4cd255cfb71fd00b77b5fda9f8d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:2751"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.relative_affine_section_cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesRelativeSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d45a390d296e14c4c2ed809546fe3bfe8e083500cceb72a80f175d218556aa7a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesRelativeSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesRelativeSections:7244"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.relative_generator_section",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesRelativeSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ba3aba182a27df01684da27ed1ac9dd96ad1fbe6f50a9cbf25669bbb18adda00",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesRelativeSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesRelativeSections:2504"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.relative_generator_section_open",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesRelativeSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ea53e2a53ec4222c334acb05cfdc2abbfb7eaa9c1bea9e23d7d7bb24f8fac814",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesRelativeSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesRelativeSections:3959"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.zeroEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e6e9cbc89c28a6190575d9932092272096a526ba1623ce85cd84d9890f6f175f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:4819"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.zeroIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d2b6ebec0720888292e90e6618a83d9b891c423a18b8f6dfd602b915a8420994",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:5394"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.RestrictionCohomology.freeOpenEquiv_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0cbd0d6d18ba33e774ca00fef4e91ef9087fbaf376fa5185eb09430acf35cebf",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:47059"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.RestrictionCohomology.hasExtScheme",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "673339367c3582b1e4c79b15a30bf1bcef9fabd466c44e658606a5ddab0cf325",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:46965"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.RestrictionCohomology.restrictionGenerator",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bd8758a386c74bbd8a2c7d7a0ce6b1cc8d95b3c14e84c250724e7341614dbad6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:48886"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.RestrictionCohomology.restrictionGenerator_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "63fa0350b7a5dc4d2179636e24eef59ae66584d44c07e07855c4bfb5035c3b38",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:49049"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.RestrictionCohomology.restrictionHomEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b05ecaf5468a84f451feea7cc9c001574091aa03ac1c4820bb64b76c591531af",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:47449"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.RestrictionCohomology.restrictionHomEquiv_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a74099c87d653e29070d87a8bd01d662f161ea6934b09f02edb9608726e4f6ff",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:47780"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.RestrictionCohomology.restrictionSectionsIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "90e7f19c32793b7803082ea2d510659291b87631a71229f1620bd3d8861b2953",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:47275"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.RestrictionCohomology.restriction_ext_bijective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c21606ad1d9b55e117609bd3720d7455ca61a9ef7b69c8e1043c3bae14417849",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:49366"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.RestrictionExact.restriction_additive",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "06ef4bb608fae9b10dd6770c7d5a01f7cbf70ed6dba94353c3c95ba7a792e611",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:40348"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5e8e7cee6b6d44bfeaba8d761bb5849c23bdb83fcd9c36f39bd0b714f05e83f4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:40854"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.RestrictionExact.restriction_mono",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "06011a83eacc1673418194f69453db2f64ce609aead1191a8a3a1b93ef7c4ccb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:39771"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ca852020688804db4747ef9ace9e164a9bb6bfee48e76dbd4e35824b7bcdde9f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:40660"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesHomology",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5855aebaeaf4de2c10a6c1219e0283f7bfe7345682e6ea8d92060482c4b49565",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:40467"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6dc89d9c807511f9b411e67fd2b0a5c467deb0bcaad0d088b8c5b2c4ad55a09e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:40189"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SchematicExt.basicOpen_ker_eq_bot",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cb537175018abf3da4b1907cf2b8615689bc03e99b14ed45edcea3b158b641c6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt:3852"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SchematicExt.ext_of_ker_eq_bot_of_isSeparated",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "713452cc90e4111ff231a051c0a9affe41fa9112e11dfc99868c397f194958a7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt:2722"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SectionOpens.isIso_of_locally_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "304009d759e2a2d88c0d7e335f5cbb6898255f6d1e64d81d7d65540dbf628865",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens:1672"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SectionOpens.isIso_of_stalks",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "49762c9baaa9ebdc609ea0fcb553867584535eda9c49ec9957caf5693991ebac",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens:325"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SectionOpens.isIso_restrict_isoOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bc28ecc904486a31f7525400dcc8add63a49ae0a1480dceb558556543ff70f96",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens:2318"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SectionOpens.isoOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0cba39bdaca8741dc586d9e4f258be03117c134dd68de04b4b1cacc3f89eafed",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens:1978"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SectionOpens.isoOpen_postcomp",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9772b51125070d715dd79f5e22d48d1d66db0c576b37c302839e76f254d02675",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens:2769"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SectionOpens.isoOpen_precomp",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fa423a21edc78572e5ad495f04cbfba9fcf0a701ce838216872f681164a43b25",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens:3429"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SectionOpens.isoOpen_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "20bdf0324c41c48eb69bf9dd1ba60272d727825b0ab2620f4d83f7dec8856d70",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens:4087"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SectionOpens.mem_isoOpen_iff",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ccbb6819fc27d23f37a9735e1fbb3a405396c59a67e7839baba00c6c01ff27ac",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens:2102"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SectionOpens.restrict_isIso_of_stalks",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7385aa7ce76f7b5eed69fc74cc7427055bc5cf5b05863447ab2215d5327130b8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens:1314"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SectionOpens.stalk_isIso_of_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a12b1e372674c0479f0dfaa1e6306ae76ff47198ea461cfaaf2f8907757a1e2c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens:846"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SpecMaps.coordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4301a2b8abbfea12a0961aa80cdfe710cbb7a3f17acc1498bea85aade67a9908",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt:253"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SpecMaps.coordinate_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "25137f31eb39bfdb6e5fd295cf2167789e74cad146fcf3166fbc4a930014bd5b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt:541"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SpecMaps.coordinate_comp_spec",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fe20e29d16fc046ce61971b25fec9d4177ce94be958daaf2976ce6450d1e724f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt:823"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SpecMaps.coordinate_ext",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6b487202e08daf9e32755458babb2a49f99e8db858ebe9071d9177be1a58a872",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt:353"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SpecMaps.factor",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7aeded39c6a0d04cdd6d32294678bfb84a3e421e6ff1fa4d2b6f0da10417e02b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt:979"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SpecMaps.ideal_unit_generator",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d8378c6dbfa45bda551f57df11ac42aa96a54e2c04513ca12a8d624174d08e8b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt:1971"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SpecMaps.isUnit_coordinate_of_preimage_top",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c7a49b2bbba1debfe3c29d8d365e9758910edeadace5f7f7af7a0dece7b468af",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt:1746"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SpecMaps.isUnit_of_basicOpen_eq_top",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e92702a01a567419279b6439803bdf895f54cb8b918cbbc34a28de2a932c7328",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt:1485"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SpecMaps.preimage_basicOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a731ea68c486d4d14ba3ba729b85462df909460e44b2db4b8b56505a4998356e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt:1206"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorLocalization.map_tensor_right_unit",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1f5a5cc4ebe7a9a99961ae662c7c48c72eb44a5b414b5ded684eb2595391d7ab",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws:1017"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.adj",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7b0d039cc3ee836277ae561ef200991582e8d4d8ab4ba6a04fb09d42009728f2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:620"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.assoc_inv_pure",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "679d55587d10805e37f54e0d6c5ff30bc0671cc48535dc39c11e7f3579be76ff",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection:3459"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.assoc_pure",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "481fcb7b12c26fb9d2affe614f35892e20ac657283ddf88967999bfc223a2e7e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection:427"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.framed_pure",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9e12c895dd32a0599894f425ed076f59464d5d3008721b1f8095b1d891a6a09a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen:2230"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.hom_ext",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1bad842f6d93d0fef92a536d9e00eb15956b6f6b6fab2470057dc28bc922f0c6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:2758"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.local_framed_pure",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "de3f66e7da0c34084bba764bf148abe6e17e5a0ac59f4d623e1d26c46faeab5c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen:2767"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.local_section_coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "01e79eca76f1101c419cc02b29c6ae3cebb609c47f2cd9357358985c76d5bb43",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen:3587"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.map_pure",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4da92ab649df8f36e3718002abe29438531c8343e0383777a3cf6015f7848bb2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:2339"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.mixed_value_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "84d90e5e06d9efca71e3ad456a8f3060a7611ebb0d1ac0ee4da79f8dd8769585",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection:6677"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.openSection_tensor",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8f3309c94122acb0c7e50bdc10649e7fc645496a6581135d20831e84ddf00d91",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection:5599"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.power_succ_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a010c15309b9e00c2fed23f0ad26f0935622ec134a48310a9509c1f09f6f1cc2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection:5062"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.presheaf",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "98bc8c4b3783048c4f860eb342fc13905015f8d9db7134a81ba0959e94c22a47",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:510"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.presheaf_restrict_pure",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "28c03c9e48217900becd3d19271f8b1608f9a5eed6969dfbfd92c5fc624183fb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:4201"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.pure",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9178a87ba60fc9315f8bf74024424da610870c441e03c42e835b8139843da7b6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:748"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.pure_add_left",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1df9292956a7dce32eba05e15cf4f6094b19f1fd5df8498099b3ab659a4bdac5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:960"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.pure_add_right",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3eba1798ff872ad3e5672eba53416d0081d7d1cd1e84ab5b23deeb24719b9bd4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:1209"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.pure_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0e8f8650081cec725eaed136d76930a1f90e5f11e4b87acf836f6e22d0d800d2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:1978"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.pure_smul_left",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d66274dd13e35c842c1475876f0879c8f80a97a8ae85c1fd36d4588741c48a29",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:1459"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.pure_smul_right",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4f4da444665e5f0d2cbc699423c865264a32c9da14e9630ca46fdf3608f776fe",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:1718"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.restrict_hom_ext",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "74e2e256d04ef88f464f62f5ca8cd67b08b64df02569b850ebc25c4c937284ab",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:6713"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.restrict_map",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7f10c4351494261ae2338ec9ec946efa5bdb0358b99ba09b10fe875b6b2e00e1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:7523"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.restrict_pure",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "587e32e6db376726fd683e9c4c7422ef146f5bddc1cc40370b1f5edc2b0f59fc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:4664"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.restrict_pure_inv",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9cf87121c9cefcb5b10f73d04f8e218a709b32b3c2920db6b5e59367e4b0edac",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:6171"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.right_unit_pure",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cd8b3926370225c31258869c58bc89eb80021ad3168fe2ee2424f7c4c3dace3a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:9246"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.section_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0b76ed148e94f800cb058555eb17cd0df48220b9b789faaa44517a48794c04e1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen:1189"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.section_open",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5d67150719e49d22829093c896abab98ed4df94de9295de93ce081fe1295c5eb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen:4536"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_032.jsonl"
