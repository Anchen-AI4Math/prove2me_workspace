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
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.differential_sub",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aa6132c18e01e2b74d817425af4cb9fcb2642fccbd89f45cc4ab2d087bf2256d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:4172"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.differential_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ebfbb02bd6bec4a86a114f6a7665df0417f170aa5552eb966dca144f78e238f5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:3949"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.evaluate",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a7e89ee6ba3d68b1b3969619543bf3aed54172ef05d2c55e0ed2eb41c88d84ec",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:2206"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.evaluate_differential",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cdb015cc4a99702108e50e86c300d00150d80d9cea63e608a43ad770a8fcc3cc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:2467"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.ext_succ_eq_zero_of_injective_cech",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "af6f124ef9965adb9bd7816f8d83f6c7a82d4aea5028a268aa58aba6419aed3b",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:16187",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:16187"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.faceLE",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "15f0caa204d9dcf5ee5f81559cc002e0e22b4924244408f5adadbd7f6a2dccd8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:827"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.glue_zero_cocycle",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b76d48400fd89473a867112769d7058eef9e5a707cb65d90dbf4e92fafd4da8b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:12471"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.intersection",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cc48c209d1e1fda18142f507f395581a76b0b462cc568d980f924023cf01f806",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:564"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.intersectionLE",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7aecaf43880c1d650603a41c52052bcb86af76e179dc22b9474e0c2832185fce",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:640"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.lift_cochain",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9cbd160438241d98f13161cd1be8204fb87f6cb1fc222f8913ad4975be53f898",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:5008"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.lift_kernel_cochain",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ad52066035bbd3559ed65e5d081adaa1cd2fbe0438b2509f0675e709ebc39e14",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:5462"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.map",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ab7c7694d8e26cdc25715d8c8a2a098d6bfaba483320b8c75bc3338eef3dbb0c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:3515"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.map_differential",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a5a3a769ee9a718026b78f7cf19f9cb590b0d9f3e01141c4d4645c93ad729d66",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:3644"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.map_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a8637964691f0c31018ee48dfb9fb6705caf2c75224bdc0fe3a77773beac2ce7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:4798"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.map_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "541e5aa420a76ceae4ee79c08d468433d787e3943ce43cb5e983fcc9c6728083",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:4425"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.primitives_of_shortExact",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "46c6973815381b1c6989bd736876e3c0032af525212fd021e1cc7b2da982f5bd",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:6794",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:6794"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.restrictHom_refl",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f402522c0ea862adcfbd9eb47eb5434af49e13e0621befcaef1212d1cc6bf51e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:1446"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.restrictHom_sum",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "42613a89ef15aa67127e10156c81a6ce7244460b181c37752becd88ded301d14",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:1719"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.restrictHom_zsmul",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "187d2a484a7a9a847881db8f5c2be068ccce6cbb86f54bb1a28fa788cf1122a8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:1983"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.restrict_cochain_congr",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ebd03572b593ac28063938d0493b76dcd4a1eb0b76204d8382bf5f59796f1a79",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:8262"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.sectionZero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e044a2105824620074e84ba6575fda70584e6cd9a5e94757844086d1b68ca1ea",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:10336"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.sectionZero_augmentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7c52cedd31461ab773d2652390f3cf37e12d12ac463d9d5f1c5843c7405d115d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:13632"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.sectionZero_compatible",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3c206b54656f0e860408cd9b4b099604c29de2a59b779eaa5ba86b210c630162",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:11009"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.shortExact_global_lift",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7f84e8f383439a47b007ea8f740db0ff2eb19a635b850b866fa3d57ac4380dbc",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:13923",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:13923"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechLinear.Cochain",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "46ff9be3502c7e207e0def20bf8fa06e901d0e3902db4d159d437d6bdb5114ba",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:1448"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechLinear.boundaryToCycles",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4d03c18598052deaaab429915e55d5c9aaa750212a09cd6a842da99968de721a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:4362"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechLinear.boundaryToCycles_primitive",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "13eaf223ab19c582773911e2431cce7fce71077c94f52ce1bd70fa20cbe16b0b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:7909"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechLinear.boundaryToCycles_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "39327b0c0b2f205a38d92cabd0470e241b7d792b76618c91dfc9aa19bdec6128",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:7362"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechLinear.cochainAddCommGroup",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c6f794a647afe3dbca621afa73dfb0d947729fbd0ec55059e01b11efb17a0078",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:1567"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechLinear.cochainGlobalModule",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "67ea07a8c895c89763fc9ee6c25514d2d98849b5ad9e422d640ef79fae190436",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:1769"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechLinear.cochainModule",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6b134ad9aa8835a03a7920a8b7c6cf5fac9a44e550405e7ce8a976665132e2cd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:2131"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechLinear.cycles",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d3773aafdf1af872794de0818af25436c6db19db78ba296ed1bd6988cac2da14",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:4109"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechLinear.differentialLinear",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ddf166fab6c1d0db5da3587c77e99d8aea5d67f134fcb929d95a7b8473a418da",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:2324"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechLinear.mapCycles",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2876294912bf3e93c29026d361fb50aeb827ff17c0ae23af22977236c5df9b05",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:6300"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechLinear.mapCycles_boundary",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b15d1f67e17843763d530b27dc8e03d81aa4de7e5c66fd03e2da69eb9026b22b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:7079"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechLinear.mapLinear",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "478c89c4b5cdbca267cacd20194800e5ac98bbfb112527463871352dc7dde928",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:4797"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechLinear.mapLinear_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ae69d1aa37aa6bbb3cad3f415beb0b881dff4821d16143d3c380ccb02e0c2ed4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:5592"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechLinear.mapLinear_differential",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d468ca5307a380ea5ea40bac7021abcb91c3a6826e452fbe438e62e374d7572c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:6038"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechLinear.mapLinear_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9194efba702c73b34de6d8acbcf729c0fcfb80d97125699be32230af5cf82624",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:5840"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechLinear.primitive",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5bd8935d93687c1359d30d454cd8540b952cc1347dc9dbecf27bc34b9645ad07",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:7652"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechLinear.primitive_spec",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "31203c9b5746d838b49b27c39f9bb12fd8ede142a5dda325edd6a05c7f6f361d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:8277"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechOne.hom_ext",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechOne",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5cbf5f6f32eff579bf8fd335224fb32a82f9691774fb03f252b8561435447641",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechOne",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechOne:3066"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechOne.hom_glue",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechOne",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "51d844d64d668495632a8b23eef7396d234576498f2c69a086371c829e38a34e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechOne",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechOne:396"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechOne.lift_of_ext_one_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechOne",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "60413d094e13677bc52c10f6cb893129f1005c301ae1d5c12b95f398b395b381",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechOne",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechOne:3729"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechOne.restrictHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechOne",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3d6173cbc52d750da5ea08dd36c7dd07ab4a73a59960b054556e98caddacfe43",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechOne",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechOne:1597"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechOne.restrictHom_add",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechOne",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "85024de58185a23e2cb44b0fde658df27ab72a0780cc56257bb6836f28517fcf",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechOne",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechOne:2566"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechOne.restrictHom_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechOne",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "72d70312716cf48fb8f80ec69cba3470ce53c0c8c2eb09feb84721df12bf16c3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechOne",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechOne:2319"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechOne.restrictHom_restrictHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechOne",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cf5f588a85ab793cd5415b42ec0c6ae6d8e608eb3b669ce4111eccf6c3f55a48",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechOne",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechOne:1762"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechOne.restrictHom_sub",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechOne",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7e6004308d7c1500711d75c36c6ef18bb8ad068895f5e6494b4b4700d4cf530a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechOne",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechOne:2816"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechOneConverse.instHasExtModules_oAI",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechOneConverse",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b3ed639071f795546b59809dfe10a4ee40fd222ac6ca4f58b5a35cc0f092a5de",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechOneConverse",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechOneConverse:2347"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechZero.augmentationLinear",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechZero",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "446c4faf86c26bae6986bd31f63c411b87914d1b33c1c6a0e0daf0d7d630198e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechZero",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechZero:2629"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechZero.augmentation_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechZero",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d15237ac4dcbb34b464214554ea16bff321b6ccab1ecb3284bfc6d0de232385d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechZero",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechZero:1958"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechZero.augmentation_exists",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechZero",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "74e4f435a62f7d1a20832cf7dab5bf24740d0589ea739a47bf6fd4d974161259",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechZero",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechZero:1537"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechZero.augmentation_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechZero",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6cfa3e7d6bc4ae1153e748c730437f1cba8b7545da00ebeefc709bb613138258",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechZero",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechZero:1198"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechZero.sectionZero_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechZero",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "411908a7d00c19e6eb822a4ac5bf6cb7a3420bc93f16f5dd6a8558e58700bfbb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechZero",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechZero:1009"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechZero.sectionZero_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechZero",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "233d2938c04fd5a2f8f903cb11ea08301ec963e4c3c6cb2853bd14ff76ae15b7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechZero",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechZero:501"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechZero.sectionsEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechZero",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6d3228a5f084381706f03e7242d77dd5622f8729d6180ac0b06fc4a6fb0c18c0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechZero",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechZero:3791"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechZero.sectionsEquiv_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechZero",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e3a16f233af33aeff726ed78a2b5ae5e0d0fa47782ada9cf5b4b4f57d6ba0bd6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechZero",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechZero:5488"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechZero.sectionsEquiv_symm_mapCycles",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechZero",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e3a97da771bd4d4fcd763c6bef4088ae5c055ad2fc5f85ef0c2cc8cf37379e18",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechZero",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechZero:5865"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechZeroAdditive.augmentationHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechZeroAdditive",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "88a67c626b929666d48cbaaba3a19d94436d75b71cd5560747f9cdf2161eb5e9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechZeroAdditive",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechZeroAdditive:962"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechZeroAdditive.cycles",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechZeroAdditive",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "70fd21b19ef343e10e2607072585a0e010c5c238355b50fa2bac87d5281dac0c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechZeroAdditive",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechZeroAdditive:743"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechZeroAdditive.differentialHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechZeroAdditive",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "650c8b4c898e9c86340337938bbd04d05dbf07267e192beb78e24dfcda6ca457",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechZeroAdditive",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechZeroAdditive:457"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechZeroAdditive.sectionsEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechZeroAdditive",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c33578ad2214021c25908cd837d6af8fe1eeaed33925e89528169961e80a99c6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechZeroAdditive",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechZeroAdditive:1331"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ExceptionalRecoveryMap.eventual_comparison_of_affine_recovery",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.FiniteReesComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "44d0766392389ae57e210ff28f3196c6f664bd5035b4021f797bd34ce36bfe89",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.FiniteReesComparison:1256",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.FiniteReesComparison:1256"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ExceptionalRecoveryMap.ordinaryMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRecoveryMap",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ac6949968e054429fd5e483397524ee934d9d7cf8766f41fb9b8a0118badbe93",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRecoveryMap",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRecoveryMap:757"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ExceptionalRecoveryMap.twistedMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRecoveryMap",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0e3dbebb22cd508fad33cdbfcf55bf26fdf385c2897e471cde4d8647901ee156",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRecoveryMap",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRecoveryMap:1913"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechResolution.coverVertices",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "97080913275f5f391f24e642ca2e640620e2d2849e3ad39531e3955874312dd2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution:2447"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechResolution.evaluation_freePresheafComplex",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5622fa84ea0cec2221cfa7ec108f08c4b29182ef7528254b64d6fef5ba87985a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution:3798"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechResolution.exact_of_objectwise",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "32172cf30468f143725168d85de6a81d4c60c7d4c0e9271a127365be96be8e78",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution:3363"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechResolution.freePresheafComplex",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "87f53d6ff3fa1802d1b717672f58868817ee9b1d7f9a0be9805ff2fe1c071617",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution:3118"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechResolution.freePresheafComplex_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cb01406781038de652c8d9f29626649160a571c95cfa44aaa575459769d3ec73",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution:4311"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechResolution.freeSheafComplex",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "28fac6ae3f025edc8c335dffb9eae71be3e61938f4f088fbe3a318bfa15c374d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution:4723"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechResolution.freeSheafComplex_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "17a09ff5480cf7783c0e1474d3662b4a3deea4e6750d26e7c322b542dfd4602b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution:5023"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechResolution.freeTupleComplex",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "78fb7e1d2f90b3c474ad7ad5afc032523f2fa618208d434c2f422ed57394de7a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution:1464"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechResolution.freeTupleComplex_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f24c856c0cbd09d7aecad585994dae5f46d739eb94f663d11cacc484db116934",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution:1626"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechResolution.tupleAugmented",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ddc4862799e73437aadf2fefcfd7addfaf4fd932623b0f0340146602205a4b36",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution:512"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechResolution.tupleExtraDegeneracy",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7eee836050c2bab2b6dae4d56e89a8519e33e7e4fa87342d15c78df83829f304",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution:650"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechResolution.tuplePresheaf",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e508443109ec35908aaae04da004f7d78d20d5a9d80e4bf4d2e671f7b67e125e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution:2712"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechResolution.tupleSimplex",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f68082d216c6e57e9ad648153549a4c3414d328911eacedcac5e8e622dafa5b7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution:323"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechSections.boundary",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8c67e23e9c22471d449a14960cf8831dcd3af277395f8f1bb47424e66694c471",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:5446"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechSections.boundary_eq_sum",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cae04e8f64b14038a589d10c416b548bb57248c6911b4fc70b412dadbab44504",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:5637"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechSections.boundary_squared",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a2aeff043375e370588206a03723c617f6c13e91f0a9570c9397ce24a708621f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:6131"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechSections.canonicalTuple",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "210953b1c61cbb7c9519471374bbca15e9adb8c23e55b5a16c4aa1ec353bf4c2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:500"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechSections.freeFace",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c73adbeb7ed7c1d6e3d33411b2d52755d77d6b760a22f2b46a7f829a8e1c4f5b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:4505"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechSections.freeTerm",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8859a1dee6d0402dc81f8f1a39d1e1bfacf8ca2fe4ce4cdd8593ac596f323cfa",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:2024"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechSections.generator",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c5544e0bfe8c47617ce553ab1d78bc4f3add3eb701d6aba14646045ecc698833",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:2881"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechSections.generator_face",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6c38c1f46de681f2da818db5fab5c7033a000352c000eded944bcfbf6679096f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:4732"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechSections.hasPrimitives_of_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "705e7d5477a504693017f99a40ddc0a92694824f8f0d4a254986f374214c6cbe",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:6999"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechSections.injective_hasPrimitives",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a93031437111ba6700734d2cc15d3fc8656451adea9d22e795717f4b82be7bc0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:7856"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechSections.sectionValuesEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7369fd03078031e698ffe59e31f618eb785ebc42120f3d944b99637de9aaf77b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:2226"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechSections.sectionsEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ec8bfe7b9216e27c1e916e4ff376217562156addd9e07a3ef736ca019fe1fede",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:2493"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechSections.sectionsEquiv_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "11fc3a756f062bb1198ed26f0c689742a85307d54713f56eda9e251da874704d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:3109"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechSections.sectionsEquiv_boundary",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a09e0fa19ba1197fb9b9cb6b63fc9a84bc92edd106dd3e14f2db435ac21c826f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:6518"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechSections.termShortComplex",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b03450ab92cc110a4e1feb29f254b59b07f03cf86bba434204fe91826c7eea6c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:6359"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechSections.tupleEmbedding",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "470da9405388c0990edd4ca23c52536e050ed245bd4efe613ce3856e787008b1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:2689"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechSections.tupleEmbedding_face",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "82fc860353c53b708f9f1cb7f13afbc33b0066d547417a00e96df5770368e55b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:4180"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechSections.tupleNatEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "270f9678135b76e28837ddfe67b06a8eed65e723d899a9153ffd9aa440598065",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:699"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.IdealPullbackMap.comap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackMap",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fa09f21114974fe39b6028c801b82b5f7292f65c982121fc3aa2a009dabfae4d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackMap",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackMap:2244"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.IdealPullbackMap.comp_quotient_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackMap",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "36a4fc345e7a05cb3e15313cb445407145c1400c582cef7b219970cf63277bf2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackMap",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackMap:513"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.IdealPullbackMap.map",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackMap",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0a763170ae02973b6314102547855c2e73787f213e204fc8c2751f68d69f4115",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackMap",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackMap:1109"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.LaurentCechFinite.cochainEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b9e32f5ffc0ec3e87baef58d3faaa2be19f9d07df924514a612369b27ccc29b4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:2142"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.LaurentCechFinite.cochainMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "42ceb1f075b1001971f3eacfea7654cebfb94c0570640483b7f40e36ed505087",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:1301"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.LaurentCechFinite.cochainMap_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8cdc6b20c8929c5afa38d49473929e52a9d2b12738f3609ebbd17ffb7567f72f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:1714"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.LaurentCechFinite.cochainMap_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "62e7632ffb8ee213456c0f3ca1d6931d8badfd31b25e1c3aaaa0d4e1b846e47f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:1913"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.LaurentCechFinite.cyclesEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3ca2bc5cfb5a31fdd49d9cedbc74aff54248ceff252e22ed3b52597235c80cc6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:4016"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.LaurentCechFinite.cyclesEquiv_boundary",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e2ffdb68cbe4caba7577974502316c5ea4653080e9155d70212118bb35c2b29e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:4289"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.LaurentCechFinite.cyclesEquiv_symm_boundary",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8bf996f7804b1ec32ad2dbe81cf29846bd095eb45c7197b16106fe8cba20e1de",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:4595"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.LaurentCechFinite.cyclesMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8ef2b52c5af8d0fe035f5e8ff76b2a8f096256addc9450ab28b20dea48a0f33b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:2429"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.LaurentCechFinite.cyclesMap_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c415e6258cf2885cc2f52c2dd99f4dcce2ec84478039f5b789dd158282450aee",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:3188"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.LaurentCechFinite.cyclesMap_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "516ec99c8bbaf34995561475e4f76fbbb43f777343cb0eda7a42e4b5dc0c15ef",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:3406"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.LaurentCechFinite.degreeZero_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3ea54ab1afbebda3902787bd69720c778e9140541adb37831411baa908e3b9d7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:5047"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.LaurentCechFinite.finite_of_comparison",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4c24c1c05f617e088fdd7eb0bede94aff25a61c21635c61a6c08cb764fe3966e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:5430"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.LaurentCechFinite.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomSheafOfModulesRingCatSheafFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "be76d71592ea24d5de981714951cd662ca3af3d332e2bf67406ca3c4289b216e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LaurentCechFinite:951"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleCoherent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "40425e21324a77b4d31e4c33b8f538bd056bd401e3d60e2aa1619c8f777fbc2c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleCoherent",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleCoherent:690"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.LineBundleCoherent.modulePow_isFinitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleCoherent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6998c9e26b689e6ba3b44e4b9ddb5642084999a8fd810b151b11e97f79f8fe4c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleCoherent",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleCoherent:1134"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.LineBundleCoherent.modulePow_isQuasicoherent",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleCoherent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ea2cf500f6d6c6c4c9f8bd76a31f18ab78c1d1e286052ee3127ad5b0864718b6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleCoherent",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleCoherent:1305"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.LineBundleCoherent.structureSheaf_isFinitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleCoherent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e96d8e30c80ac85a5f5eccb402626a88f51ea2b9c14e0568697729c8b879386a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleCoherent",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleCoherent:299"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.NoetherianAmpleSerreVanishing.ample_serre_vanishing",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.NoetherianAmpleSerreVanishing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "80af1c68d7e8e2d0f89d5516c03d9f4c65bdcfd99a7967f05f71fe7343577367",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.NoetherianAmpleSerreVanishing:661",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.NoetherianAmpleSerreVanishing:661"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveCoordinateAcyclicity.coordinateLaurentCechPresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveCoordinateAcyclicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fe1ce3902f2452ce8a19e5c8e6d3741d1a2682f8d5a7e746801f98474687622e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveCoordinateAcyclicity",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveCoordinateAcyclicity:2494"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveCoordinateAcyclicity.coordinateLineBundle",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveCoordinateAcyclicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "355bfac3f8bcb1ca654a14b5d630f58b8a1406fb4e8bac01867666cb7b8a4b84",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveCoordinateAcyclicity",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveCoordinateAcyclicity:3078"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveCoordinateAcyclicity.coordinateTupleCoefficient_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveCoordinateAcyclicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4455b877a983b41b69000a325c4fdae1ac6db8aa38aafa11387e5eadee3c81dc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveCoordinateAcyclicity",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveCoordinateAcyclicity:1279"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveCoordinateFinite.inversePower_cohomology_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ccfc22023b6a44e8b2605d816e332a28a5bac8601bd48384f89c5f5c15fa79e9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFinite",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFinite:764"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveGlobalPolynomialAlgebra.chartExponent",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomialAlgebra",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9bbfb241b121f360105e1fb2b761a7b64fcc9ed03ac76bcd7b1a80897c167d55",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomialAlgebra",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomialAlgebra:538"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveGlobalPolynomialAlgebra.vertexLaurent_dehomogenize",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomialAlgebra",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6e9dcb7aa32d623af32e724dbbac89594b0cc7d579748d2dcbca7d01f976eaf1",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomialAlgebra:3447",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomialAlgebra:3447"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.FullGroupAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f1d91f4f2595179b199cd2f366a1b1fb32a6e5e623aab36e1224c852e1c71bab",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:3012"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.chartToFull",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4f398cd506560cb902447561a2cfce755c0269ab914706cad63bdc6f4531c600",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:3074"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.fullEncode_eq_standard_add",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2e02aa05c6c350216b61bb6cbeadf9cc87a7b54d3be1ac049197c95810740d42",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:1888"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.fullMonomialUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "21024acf2ec217274041f8519c79ad8f66da8c822c680ce99cd765d0270b677c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:9187"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_009.jsonl"
