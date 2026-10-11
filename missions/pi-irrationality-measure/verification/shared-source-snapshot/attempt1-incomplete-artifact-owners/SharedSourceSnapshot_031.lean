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
      sourceName := "OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_eq_sectionsMorphism",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "45f669fde0b8ef5e14f46d663f56e6c136be6cf5ad513378e2dae997e15c4538",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections:6553"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_local",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f044ad77093c6bb2ae506d505a0de15eff1c0a2022b36dae91b4cff229c195e6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections:863"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_local_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a20d3ba055f52e19fc14db306051666837e31422dafd1316f42ab00acd16ebbf",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections:863"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_over",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ad92282892cc7b2f5129c545d2ca3fe03af386eddf0b872f685d70b5ba69ad0a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections:2007"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_over_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e10b7032d836d135958419d1f7acf5ec15d73348a267a5b7e257dc61000e42c1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections:2007"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_preimage",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f4d04bb59e10c6fbf4ad6dfe4bf196be0016f942f545407820919ca82b33321b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections:1253"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9f84642611d5931a8b7c0ce10fa2901d1abc3848915a179ca2ab467d185c43b9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections:2480"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.fromUnitCoordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b6bd2e8cca1d8dc0aa812a7f66d790c69354bff2427aae725e79bdee157c46aa",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:3398"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.fromUnitCoordinate_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cba1c9bdda6291a98af6238f4af0567e9fec81f4ab0c32cac4e9ae5685dec917",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:5587"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.fromUnitCoordinate_mul",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "31d77cc64fd736f8cd668ae27e6bbf243d68124e1e7ffc111afe9721fd3b004a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:3622"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.fromUnitCoordinate_natural",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1913345f17d5d3215dfa15d4ffbdac17b6a5e34585cb4d3f3fb952da5fdcc9cd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:4110"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.fromUnitCoordinate_natural_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ac102823dd8d988c7f02b9460368374fd3f0d54a8300aa4912c15df8332508cc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:4110"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.fromUnitCoordinate_preimage",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "648d8f6966de07ecf0b791012c33c93bdc2e1933115abbb8e849721f01fa69bb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:4902"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.fromUnitCoordinate_scale",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0bef710a523a2dcdee47b9e2d026975368f8990ee500295fed2a613a9cdc993b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:4531"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.homogeneous_eval\u2082_scale",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aabaaf1804dd8ba1b97e11020c29f1f960b91b7923fd4fa9ed31bd71eb0b4a1a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:300"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.identityCoordinateOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6c600aaae1332a829220292238a23d9e7ece74b46e0d8cce3ebafa891aee900b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:16324"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomSheafOfModulesRingCatSheafFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a9072912f61556764e941c0e28edf6eebd07d989d27eecb33cf4bf63359834d0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars:3554"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomSheafOfModulesRingCatSheafFreeOpen_1",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeScalars",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9e460fa180457d1820d49a71a559213d5f6b0af984284af9f8a3792532ed56ee",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeScalars",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeScalars:1029"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.isoPreimageSectionRingEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "098bb5342f1b21bae3794a048305073855e91337b0ce804e6e08d8325274d4f5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections:590"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.isoPreimageSectionRingEquiv_appLE",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "830421d13cba147dbfab55da4d33acc2d89210525263b240373cff70cdd74ea8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality:825"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.isoPreimageSectionRingEquiv_symm",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7e7edd4be1fe6a814c0b8df05ef005193d1963faca921182275887c2ff79eb41",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality:303"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.negativeCoordinateFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeFrames",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "be9bc766286d116698e617adc0ca4043eb15548d1c3bf52473333c1354b73693",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeFrames",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeFrames:466"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.negativeCoordinateFrame_frameChange",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7f39ba6647f6c0e9a1315ab4619d7999f15a01dbd710e5b05be646a009c98b1d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeFrames",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeFrames:721"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.negativeCoordinateFrame_hom_change_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "12733876f1ea8b9f6a4c9402c836d70a19dbd164d30263af95405fd53e435677",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeFrames",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeFrames:1655"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.negativeCoordinateLaurentPresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "de7a0e900f5c8780c68a082191350b1164a712c670a285e5ad9094149f2c7cbb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeCoordinates:3416"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.negativeCoordinateLaurentPresentation_smul",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeScalars",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "70cb03124af1822a1aa01a38cdf3b75bf835abe7db8805a93c68ff0b216d14d8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeScalars",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeScalars:1273"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.negativeCoordinateOverlap_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f07f08cabc10f25bfca6fc573a87d39af63877886001f510823acd4970747d01",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeCoordinates:1099"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.normalized_coordinates_closed",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b401faaf7cda1b2192d6bfe4903ee2d6446d2405cc67c002e478e4d8d51ce953",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:2611"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.normalized_evalAway_polyToChart",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3d8b39c2eb109ba735bb7bd17bae0ff3395041edfaea14f1a6f464e5c940a45b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts:1973"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.normalized_evalAway_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8b12ddfbf4d24028cdc5c7a274ff701ee96965152e561cfeb7dbf41efe5c06b0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:442"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.pencil_overlap_basic",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5da6396ba77cdb16201032e0981f8e5174f0aa1cc1ae8f3762f893a013c4b7b0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts:7514"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.pencil_overlap_reciprocal",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6d469af3d4a5260ad2239ece7ed4e51eed34c3cd6373387910dd79f9c2c131c5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts:7860"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.pencil_polynomial_irrelevant_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "288cb6e21bde2b5f089e04089a376b67e0f8be5960fda91b3087b004c9073159",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts:358"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.polyToChart",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6823aed170898e0513498fe538780541a54ed81d17342372c61014fdc16bd352",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:2130"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.polyToChart_comp_chartToPoly",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "be534680c7a9b7e8b5791460eed2a9ad468acab6b0d2ae5544103bb9e944c016",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:5150"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.poly_X_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1cbd07372e63c2cbe564cfb312cadca378c8332d5f84856d764c8a1f45853360",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:1023"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.polynomialChartEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9d1c1fbc8fcbdd31fe66bb300b01326c629cf5c84215612c83b18b637e5807b3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:6128"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.projectiveBase",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "421c15b8c7e8187ef0c79733929b26569fecc5a6a694effe461e006d29a8759d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:5535"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.projectiveBase_separated",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7697077853647d0ca5d5d64c136c4417a3f78a48a2418d98e9472bfd9f95d1fb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:8118"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.projectiveChartIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c17097e6c9d6a0beb0c97089a287e729eb5729b56141c521b24ab0f1a51fe9dd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:6436"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.projectiveConstants",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "46fa83973bfebd28bee51f84b1bde92aa089d46e3d6070de0ff109f1b96a3d22",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:5282"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.projectiveCoordinateCover",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5e7cb8338c9d057d65b8bc9713224ef1c2e3ff6a64b9cc87b6d75da03b20826c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts:848"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.pullback_isoOpen_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionsPullback",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "78f88720a97fb392ebfb5310db81a0350e1d87eba87f5a4d41555c52831caaf7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionsPullback",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionsPullback:2241"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.pullback_sections_cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionsPullback",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "72bc5130ed46fe6a5e086ca62750814b94e2f765a6391c86abfcc1bb20935b05",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionsPullback",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionsPullback:3069"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.reindexCoordinateCover",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionReindex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e924bcaf1f1452dc23118c74a1ebc38bf1e251119be99f82ac741dbfbdb3009d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionReindex",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionReindex:834"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.reindex_polynomial_irrelevant_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionReindex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dcd56818987261e58e6449540ff6298248b13ce70ccb7f1106d8642896c5dd6a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionReindex",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionReindex:345"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.schemeIsoGammaEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b6af1a9c43dca7c0aa0036f422a7ced1a1cd28e797be771772a146aa7fb60f5f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections:765"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.sectionFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c690eea0779297e936228ad6223f9f62734a47d57d05c91c105947f1c8b7c45a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:12834"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.sectionFrame_coordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateValues",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "66e8331b0eb8a96163d923a9b1e1eb52d5dd289272d5f0a4448a3af9a54216bf",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateValues",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateValues:2264"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.sectionFrame_normalized",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "30db388310f74ba62d464c97af32ddeeb2e97e2a0eb193697300a83b73aca95a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:13189"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.sectionOpen_eq_coordinate_preimage",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "12004d8bfc240613e8a0e113bc8973d2b50ad352dcd2aa8896905febf460968b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections:1547"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.sectionsMorphism",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "45797b2124478b734c052a40078f4888faa9823aaa870debcdad32e80aeb3bfe",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:13456"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.sectionsMorphism_frame",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionsPullback",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "be7252decedfcd6d0b939aabb97066e5f0e7dafc10ba7cf61a5f1176d3e3b839",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionsPullback",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionsPullback:449"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.sectionsMorphism_local",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "efe68e30d55e27856d7480a15df961ca09e0823415680cf82a899a5131468163",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:14110"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.sectionsMorphism_over",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9099b0a80ee2a5bc15c14f94a00985f2f8cde290f7b07b9eea95efba3c9b28e6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:7128"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.sectionsMorphism_over_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6d30d51e12bc76ba38f8ad4ab04ac1b66e8d05d7c0ba74ebb0cc3cfa495e63cc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:7128"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.sectionsMorphism_preimage",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6ca21bfefd78d5966022326f46e1a4186431902673b6202904ecac24d13dca05",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:14873"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "33ece8ed007ef40c40bd6f486946f183c337ee6d79a73a612cdd61a34ab6aee7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:8255"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.sectionsMorphism_pullback",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionsPullback",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "88af512043f0390a471e94e8fd7d0bd68605e89d1f948a72b91204512e0f2e40",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionsPullback",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionsPullback:3437"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.sectionsMorphism_reindex_closed",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionReindex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "290618ebc1c6b6b422de5dc10d4dc7df7a50900c659fe482e0f2a4c2996e0f76",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionReindex:8636",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionReindex:8636"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.sectionsMorphism_transport",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "559829a07ae1c41c3c10e24df3cb1a564efbe7d74fa9bf3d9e16f1652eaa5253",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections:8594"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.standardChart_cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b24c49957943822331ee637666a1a5d4f8d652f47eb269563c84933ecd11a3a0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:7535"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.standardChart_isAffineOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6ba3f19f692eae76b741870838ad4da76bd09ecfb1aad7ba3395a4b8ee47bc8e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:7374"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.toSpec_scalarMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2f6e874b318b9fbcfd99e2d2eb7c0231cb114a8399e29bafce08eea97e20c268",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts:8700"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveChartSections.framedCoefficientsEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fb6a16df3b46d4464a3e0afebb5d3753d099bf16dad02ee59329965cf3f74ca3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections:1238"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveChartSections.framedCoefficientsEquiv_change",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficientLaws",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3ededd06100804d46042cffe339a1b5c76faaf8a9e9319b36bf6468dcad935dd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficientLaws",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficientLaws:1212"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveChartSections.framedCoefficientsEquiv_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFrameNaturality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1e4d422aea0d83033f3ede4408dc984e3a72bcbbda2bceedf5ccadd421f7d72c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFrameNaturality",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFrameNaturality:3027"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveChartSections.framedCoefficientsEquiv_smul",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficientLaws",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0ec0688f50bb92c8d658a623a2292330e6ab06dda4d125b30bcbab59f2cdd893",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficientLaws",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficientLaws:364"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveChartSections.framedHomCoefficientsEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d24d21461ad3c9b946cf9e82a3680ce1d48bf37ef82d55e9ab61d70fce6d7d5b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections:1584"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveChartSections.framedHomCoefficientsEquiv_globalSection",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveRepresentedCoefficient",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "97489c6558895484a95f62dd06a1bdb8b5f74e76277822b9be9cd1966fd7e5f2",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveRepresentedCoefficient:1035",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveRepresentedCoefficient:1035"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveChartSections.framedHomCoefficientsEquiv_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFrameNaturality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "05df8f443753eb2c0ddf3c4d3b1a6b69725f9b124031206d5b93d9890ec9289a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFrameNaturality",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFrameNaturality:3586"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveChartSections.framedHomCoefficientsEquiv_smul",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6a9a30ff1ed230f7c9e633355252f4a121d53cfd90f60ec715ede65f12f48292",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars:954"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveChartSections.framedHomRingEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ccecbf5c3c0531a3fda69680d6ba5d61a0e03a990d9fe13729c9aab3d45df617",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections:1784"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveChartSections.framedLaurentOverlap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9c7e597de429b115695f0c14192e912e313ca0255f0b4699b15dd49d3fac646f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections:3869"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveChartSections.framedLaurentOverlap_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "19d87dac2b4ed1f66bbbae63ec03d33fd6b8ab1a0fbbadbf5757c18ee29599cd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections:4190"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveChartSections.framedLaurentOverlap_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "62237d84839bd37646030ebdf78ec12ba80d1456db0e15c575cad93ee32e95fe",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections:4539"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveChartSections.framedLaurentOverlap_surjective_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6238f04b7a01e7aaf424f16b42a9a78cb93028fd6d5b0c2d58431b72edb6562d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections:4933"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveChartSections.framedLaurentVertex",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8f48e1a43b42be498b2be4ce9bc88041645354c5a98ba3fe06ce259330a97661",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections:2183"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveChartSections.framedSectionsEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "121823e2b5051a18c258159d8f26565eca06aed9f9f7e4449beaa40246ee7c99",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections:658"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveChartSections.framedSectionsEquiv_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFrameNaturality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2c6c775ae19628614d1939f11a3ec7df9a98d94855bc48664a793b8259ce12bc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFrameNaturality",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFrameNaturality:492"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveChartSections.freeOpenAddEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "36cfabad2ed1348fabf9dd8494ed8e806f4f984e39b9b794b9103aa36e8b4cc9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections:1435"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveChartSections.freeOpenAddEquiv_smul",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "26bc78fbd3630d8a89d6169d7c9c45b67aa9b01467c756486d3b74b1d6a3c833",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars:775"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveChartSections.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomSheafOfModulesRingCatSheafFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bd3e40b6eb1d819a73b09aea436ca181f9ce9b78a58905d9b6fd544a7c32665f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars:565"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveChartSections.topIso_hom_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFrameNaturality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "583496ff28e5cab8a6820d86f266683e1f44dbc5c81cb339e82bdbea50851db3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFrameNaturality",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFrameNaturality:2625"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveGeometry.genericPoint",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f87c8fb6a882cb1aa31f607ab7e32622549b1408814f37df96d4e2322b665cbb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:2162"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveGeometry.genericPoint_dense",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c764455b2417e3fb93f2cdb2c1180fb98fdf4b94c273d4fa51777cd0751f4224",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:2438"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e1610fee681f43ec181fb428ed1f3aeff7dead53793fb23bb5ef692f7b0d241c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:1612"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "579da38e2a8ef91310278e646df8a824d37076855a23586bf70c0fd46e9d7ff7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:2779"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "555f03171d3e8499424dd5749d3648a51c6a2f43baf7bbf7d50d995d469c9763",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:3070"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "89f717794f5163a6d2a99a9b33e929dd427a1ecd654887eb6f1b3061ea6ed011",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:1881"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PullbackTensor.framed_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6a7c65125ff667a5348fc03ec37703bd2a9d7971ddfe611aa6c66c3bea2264b4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers:9222"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PullbackTensor.hom",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "839422f40fa306b2c865fb232768795b2374f4da522170439cc757ee99215932",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers:476"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PullbackTensor.iso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleProduct",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8c1ee673de3afc14d22b0826d378299f6a7ccf21b0296574911b2915949d779d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleProduct",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleProduct:3028"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PullbackTensor.line_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleProduct",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b22cdbdcb62b4d5e516583d4a78103d74350ed820df93e08edfc15c698a81d2a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleProduct",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleProduct:1554"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PullbackTensor.naturality",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fd5c9909e60bf7cca53f01cce4cdea1f82a1faedc977dc8795c11278b29ced41",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers:1386"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PullbackTensor.naturality_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "39025baccf9de7310fb24538ba445340119615279bf30a2250e6cd1fd9d48f0f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers:1386"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PullbackTensor.open_transpose",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b8ac9f95841595c78d4ed657b38256a72da8761e4a8fa2d4baccb60ec4102465",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers:6056"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PullbackTensor.powIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e880fb28e7f30d7c9b351afe94dc82a429ced1986ba07ed2df7ece26e222104d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers:11708"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c94fefd0cb23c623473528ad88b616a5caab149c9e63a11d441b2827c52bbc07",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers:10057"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PullbackTensor.restrict_compatibility",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0ca2f23f9b9a54fb17b9efa3e36e10014653ed3e1d84ba3e7a7eaa83e6c7c2b9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers:6474"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PullbackTensor.unit_compatibility",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "613182111039c58c69a1797231cb693de299ccea40a872f0873773354921f399",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers:2433"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PullbackTensor.unit_hom",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a2ff7e345e569ef2ca86bb35d3c62a7de9b581c15133f918694ea080a8bd8c7a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers:924"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PullbackTensor.unit_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cc14f48f378bd705bb832e9fb0960d13894c7a663ef5fa3b73d0247f7b79036c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers:5416"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PullbackTensor.unit_pure_structure",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "91498581dd23190588be93ff53c0508800d5b1dac23a2e7f804002f7f3c7ecf6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers:2178"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PushforwardTensor.hom",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5bd51cf6508ebf8deff0f750a1e09c5b12aacf33d773d411674fc8fbbf923cfe",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor:1200"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PushforwardTensor.hom_pure",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c7c0a1edd044ca94865e45b9db49fc26dc605f68f603d6fdbbb49201882e6b95",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor:1450"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PushforwardTensor.naturality",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b8ab5484f7367f81317b4e1d8434f089631b4c2d0bc1fcf02e6a4e87622712c6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor:2035"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PushforwardTensor.naturality_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0a5c8562cc7bda0f1a385f78a56775de98a8e1afe60d6219066d13ab17b1aa28",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor:2035"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PushforwardTensor.presheafHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6831400920f5cce1e7491805410f0abafb6d90a515709c45ebc9099821bf495a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor:491"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.affineBlowup",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "db94dd9b884af6f3373847389c9ff1e6fd6d306308438b0d9a195cc3f36e89af",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:4768"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.affineBlowup_isIntegral",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "06fd9d08407a78d7973c158f1296b6a3a0d59e23f662c4e13ac2d33fd1fcdfc2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:6054"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.affineBlowup_isReduced",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7d6d5acaa6c749ce65f76afb24e4d974b8e88a26c60b769afb18e121a3a7be88",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:5795"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.affineBlowup_universal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AffineBlowupUniversal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "847c465141f5cf91d0b23ec0ef3f149f73abbe0c505c4343d794b75343b93907",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AffineBlowupUniversal",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AffineBlowupUniversal:2252"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.base_generator_comm",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9e677243b9f0c331bee6cfcd2952f884ccd4ceb768b8d9ad5e10f70448647973",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:4080"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.base_mul_ratio",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "99193056d2f2943f906b22a11dd84ce709cf1e883365eef5c56a682341845271",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:10564"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.base_pow_mul_mk",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "86d6ed014601a00837f3038a3eee9ea84d29d998716f97ea445fdba61177def7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:377"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.chart",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "215027d2ad118941f7f5421473672f8367d4d366201c62493acc838355a582b6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:7219"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.chartBase",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1096454a1a0093d026a2df5b434aefeb164825f27fbe1d01b1d98aa88220c30a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:9399"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.chartCover",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3f06fd2a9d8693c312dbcd499785d426a74dc675a01aac415ae9bbf06051be2d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:1776"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.chartCover_projection",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a007c81d61be169954d62f78d6e4abe88f7ddd8014cce28aa2b4ad6938b41afe",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:2474"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.chartEquation",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ad4185567fa4fff24225e4ad3d8b883ecf2f20c4c2497d95e2f6ce81bfc153d2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:4062"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.chartEquation_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "408670263fac2d5aee247ebfe48a7a945375c4e853921162fd94e24bbd374e1f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional:4606"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.chartHom_ext",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8660bf62b2d7235ccd23d24be996daf0c5820d59edb6507c6795ead789b92451",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:4909"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.chartMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b0be28de102982bf079be35f741c73ca6250a5a57ff22f461f40b0bcb3ffd243",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:7301"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.chartMap_base",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "060e554681bb4e9d2b975bb7eef33d2e23f988e04bd1ae4290ef4485d7c242d7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:9571"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.chartMap_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c8be2fc85a9da69a176e37d8302ca089f3cd890de0d4a59b755d779043f98313",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:8292"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.chartMap_mk",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bdcd1f24e6f5b78d6784fb7b0fb5f5a080ba7ec58fe998b0ac13df96cbf9491b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:7685"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ReesGrading.chartMap_ratio",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "65afeaf9b1978e4e369e664b2ae0c9d4814353559f9c0f55d8404d7f407c9b54",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown:10294"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_031.jsonl"
