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
      sourceName := "OAI.PiExponentSeshadri.IdealModule.closedSequence_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a44f57b1839069e0a02ded883bf728b7d640115c059cfd366bcd3579c178e662",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:9417"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.closed_image",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0602ae8f45df3542cb4ac9ff15ecb30fc6c93a1e24551921ab4772d95ebd7fe4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:3175"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.descendedPowerLayer",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerDescent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "76d8b81bf91ff9bf4f095b8b2c4596d14e1cd2dccd3a8f09b830ba5f620fb9fb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerDescent",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerDescent:743"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.descendedPowerLayer_isFinitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerDescent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1952651a025c89ad883804196b9f257d85774a9c99a65dcb36d39306960bb360",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerDescent",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerDescent:892"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.equationToIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "70b0e067c2aa2fe06cde2b963d7fd57c51d8707e6492eabde355439f2ff4d755",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:5265"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.equationToIdeal_app",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "183fa9d6e36e0b9a2c86d0a1723c50ebdca58d424382577ffc8bd068e6c919e1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:5662"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.equationToIdeal_inclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3d036d8a27326c7f6798a609b2f841f2c3517cf2cc946bbf00a49cdf2c1e1a75",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:5457"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.equationToIdeal_inclusion_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f8933a00c55d902844607b4b988fafb552011e932f2c2e528106508b2956f49c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
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
      sourceName := "OAI.PiExponentSeshadri.IdealModule.frameOnRange",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "97590e3324712e7ddc9122b8758dd9ce660195d37997a3c4849b4206a66f5dab",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:8211"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.frame_restriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "182d361dfcbf77bab03d5fe1968660e876d2a580fe6f694a22022b7f16f70cc5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:7009"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.fromSection",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b95175cc5132e958715200526b0cb39392f13638e7ca6e3ff650e35c94348e82",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:1877"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.fromSection_app",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "63f3fe925d55c76ceb52666fd701ad8a8df771fa8cf71e7417db9d430c186456",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:1988"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.fromSection_inclusion_app",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "89ea5c09f078203c43681ce62e9da9bf8b0fddd87020dadd43a77fe10957bb7d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:2180"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.hom_ext_affine",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6fb6bf6eae7524317299f2bc012a721ca4d103270a75d89ff1196b8c7a72e7c3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator:362"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.idealModule",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e1578b22f93ca39b05bda48bd21ddcbbcf35c0b60fd44a94abb410d4c4423277",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:792"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.image_eq_ideal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1c38d8528f383b8a7e48f410c053f08dc633f31f68dc9bc6e53ee2bc942c1a2e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:2679"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.image_eq_kernel",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e176fad2b00f71b01460598b74c69ea7742ce275324bed8bf5ab5f1544ca047e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:2064"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.inclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "62bfbb95c4d51adace1a7e3f7cd42aa787032a9e77ccfcdf463cf72aea9a47a0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:850"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.instHasExtModules_oAI",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.IdealPowerCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "40dd8f77e3a38d30a072a5859c64482c1277fea368343990c64082f1a747461e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.IdealPowerCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.IdealPowerCohomology:450"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.instMonoModulesInclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1c519f9d616a57d574b8b323648f8325410646fcb20ac655443769065277f7a1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:927"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.isIso_equationToIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a26cb2006728912ceb398afaac99ea299d43397aa7072a9390a32ace6ca0c1a0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:5991"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.isIso_fromSection",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cef9519d3de1d0dbcd115e6fc9f9068fd0882ecb84ca224e1c95e9f0a71484db",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:3098"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.isIso_of_affine_app",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ac5cdb4af86d6b7dae105acfb0c3ea609b0cde524cd737c6128159ce7b9069b1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:3412"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.ker_appTop_subscheme_morphismRestrict",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "31cd56983570c967b3838224b316d3dc683ec3ff574323c3feb0a027611a9711",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction:2701"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.ker_subscheme_morphismRestrict",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fd3b9bff166f2e9981c59f9a3e341825a3b59c8b31a0f7bb00b63bc97db8163b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction:2276"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.multiply",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b61818884efc9e90b847f792c79056f19d4df2d1cc35a3a239f14ebc9957de5f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:3993"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.multiplyToNextPower",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "26e60ae4076dc2f31d88b5ee155f89c7482a1cc9e8885d5debc1b7febbb4cec0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator:2115"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.multiplyToNextPower_inclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fe7ff867a175683b4ba1dba248ae73722ad192583ed0a16083746a87285d1e21",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator:2426"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.multiplyToNextPower_inclusion_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f4e106a360512788386b5fdc628eaebd3b52a5f56f611a2ade1b50b4ea24e035",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator:2426"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.multiplyToNextPower_powerMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e70532e6159b2818170039f2e7620271a07ec7055e87b727160341158019102d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator:2702"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.multiply_structure_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ec083c5d313035fcb31fb9f08904c48bcbf90ab64aa13d0f90d15446d31ac8d7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:4787"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.powerLayer",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7c3dcf9bab1c7b24944320e791f7d51bf3f126cf08e6bd2b89af7c3d3c1b56d8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:2631"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.powerLayerPushforwardIso",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerDescent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5485af9e5f8bde57c6fa456ab7b685b4828be62cdcb6b10a9ba08f2c39a5d165",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerDescent",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerDescent:1179"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.powerLayerRestrictIso",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3fe3dc33024e243099c92d34f570703af4754ec394909ea7274549edb025ba4a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction:975"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.powerLayer_isFinitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e9a6df64dae93e2fcedcb86e3b5a5f166a9c84e09557bc5ac0fdc27e0cd9e113",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:4443"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.powerLayer_locallyAnnihilated",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerDescent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a64d1fb5fe71710412c1a9ef8f8162cb92e0b7a1a6c178b615f5ae57c17741d8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerDescent",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerDescent:481"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.powerLayer_restrict_kernel_smul_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ec93a07d2bf8c11bc2026ccfc67eb2b157b3c73585004a929a327a34864b680e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction:3278"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.powerLayer_restrict_smul_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f36574cfc2206e2595f581b66339c7343e9437c79e0709b06e8b9a2b8ac897ec",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction:1329"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.powerLayer_smul_id_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "55ac715024749a3acd6f308fe553be9cedda89b8150fda85cff7a45f7474a821",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator:3352"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.powerMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4f805df10914b5bc6d0871454b6319a8bed040f418fd82a728bf0539c9561dc8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:2363"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.powerMap_mono",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c34a270ff5b62bf2046886286844805b8e97232af899cbe7950a7b8cbe9388bc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:2527"
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
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration:2721"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.regular_map_flat",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7a881a5fba77d1b357a458280b0b06850bb1012f2bf9f717d921d960327f059e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:7721"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.restrictedInclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d85cb2e9067e196b5128a74e1550a2aee3d5bb818781aaaa7d599d2f1c947cae",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:4698"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.restrictedInclusion_app",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ea2c5a1ce0d49c46d1510a26c2bc75a93c6fe1a9e88f99024fd8f3f394f2cdd0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:5469"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.restrictedInclusion_mono",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "18f7ccfd6309d4bb02b15595d3498db8faf208d24b44fe6a5a5d676577cf519e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:4941"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.restrictedInclusion_structureMap_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "85c6f5f99187dfb8f1ebb050fd052d61541fca63a3b4c522acabd149b7b986b6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction:335"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.restrictedToClosed",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8ada359ae42bbde1eb0d5a8d3fd2ce264ed1e4b7aa8b873c9588878a5dec70f7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction:776"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.restrictedToClosed_inclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "37d2f479b5a7d1b785d416b94349cad79c08b0143dbc23dbbdbe30a9d652c77b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction:1058"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.restrictedToClosed_inclusion_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7daea03a1404da374f35d18dbe410096b48afc6c7e9e2699387300d6af7f9ee0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction:1058"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.restrictedToClosed_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dbab76eb1983ba5909a31ddf0ad31053e3725d18c8762930abced7ae7b2eb476",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModuleRestriction:1299"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.restricted_image",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2bc6ecd9bb7013cb41de9faf5bf30e1176cc909eab525b945cd51b48755e5d79",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:5751"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.restriction_mem_ideal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "68c1201aa00bea08559f778a7112a2e3448983068b190133f4772be3973b94a7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator:794"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.restriction_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cb5faf6b510a698fed573b8b614feb2cff86d823aef91d0ac6460f4951c75927",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:8173"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.sectionFamily",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "55abb19102d8efaa7c910c9a6a11d80daa31d2b6dfc84f6d1ff6e47799e1fff8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:1586"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.sectionsKernelIso",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dad03163dca198d3bc42c64a2abb199f230c019bfce875e967deda3ef0e18b02",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:1015"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.sectionsKernelIso_inclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dfd52d64352079e3e4ff1301bb0fe0cf1ed480d827a77f1fc014e53d85bdc1fe",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:1389"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.smul_closedInclusion_structureMap_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e17661ddeca917d82e22c2db9875bfc5e98fbb08a6861e9f0b4d669eb654e9e2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerAnnihilator:1334"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.structureMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "697b9f61477cc7b7c320e145b2b593e220a955b6429fca41cab26db3d1ba819c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:517"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.structureMap_epi",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fb25f3df985bd6c819fb3f1e7c94779fc14038d190546e4f9bc953152e27042a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:8672"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealModule.unit",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "303e3971907b7aa2b876564821211d130662483998f81740524c27d8c6a363ea",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule:438"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealPullback.comap_ideal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c18da3ad866866a5955544536bc728e29de76c7974031b51a611efc7d14ad3e4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:11216"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealPullback.comap_isoSpec_inv",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a8b9c2f978db248ee48167dae0447be2f6b70e9f497d56b8dd8d363dcc11e123",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing:1133"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealPullback.comap_pow",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.IdealSheafPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a2ebc79a69471f2d2cc51ae48edb7690d393dec3fae80c650521853dc100d06f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.IdealSheafPowers",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.IdealSheafPowers:227"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealPullback.comap_top",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1c07e5a04b5c3f9c8efcf0cfc9c37705d585322c0698e84f323ead7a74ce8466",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:9079"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealPullback.comap_\u03b9_top",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f489b82b8fe1fe9dbbeac3c78e78b28e7a981ca0276a044ec43c4827b1bd62e1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:10754"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealPullback.map_top",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b654d4dcb63b3ffece1bf334d1fc987636a71f235d681476e1ac4a311fd75d6d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:8833"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealPullback.specIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7cd970f36be9c2a49f64aa0cadbe30ff43bc114fb269972c889968ea1ff40408",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:9933"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealPullback.specIdeal_comap",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c1cfd0eb429581e9f5660088e5382f75605034f1f3cacf276952681cc65fc729",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:10289"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealPullback.specIdeal_comap_toSpec",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a06e1de7c1dde3777ef66d791236567fa4a0f23605bd48b38ac879860f07bf2e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing:669"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealPullback.specIdeal_coordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AffineBlowupUniversal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "90fc65db3218508075df359edf6fd6f74899c9a45a0c97994f8c3e2e8b7fcaf9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AffineBlowupUniversal",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AffineBlowupUniversal:379"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealPullback.specIdeal_pow",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.IdealSheafPowers",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "24af392c7eb14a39d541a16c9596be84fb5c8e7158d2ff4eceec76f803d32dc7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.IdealSheafPowers",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.IdealSheafPowers:1110"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.IdealPullback.specIdeal_top",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "183a58f0c517f7e0c296541a18ab7608310b28de1fca1777c74d8dd11ebc1df6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:10100"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InjectiveRange.injective_of_retract",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6860f9407634fdcc821e72e2c5a054a63ef688b6ec46ab5b223d23edf09581f9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:5043"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InjectiveRange.range_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b0dabab50abf2b2590eff7dada7b508f031f839e1a20890e27de3c0f8763bd91",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:5505"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InjectiveRange.surjective_of_torsion_cokernel",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f5da11cd2260d8b9485a48dbd7a522f9866cb64c7fd01d99689e4420018244d7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:6492"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.affine_frame",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PowerSectionExtension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1033427d9fd352b55a4194423717fe415fec4fc1bca48cb3090d1854a5d9586a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PowerSectionExtension",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PowerSectionExtension:10468"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.affine_local_equation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4a3e57e49c343199faa711e2c7ef150673732d98d0e8f41d635d56adeeaaa24a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:5551"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.frameOfLE",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PowerSectionExtension",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9e76783a108ba9791a6fb1ba63308e61a9946eb40cf3349cdee5406cd6fac6e0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PowerSectionExtension",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PowerSectionExtension:10041"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.frame_ideal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesRelativeSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "33d598332c9969c40f7aa4bb2f7f49f0916b27b5a9984ff26d1cb5b1b9bfe785",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesRelativeSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesRelativeSections:425"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.image_eq_comap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e47cc023db500161100fef6ded40c994873c2297287ede68efc5300261fb0335",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:1867"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.invertible_congr",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "740d5c958d7e9c0b63cdf70f5a24853dc1185ead9fd3b2ec49edf512be4211ca",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal:4443"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.invertible_iff_local_equations",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "78c47eb425387dcd32662fde6215b71c2b30ac340c8da087577e156a98cb5e23",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal:4111"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.invertible_of_cover",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "39166830b3bce38b5c58be442eb8941a5ce45d0f6ffb1efcf84e2e36cfcc0151",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal:5834"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.invertible_of_local_equations",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a9839054aa532561e6ed89e94403a7a5a6fb135a86dcb217476c85a34f282fe8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:12312"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.invertible_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c5056d0abcef239c3df1b3b7b953c093314c1589bfe47d0b0d5270eb80d4d533",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:7471"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.invertible_restrict_general",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7cd4a8ae7b4d9cfee6a44dbe17241062c73dc7179e7bd1cd1ce981b62baf62be",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal:5495"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.local_equation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2d00a855e3aeea5abc4cc68ace66f55c5c5b97dba14589b632805aa6b81e6739",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:4094"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.local_equation_on_chart",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ba4fddd450551577d8e94f141a973c75b9dce670a8767ace59dd44eac46aaf33",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal:1756"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.local_equations",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2c276a07372a2c8a5c64e6513b514cdba87cf5473a3b2d038f724f8a6dc5d383",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal:3353"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.presents_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cb741d8da29f178858a3dece3e87dfcdf88c889e4d3058ff7b9fc6a591b7ed7d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:6855"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.presents_restrict_general",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "30a20f9472cdc051a9d3fcd08845c3f1e213c88853f9e72353fb2c0a4fcf84f8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal:4819"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.restrictLineBundle",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7dd30c7563ba137bb0e046bd078b982b238943ee87e3b227b17b73ec12cd47f5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:6145"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "51a53ad27517bd2955b26c7d227d4e9ff6ef69c39bc85299f23f871382045d81",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:2523"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4f302f9a8c81e619211e012ed05b0451c55f6a74a5b84b082583926128210814",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:2722"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.restricted_image",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "71118f2837124136209da60cfda07882fd548a57c1bcb75d2214fdb73bd0aaf9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:2957"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.restricted_image_on_chart",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4ab01fc73ce1e8e3023d09e559022c030ec3b118520210a2a3c1d61a05d157fe",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal:317"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentCech.cokernel_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4c11152f5aae6e4b236673bb3f80d7b9473b02efbc25880b7bd0727fcc1144ed",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:4595"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentCech.intersection_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9c9d9ff4a601c45bc3ce32f78effe9048efd07e2c2fac48da1145ee9bc1bac9f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:20759"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentLattices.above_shift",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "afde0e5f12029a215bcdace7ac752a3e3bbed82ac71aecbb354a7d45e5212c17",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:9803"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentLattices.band_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5b5d2f7520f0e7a7d89bdf9d498bca01eb523cdac42863703b2de4fd010bfd4e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:10128"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentLattices.below_shift",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c01ccea10c14f0a1453d722bb9c62127094cfb68efd95d1b19368bee7e330ff0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:9481"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentLattices.boundedAbove",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a54c1bb2c11089d484001e79a66a73399cc6d9ab90c91bf2597c78fc4f592231",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:8038"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentLattices.boundedBelow",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b59c71ecaac151ccad8457742dc5eff7adba78af10e14ace4c212223f3156993",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:7719"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentLattices.coeff_T_mul",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "107b1a9734c5988a9ee553b1476991f12dc6cb106b54504cb494e4c2f921b43c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:9296"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentLattices.finite_generators_bounded",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b4354ad72288d7b50ebb1f26cffeaeefe93253b61f3f33a6e5f36fd9be25e1e5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:11110"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_oAI",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "12ffe133dc97f8c0ef6cc01ee6b890df09f92fdd093076d22ed9e4b58dfbbb2a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:7361"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentLattices.intersection_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1d4f41e026a7675e6e510019c4999c4f4c40e75a4228d0edf37a41d616426553",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:12072"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentLattices.intersection_finite_general",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a75c121231d4dd49f462ceee640bbe254abf43effa1ba2001478a8c145099c83",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:15540"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0b0b18869eedc21c2cc41156552f52f6443e3e677710c5f41bf113f4d2663f1a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:13301"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentLattices.mem_boundedAbove",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ae4c03241005891ba302f76e7e8720896deab647c58673246798b06fa8a2a00d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:8884"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentLattices.mem_boundedBelow",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f4dc94cf76aaad15e666dae8ee77895cfaf625e8bc380765343673657ea2d6c0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:8472"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentLattices.quotient_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e0a21c90a0999fb4f60baa00c755561909f0656d32d30b3f5b3ac7021e891045",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:13876"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentLattices.range_intersection_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b224e4ef75476625d1519dd425a2fbefc4d2ced5a484610d281522e812feb641",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:18952"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentLattices.range_le_lattice",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "653858af706f942debc08ccadb07502827e388a07781f0780d242129e48425d3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:17995"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentLattices.torsion_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cd1018b17fc9adfc9727d85a3398fc69a965dbe09bfa2257866bb0223b154b90",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:14325"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentTails.negative_tail",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "57616818c87e277273059f0ecfbddd945b379c2426c7ea825c1f3fe13311c828",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:729"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentTails.positive_tail",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ef59cd13fc277569df9a7617fc9112f4aa6e42d825b3acaba36b14bc3c0d15a1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:317"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentTails.quotient_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3435dc8b36e79b16a49fe0366e07661b0b1cedbd474379ec31fa4301f1c15a2a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:1162"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleFrameCocycle.chartEquiv_toSections",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b0186b9ac6f1c4ba71059bd52139375a3b1f3c054fccf4361d144e3d58c7e2db",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle:3861"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleFrameCocycle.cocycle_ext",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoordinateFrameIdentification",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ed96ec5c63e806e98449214277f3babb469a3f81e7d575defa404eafb1947a09",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoordinateFrameIdentification",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoordinateFrameIdentification:346"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleFrameCocycle.coeff",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3ffc1217086aed12d15b06bb33addc9ad5fda879d1969d9ea0b45cb2a75dcd71",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle:768"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleFrameCocycle.coeff_change",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "926c5ef777d35ad3acd14dd83c9be5f2d8b6bd55195bdb5d8d8d194b4e408389",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle:1491"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleFrameCocycle.coeff_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7126bfb3e9f063f136bf26261fad6ae47b0031e41c05119ab24025647c70b12a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle:879"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleFrameCocycle.frame",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f43163cd8e75a60e5c2cac574388816fd40efe533e178b3f9343c6adec6935f8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle:682"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleFrameCocycle.isoOfCoordinateCoefficients",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoordinateFrameIdentification",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "23c3a48b1c5d64da5cf9a08409d84bb241c842a69075d4e40a8a9281405f5040",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoordinateFrameIdentification",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoordinateFrameIdentification:495"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_028.jsonl"
