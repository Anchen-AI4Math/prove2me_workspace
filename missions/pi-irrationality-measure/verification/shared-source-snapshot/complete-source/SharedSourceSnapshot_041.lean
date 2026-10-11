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
      sourceName := "OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4000fe54190285811e5cf18f1a555a0c7450ee5f25f9cbc7820d0dfc13d4e8e1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:27150",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:27150"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a6492a0837fd4eac30e1ba2bd80c8d65361ed50d3d657b0459980d880751d9ba",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:26884",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:26884"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleMayerVietoris.freeOpenFunctor",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fad84b33161f4fb9884c4cd519cac88efcb9c2c0a6687b4dab0e8d49e3f590f5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:50867",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:50867"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleMayerVietoris.freeOpen_isPushout",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b8cefa55acb602f6643a212a14dc8d81563629ffff439efc54b59ee1bcc05304",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:51021",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:51021"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleMayerVietoris.shortComplex",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6c8a9d39746bd608bd48c9f6b58dd10bebfe5fc4783788539eb0b99fabd54253",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:51662",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:51662"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleMayerVietoris.shortComplex_mono",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4f09a21cbc49dd960bc2e5131d2c97f8b4853bd4afdd7f792a3697ccde32b5ca",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:52162",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:52162"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleMayerVietoris.shortComplex_shortExact",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "19b4a55896ab76d82b239215b80beb2cc1064623bb0146a1f973c6a09232542a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:52419",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:52419"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleMayerVietoris.union_ext_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "03231c63c9d673aa16bfce74c069ff8eb20aa94159f419b73cef8faf2ecc6b19",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:52801",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:52801"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModulePresheaf.pushforwardCongr",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "33dcff42f2d6f557466de35d4c8d9eec2a8b24a57057e23bb280db0722270376",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:1829",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:1829"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModulePresheaf.pushforwardNatTrans",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e75fa90c847133475c381dcc18d5f47d65b24b10302031abd77996ba9214f3b1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:2355",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:2355"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModulePresheaf.pushforwardPushforwardAdj",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b4c39eb7e16646f2da13155c881fef87de6d95425f9c72bdb2cd9b4e50a138c5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:3479",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:3479"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleSheafExact.shortExact_map",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "36b0422604885ef69a8a4618886ae0770290e1558907c3bd796be5c0e946e932",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:31997",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:31997"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1c34bc088618113472de696906f541b155289dfd8ba2c829cfca0cafc4eb06cd",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:30871",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:30871"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dbf137dd72511ef42b52da42f0c994cd723e5655225dc5766eff55719d68bf30",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:31824",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:31824"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.OpenBaseChange.hom",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.OpenBaseChange",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d21d83c99b38329cd9c9f451a244d3daf845b2548d52eb4e641a3676450499a1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.OpenBaseChange:1445",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.OpenBaseChange:1445"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.OpenBaseChange.hom_app",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c2ce2cb30f14f41fb02bc8e1c4dd9c2270d198221466fe8632865629c037965b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange:3452",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange:3452"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.OpenBaseChange.hom_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.OpenBaseChange",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5aac6f37be81a102144b6b380ae46fce1e5e193cbf39f92c9f4392f9c87ab7c1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.OpenBaseChange:2036",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.OpenBaseChange:2036"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.OpenBaseChange.iso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.OpenBaseChange",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7e5fee3a4cc160eb126a7fedca7c3d5afd71bd1ec4136d13bd48e80226405e70",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.OpenBaseChange:2697",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.OpenBaseChange:2697"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.OpenBaseChange.leftSquare",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "067ab4637116f46d9840e91118847ba1831f3853a60580c02f74eb4e2aae94e3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange:439",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange:439"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.OpenBaseChange.naturality",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7e3eb7df556b705d183bb40a892b496478eb5ca4e6be6bca858a9e3868d84195",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange:7365",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange:7365"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.OpenBaseChange.naturality_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1727cf2be91c8a8ee138553320a8b04061cd7914452fbaa61d75d3e3de22b995",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange:7365",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange:7365"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.OpenBaseChange.restrict_unit_app",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.OpenBaseChange",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5fd6bb85dc6ff3cfa8c13fb96824da7f5b6f506f84de58942d4e596ff46396df",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.OpenBaseChange:284",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.OpenBaseChange:284"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.OpenBaseChange.restrict_unit_app_iso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.OpenBaseChange",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4f7088838715c95abe9a2797353c86ddea24b57c3d93e574f3f09871f51d11dc",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.OpenBaseChange:531",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.OpenBaseChange:531"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.OpenBaseChange.rightSquare",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.OpenBaseChange",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "978407671920e5a11b3ef796db1a17c68b84e2afe24375d03ed1e991b3851e2e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.OpenBaseChange:1084",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.OpenBaseChange:1084"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.OpenBaseChange.tensor_pure",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2897ca7396a3160d0e7ec821d80c7903f21eeabe14757cbc3fee61c96f921fc6",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange:4524",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange:4524"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.OpenBaseChange.tensor_square",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c03ceec53c81965c8a8c05ffc6cbbc98b209b16c4e3683bde634d88157e0f61b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange:5450",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange:5450"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.OpenBaseChange.unit_compatibility",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ab80428cb5ec590083b3892dcd3bd0ffdb6c6b8c9cb728b98c82a4fd233692f8",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange:918",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange:918"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PrincipalSequence.end_regular_of_mono",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PrincipalCartierSequence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3b214d29d68f287efc044bc71af11fe82e085686c9f3c7e6ce2e26a29d5c225e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PrincipalCartierSequence:493",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PrincipalCartierSequence:493"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PrincipalSequence.exact",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PrincipalCartierSequence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1fdff1f25881053194a6b6d6d548c2bbd1532a5b8b08a4941f0480b72512286e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PrincipalCartierSequence:935",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PrincipalCartierSequence:935"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.PrincipalSequence.scalarEnd_eq_multiply",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.PrincipalCartierSequence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c1e07828d54b46cc03dcff32d542202f3f46f130806e0ce6ac87105e3c1b2f4f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.PrincipalCartierSequence:400",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.PrincipalCartierSequence:400"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjBase.basicOpenToSpec_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0aa208a46d882e7e5aeafc672e3363b094a5dba33c565361137d2ece504d233c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:1145",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:1145"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjBase.basicOpenToSpec_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cfb731ea1bfc80cdf7be0fc03def74733ba5b195082230c10d3efda227e6598b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:1506",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:1506"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ProjBase.toSpecZero_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c44814b7a2e4476ccb87ae0c7ad5ee18dadc318c7f860000c673687f4b9dc0a4",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:2007",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesUniversalUniqueness:2007"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.ChartVariables",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "03b5a4a594dbdc697ca1e582ca3dbc2da620a8ebccd99ed7e21772d42f9a3a3b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:1175",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:1175"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.CoordinateAtlas",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "inductive",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c3ec0d7e6a6470183f411773c42d69b069c829717c56200a3a349644a2cd9efd",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.CoordinateAtlas.casesOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1a085443879a1d090b1423aefac6a6abb9ce2c8d0c4ef0857e68b43b3fcf2684",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.CoordinateAtlas.compatible",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a1546ca382683afd85455bb716431443aeb9fcb84d9b4009c804fc963e3ee8b2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:10538",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:10538"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.CoordinateAtlas.coordinateOverlap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ca484722d97d62b45a863deafefc8a02bd244aac753d26aebb4bf0b765659117",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.CoordinateAtlas.coordinates",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2fcdebe15ccb7c4d5cf0b9092c774370d2961f775a41e74634d220fbe69953bd",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.CoordinateAtlas.cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "40f289845036291b464f6fcc703008d2da5c4e7c4d8563ba3d7da459bc383b65",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.CoordinateAtlas.cover_morphism",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5f76c168f22b1acf597d9373f252aa9f4f21617fbb3dd653d3f82a5f28dde1f1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:11281",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:11281"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.CoordinateAtlas.cover_morphism_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "97560ec793ad3c50b11e99e71c79cb10d77644535f6fdec063fc5f8ad2f75710",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:11281",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:11281"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.CoordinateAtlas.index",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "657299de1b7363e30294539c2ce5236adeb61f47edfd53687874e6ff992df6a6",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.CoordinateAtlas.localMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "35edd56a019e325a95bdf8997c65837902a768dbf4808dffbf99b706581f7386",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:10347",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:10347"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.CoordinateAtlas.mk",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "ctor",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "64bdc8f1d85b18a807a22c99c6da8cc93a5355240bdc729623a98789881155dd",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.CoordinateAtlas.mk.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cd0602b6d6c26d0bb2e4b3d6d0164356ebcc78e830b78ff0768602bb8afc1305",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.CoordinateAtlas.morphism",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "98acd4d0585281abea377c87044e8c9abb9fb39d3c772aa43e2ea7904b2cbabe",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:11156",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:11156"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.CoordinateAtlas.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ee315122887e8e5de2a19de2db412da36634b69634de49a545a53c67727e4e33",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.CoordinateAtlas.normalized",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d85bb690eaedf26017149b874f6f41155a73a8ee61828d5b2de0fce8dfa0166c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.CoordinateAtlas.rec",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "rec",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "97f5ec9dca40281a1903db33e15824d9deea1973bb7e0c63d9a827096082782f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.CoordinateAtlas.recOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7d7cb5853104894925abdc66a1ad7a3a8e1e0a3a45e006162adc365183797e0a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.CoordinateAtlas.scalarOverlap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "30ad7d00a6a24a7f7a2829d714197eda4b9a94e260a377a00f8c6a8ee11b6656",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.CoordinateAtlas.scalars",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a98f09e09ed154c24d8022c19de016211ae8af76e0e166882483e37d79999e4b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:9516"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.PolyChart",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a6f0030b805ca1c839cf7a176dfcc69bed7aa06526ea7ecde82b67f409108533",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:1102",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:1102"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.PolyGrade",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "478388b9fdaa30f83c7d511952b9340f7c24dd4e6ae2f617c002f801f2191897",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:935",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:935"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.affine_evaluation_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2b91c89edf68fd8510a855218805b4bdbd1780087a7f3dc624da246496f487c3",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts:1140",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts:1140"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.affine_evaluation_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionReindex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "70997b472e7452b0ad2645a30b8bd7ff507c40559237cce750ad8a1bce585b58",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionReindex:4844",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionReindex:4844"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.appLE_restrict_comm",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c573df0980dc7e170641f2a7ce5663533e262a10b7ac6dddc84cb7c0b6fad082",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality:1235",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality:1235"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.atlasOfFramedSections",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ecd88f4b343b6ab985a5d98c702398dbead38086f7efc8771618dc1e35d2f2c1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:11714",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates:11714"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.awayToSection_pullback_open",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e245a8131af56e69d998446c4478421ef46da30e80e09ea1fc95aa4efb245ef0",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore:2651",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore:2651"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.awayToSection_pullback_top",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e5204c7b28256ea3fe4aa85aa5066d538db561d793567f0cbd59f734457d9d6c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore:1946",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore:1946"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.away_chart_appLE_top",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "368679a22a7952189ab9ce0d3cbd58b534f2427f0633cbcca61440e41274dc59",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore:736",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore:736"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.away_chart_preimage_self",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "253c4b885d69b1004db4fb28063f31c631975c9b7bb5026558235ebf53d999b0",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore:459",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore:459"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.boolChartUnique",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "42d92650312701b156a9d843f8864037a3176ff1ec43409ca87de9d9023e9f5b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts:5446",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts:5446"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.chartConstants",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "08204c2a834d414198d43a933c14135030d8e1fb74acc4f263beaaba53978138",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:1223",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:1223"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.chartCoordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "79efb580b74f95a5fa7fa2538a0c8677c1b87b0132665a594a7fbf92b347d115",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:1558",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:1558"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.chartFinitePolynomialRingEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartOverlaps",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "61ab2a74f0fabdf3577a95f84a5eb48e264e55ccc1f66f73942ed08643ef27a0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartOverlaps:4310",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartOverlaps:4310"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.chartFinitePolynomialRingEquiv_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d3b55be49025ffa9235e363b8f4ee70a7b7119d60d43da04bc917a7540f45cf2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore:6072",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore:6072"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.chartFinitePolynomialRingEquiv_restrict_poly",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1cf4622e0832ce6052f45d57731e01161bb607f7fe0398b2d585e959ce9d1841",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore:6532",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore:6532"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.chartFiniteSectionRingEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartOverlaps",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ff553c8e48d07f3f6d77e7f75c464cb1ef19b208e2e3cb4d276ac703369f4386",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartOverlaps:3131",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartOverlaps:3131"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.chartFiniteSectionRingEquiv_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "28ea11d7af923dc3bf92ac288450a62ca385739e8509ce84ffeffbacc6847c93",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore:4106",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore:4106"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.chartOpenAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "883b801a8856ffb1104bcf380ad0289a02ed959bc99d428483e95f1e58d8e5e8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore:2408",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore:2408"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.chartToPoly",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "edfdc4ef4e8f3a577c3ebf7e5de224e1c7d5aef5599232d0cf58162b5721a7a3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:1963",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:1963"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.chartToPoly_comp_polyToChart",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2e2436e8994447707e6670469e1934d33aaa11411b52361b5363301ab49d0cf2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:3106",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:3106"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.chartToPoly_constants",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "870ffd3d081fab2056276fffe4a3d979a43c2a883d52918e26ee56f3f5845c46",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:2706",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:2706"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.chartToPoly_coordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "21bd21c03da54a39ff26e28a3a488ecb674de93937c866017d918cdaaa218cef",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:2889",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:2889"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.chartToPoly_mk",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fa53a94b74671d7dd6f118189f00e4e19f1f4323a3a056737b9ca6506231191e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:2283",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:2283"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.chartVariableOverlapRingEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartOverlaps",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "10989422dda15bf3d97094c498ca57209234ac4c6c475933725d1222bd035099",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartOverlaps:5151",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartOverlaps:5151"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.chartVariableOverlapRingEquiv_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fd375bb7814197199d2b534f522013c3b50d519490b898f067b1a2a90d5bb914",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturality:1207",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturality:1207"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.chart_dehomogenize_val",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7c6b4e10e9ef5364b8a30edc5b5b703eddeb1b83b05c8ecba2297c4f47874d86",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:4348",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:4348"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.chart_val_constants",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6d204387b9da5349f1ec0d3698f828e3cf2a60b36c7cf3bf9f185570b3266f01",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:3833",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:3833"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.chart_val_coordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1524e5c5d5fa2d0f6571fa272e3748e71f24cf1b7c2ddae2650863b585239045",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:4079",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:4079"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.chart_val_mk",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fc7ec0d92afa83d43e2a5f472f04be573c6d933d2a9fa2b361d4e38b42abc7ed",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:3353",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts:3353"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coefficient_postcomp",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e18b03885b6897d09fc8b2f9c8fcc0112cfa9c8757dbd2c0bf0fb10ba2082865",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections:7438",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections:7438"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateChartMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateChartMap",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5c59db06f5c7d0083ad8805337233fe5fd10e4bb231df1ae55a4a37e6e860cba",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateChartMap:577",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateChartMap:577"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateChartMap_factor",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateChartMap",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b469940713d64c718571d024a4d9ff809d76b1d62bec52a07a1d2d8df0993928",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateChartMap:867",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateChartMap:867"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateChartMap_ratio",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateChartMap",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "13e1b11232856baaa210c5197073b63e258a221a2a936e05dbe9c666ac818496",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateChartMap:1185",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateChartMap:1185"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFiniteOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0cd3dbb6bb556d5c6532e54157180374d1a9fc490bebbae86af63a522e9b2fc9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections:1113",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections:1113"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFiniteOpen_eq_preimage",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "85629b12ea767ae892855b74a3fc32cab1e86a4b3479c8aac8bd000e9821e415",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections:1457",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections:1457"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFiniteRingEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "548d52cd148338a89010a3534132b2ed461d1baf4fc4ebd2b540f0608679dcf4",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections:2121",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections:2121"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFiniteRingEquiv_appLE",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0576b53da788d45a3fd91246f5cf8697c6913a034d77f67367b70b60900a2bfe",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality:4040",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality:4040"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFiniteRingEquiv_constant",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eb171c5f444462e58644a424c7344fc92b96fc4c5743337ad79a84c9f5c1b007",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues:1996",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues:1996"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFiniteRingEquiv_coordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "166d9a35d510ff449b728a8bed31b7480321543cd93c045b45c7cb103914a92d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues:1388",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues:1388"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFiniteRingEquiv_cross_ratio_full",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "71e2d537660a03938fdc976affcb2653057ab17aeda340f4c4c641d9d0e23add",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeTransitions:707",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeTransitions:707"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFiniteRingEquiv_ratio",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "64d17151b2e2473a244134a41bb823a22224f3a1515c49066975a2c41c020e8f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateTransitions:886",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateTransitions:886"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFiniteRingEquiv_ratio_full",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3f862452d0e4327a69660dae25c5b871f793bea349ff84c39c369163380fca6d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateTransitions:2151",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateTransitions:2151"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFiniteRingEquiv_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "290102b4daf9c8fc6409fc38e7df0fac9e5f9ce0f7d2eb6fd62f0da4bff3964a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality:4861",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality:4861"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFiniteRingEquiv_restrict_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0f16a49e63b0129743d5bc4ab35b9140d3ebd2859ccb142c4f200efa52eceef9",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues:824",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues:824"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFiniteRingEquiv_symm_X",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "68ead3bd7f5dc201e1f06c22c24616970e883fae8800308d3438899b4f58a9c2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues:3160",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues:3160"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFiniteRingEquiv_symm_constant",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3736dd29b7f0fa16a93514a25c2d021210290169eebccee0be33cb755aafa65e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues:2697",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues:2697"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFiniteTransition",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "93a4a45ef907be87a6b9fe9f918f54f2194b4a66a444527e4eb218b6fb145f90",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues:3874",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues:3874"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFiniteTransition_X",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "579a70b323e278a3e18588045af2260b3d2c0572a10c2058ed4c73a319961827",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateTransitions:1294",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateTransitions:1294"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFiniteTransition_X_full",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0568b3cb620308ec76ede112993c4de102c8a145036729654351aab93a0661dd",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateTransitions:2747",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateTransitions:2747"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFiniteTransition_constant",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "69f1a45cd96466aa9d4a63d62b41933c6921264c0bf31911c98998a00f0827e7",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues:4356",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues:4356"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFiniteTransition_full",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d2ef420d7f31c7665331595550a02fecdd8fa5ff069b4a853517b20155288b14",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateTransitions:4058",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateTransitions:4058"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFramedLaurentPresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1c905faab05b9c914f641a9f940d188d6622559a36ee403a455c1672197425c5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech:4382",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech:4382"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFramedOverlap",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fb6e0ab1d01f47ea7cb0f4486296026febe3957665c58088ba617b008bad6829",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech:1060",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech:1060"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFramedOverlap_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "507423267f357ecc922ae7ea6e6bb201fa69bf60b728637a51755ab69b3a951b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech:1339",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech:1339"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFramedOverlap_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a09f7a1f75075bdb965d5db41de8439ebc3e12fe8eba146dc37b2d1f6aacfd15",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech:1550",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech:1550"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFramedOverlap_smul",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0da4f64f39d4b9fbdd0c4823f5658bb9561ea4f0cec678f3b390316a8e98f25c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars:3914",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars:3914"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFramedOverlap_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3ff35e34abdd9e2096b0f0f443b0cda4118b01d9d74d67fce601dc7795b5cf8e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech:1876",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech:1876"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFramedTuple",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dd64bec3a6f6b1578efa0908ba4272c94bc57fa83f0677947a4bcdb804717be3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech:2250",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech:2250"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFramedTuple_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "420d06a52d80c9a12d1b71183b38973302261c80980e9270cb05e13741e92a5d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech:2633",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech:2633"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFramedTuple_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ea65032366a37a8c87e3a49c65e399215308193a054d8cf51c1ebb61f8b1a60a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech:2982",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech:2982"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFramedTuple_smul",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0445e83ac44dc2acacd4f8f2f746b36405f99b3acc22f2efc1945e274701a9f3",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars:4989",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars:4989"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateFramedTuple_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6a39048f59130595913a00bb8db6c622b3d833766a2baedaabe6f4a1ae9ccc07",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech:3655",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech:3655"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateLineBundlePullbackIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinatePullback",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3d1d752e59478755a70657d8dbbf340d0d596eac2fc61dbda98f8b2a5e636dca",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinatePullback:3036",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinatePullback:3036"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateNegativeFrameFactor_full",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9530589fb9aec0dce2804603c7c1f0c78eb605e53c69dd2d23585b5a97c3370b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeTransitions:1793",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeTransitions:1793"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinateNegativeLaurent_change",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "02c4ff194c992fd0872126ba7df84f7a03ae9108c33bb6991100ad5b1d18d362",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeTransitions:2435",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeTransitions:2435"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatePowerFrame_hom_change",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a01335fc53238d331b6e56b7a439c2bea4c7be058716064205e8558466a0a487",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios:3561",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios:3561"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatePowerFrame_hom_change_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e55d56a3dec46c86593340d31f6bea86d2a21f8abac26baaacf2313cce32484d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios:6183",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios:6183"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatePowerFrame_hom_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b6f70544629ea989c1b23a8c0d20c1543e599c7e31dcf4a07c0acf8cb56ee909",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios:4755",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios:4755"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatePowerOverlap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "252da5b6365eb18c767424cc481393d707919c39e354981165bb24b05be3c995",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections:2540",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections:2540"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatePowerOverlap_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c0343653f58355b9e49bb7c5273654daac7fabe76a9fee933bd852de268ecf8a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections:2976",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections:2976"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatePowerOverlap_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3f8e731c98ab95f4128751d047b000aa1858a7f93891ee170ac95cdc9ab29d10",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections:3191",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections:3191"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatePowerOverlap_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateOverlapNaturality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6d0f605950ce8030c093f6ded4faebe77b6044933521fbf09d0fdb1af8ee2d23",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateOverlapNaturality:798",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateOverlapNaturality:798"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatePowerOverlap_restrictVertex",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveVertexCompatibility",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0e8766d01ef0a72d864d08a72ad6c8da4cac954b1028b9f674f5cbc391b82b48",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveVertexCompatibility:930",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveVertexCompatibility:930"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Projective.coordinatePowerOverlap_surjective_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "02554aa70acb7cc914c5c1e36a746fe6d0274d5663aef8dca72dca95c06f5e63",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections:3539",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections:3539"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_041.jsonl"
