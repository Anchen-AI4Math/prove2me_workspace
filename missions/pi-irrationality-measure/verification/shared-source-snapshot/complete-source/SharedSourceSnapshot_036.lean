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
      sourceName := "OAI.PiExponentSeshadri.Frames.moduleSectionEquiv_scalar",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f8a5f476f0da1d4beb68eadf285596e9bd3dba9ce84816b7c7b1f4b494bac36d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameSections:4459",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameSections:4459"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.moduleSectionsTopEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "db41a21ff3f76d71aabf258486a9cdabbf3d0b742d619b3c76670bf5fabf2c5b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameSections:2245",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameSections:2245"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.openSectionEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4804379a5001acd714b0f238d589e7532b3e4f5045a2a1e67535e2ee407f4da5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameSections:3151",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameSections:3151"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.openSectionEquiv_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "649374095b3a3a906810e76ae110f7685e2dd7f5b65b052f78836a9dcf498d1d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameSections:3946",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameSections:3946"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.openSectionEquiv_restrict_value",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d69661d67e5f0c5125cfcc937623447c23ec5d55bbf7e1ac3704e252c96c7186",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameSections:5505",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameSections:5505"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.openSectionEquiv_scalar",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3a1eaf484eb07382d1b7f7b543c12ec16d6c8b0a4d6d2c4cdea6031f2ef9ba46",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameSections:4905",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameSections:4905"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.overlap_coefficients",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9902a40ad61e4504ceb02ed9f6c18feb2318ecbddf27f9e62c9c42c7e159dc66",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients:7514",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients:7514"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.preimage_isoOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4ed70d458728477a14a0333baa8924476b135365f167506a6e52f6af46b5a230",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens:7468",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens:7468"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.restrictFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "347c468ed9134c7ecbe340526081c5613fe9bec1396e007850fb87693771042f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients:1910",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients:1910"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.restrictOpenFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameSubopens",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "60c73a084d85f135cc99cceb4120fbc9f098bd861390463b9fdbe2439ee3efc0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameSubopens:242",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameSubopens:242"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.restrictOpenFrame_app",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameSubopensCoherence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "470aca0ed68625485e2faaf8e7a4905e08507a293605d010e7d7fe6473714803",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameSubopensCoherence:267",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameSubopensCoherence:267"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.restrictOpenFrame_coefficient_global",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameSubopens",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6d34e8c22a733aabb19af179d2606d137493384ca12baa97dd04cd5b7d4bb8bf",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameSubopens:568",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameSubopens:568"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.restrictOpenFrame_trans",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameSubopensCoherence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6cf9689ce9eda4c0d4b76b2c0b51bb791e5c7c6376f4491a6167bf0deb188e32",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameSubopensCoherence:1264",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameSubopensCoherence:1264"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.restrictSection",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a2e3ef31f06deeed33bf12ca511f5b6ee090aa3d2a00e6996181abcd644a6b03",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients:1698",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients:1698"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.restrictSection_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ab50d663236d6389cc123adaf8f1b9e97bf96041a6f56634295b9e404ddb5151",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients:4943",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients:4943"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.restrictSection_congr",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "85b902eeb2ca14b250a649416a1e44bca65104e181fc99a1861f27bfd5934474",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients:7083",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients:7083"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.restrictSection_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.IntegralLineSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a235891cad7f2eae1e5e99bb2d62b9387a90fbc9d7c68c585b8005a4686f280a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.IntegralLineSections:8002",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.IntegralLineSections:8002"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.restrictUnit_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "583e1d824b976b810538c8a12a86583cf9ae7df320d1a7b18bdc13e566cf7a26",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients:4061",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients:4061"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.scalarEnd",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c66da71f0cdda6008965f60885ace39486120976e77fd15e6fd56e3163a5e770",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameSections:290",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameSections:290"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Frames.section_value_natural",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "05f1a1cf83312fd190f118155f62965c5cf4da928cfe1adf3dd7fe65879a1c9c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameSections:3536",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameSections:3536"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.FreeOpenUnit.freeTopIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b3345e4d2b45aca4c36ef7605b08cfc543655927447e62c99ec9c0a62f275610",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:56903",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:56903"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.FreeOpenUnit.isoFromHomEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "85d46d36dcdbbde5ffb7602408559188e407856cd91109f678fed97bdc019a62",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:56374",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:56374"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.BaseSections.Sections",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1084b2ee144b1e06ca7c29c0da93935ae4dfbcc57dff1b77871a1696cb9a652b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts:299",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts:299"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.BaseSections.baseModule",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "973f949d8f5b6fa84b2c0d8981da0b923b3cbbb5695eedfa8b819c8fc2ee3178",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts:717",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts:717"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.BaseSections.chartMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cc22c166124a8cf2731927afd05e69c7ae22b4df04f78967c60b3c6374dfbb98",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts:8986",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts:8986"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.BaseSections.chartMap_range_coherent",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyPencil",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0acc86478a89c5ae7f9739c2b26a512b1e79248cf956f3f268e520be219912eb",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyPencil:2477",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyPencil:2477"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.BaseSections.chartMap_smul",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a554f1411ddfe663acb7c4a21ca261a836f4e5326f6dbc21dadf84d79fc4ec13",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts:9675",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts:9675"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.BaseSections.chartPolynomialMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "26a69a885fbc45a82571d68462db7390fb04678938eda8198b23903e45f01c84",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts:10884",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts:10884"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.BaseSections.chartPolynomialMap_localize",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "78b2466d81d72b7397245968a7ecbdb0582b283321938695b7098874d4d8701f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts:11709",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts:11709"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.BaseSections.chartTop",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9a38c0b27bcd4d0f9764e311c74fcc9ab09d4a7961f762e2c15291ec56fa4f0d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts:2849",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts:2849"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.BaseSections.chartTop_nested",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyPencil",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a984bbb1a260a06da4b674a72292d38bc32c817a8d9e70f5801d7cb2f1b92234",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyPencil:1278",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyPencil:1278"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.BaseSections.chart_image_top",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e059cbdbacfbd84ac473c644b49f8eb97d7479549eceec8d9a464ff3a1eabcc6",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts:2520",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts:2520"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.BaseSections.cohomologyZero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cb96928c248aaf6e2c41535d7aba5893cb49ba6f5e9b8669c9716a11091e7f01",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomology:7209",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomology:7209"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.BaseSections.congr",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0faff33d5062b5d720ce158de474d54c14eeb192823108f04e6557e91e9c00ae",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts:1116",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts:1116"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.BaseSections.congr_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyPencil",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ebdd8944c8ac48450a2fb31eec039b4998c5606a53705a7d26c21834f85bc2b8",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyPencil:358",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyPencil:358"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.BaseSections.eval_transport",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2bd8e7e4e6c565a247f35f0b0cbe410257bc9495eab505b5bb079848a59a8b65",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts:10361",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts:10361"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.BaseSections.finite_pencil_cokernel",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7dccc6095229fb9b15fc670261fe43c06e0f9fcdaea07e0427b87a3c4a029eaa",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomology:10011",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomology:10011"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.BaseSections.finite_pencil_intersection",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0e35445f7a08fa7c310da7c645120ac7c1c1e78d0d2c924c25d4f45d6737d60c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomology:2710",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomology:2710"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.BaseSections.globalIntersection",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c0e38cf7401d3fa0c1f2281e329f52987666f17991620f90d0e2d8edee002248",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomology:5906",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomology:5906"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.BaseSections.globalIntersection_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0bd97ce1d15a2438a2ba0e820e654d31ab86b65c24ba4040d7b1035b465a3c1d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomology:6416",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomology:6416"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.BaseSections.globalModule",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bcced9f1a65820746828491d840f720bf0d367a14b65ccfc635cef0d37625bbe",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts:542",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts:542"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.BaseSections.globalSectionsLinear",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a353da6737a7146b90f158cafba5b583827dac43330e4b08d19e01e57b035deb",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomology:6761",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomology:6761"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "16f950cff07d7d63b1bcb47b0dc755d855dc4bb9b92757128e0bfdbf6475216d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts:388",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts:388"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.BaseSections.nestedBase",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyPencil",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5a72f7cf2e9b069c3a8e365dd16752bb50af1962035371cc83ff2245d0d91de5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyPencil:1002",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyPencil:1002"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.BaseSections.nestedRestriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyPencil",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c5cc48033cb7882661bedc13402c9b54d91d93648408a5cc2cbc4b9df727ac2a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyPencil:715",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyPencil:715"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.BaseSections.polynomialModule",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3211b6aae028ab03f96fede4a7e136d3dc4c1114ca1e08d3c8902f4e5046be61",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts:4020",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts:4020"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.BaseSections.polynomialTower",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "38619e81bdf9e7b7c2adcb6675dafa4d2d5dd37f982107e72ac4fc9ad6636c9c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts:4243",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts:4243"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.BaseSections.polynomial_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "144215cb121f31b7beed78fe435bba3323633999fb3b9d6084d2ff461fb98c0a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts:6303",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts:6303"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.BaseSections.res",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "103437202a06caf4ae15c92ce0ea268adce2fd7fc5b3d2e59fe5433ab6855a0a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts:866",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts:866"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.BaseSections.res_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e78e31fe6b275bcca19956e5b4d608b08756f28c0bbad5396ddedff616f21410",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomology:5477",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomology:5477"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.BaseSections.restrictEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ac3aec06d708cd5cd43a43d09a5c9553dfb03613ef09f3f91e207bdb0017dbc6",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts:1796",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts:1796"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.BaseSections.twoBaseCohomologyOne",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b7c35a4d599d4ffe587b9dfc98b8f91a37d2d9287f37ddf5714b75c5a8906c30",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech:11148",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech:11148"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.BaseSections.twoBaseImage",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "529efd13cb356d8f56c1cb3e41c08b5489e540d485675363db13d349972102e0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech:10782",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech:10782"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.BaseSections.twoBaseIntersection",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "42d0c7863cc4a78ef3f4fdddea46914bb0f9b02dd50fccdd882d25432d99cd1f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomology:2459",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomology:2459"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.BaseSections.two_chart_cokernel_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "603c7386c31769015db448fa58420181c07b96d38765672c46c99ce2c88e74c0",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech:8053",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech:8053"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.BaseSections.two_chart_intersection_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "24e39e681d0cd22120c64609338f3a9e8730120ae5c2f607d78ae82350e3d551",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomology:405",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomology:405"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.GlobalSections",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7f2dafd128346910c0efd5304bad1fbb25ca7d1adf7e6bf74df1bc69d3823fee",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:1003",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:1003"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.InvertibleLocal.pullback_frame_equation",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalPowerSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dd7403382fbbb737cffdf7f8943bdc72eccd0373c50c46ad6cbc3b59f015a0fc",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalPowerSections:424",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalPowerSections:424"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.InvertiblePullbackIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4cdefe3140df754af7024787195bad088ccda838e3e6fd00837d8a8703f44c23",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:1023",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:1023"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.IsBlowup",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fc384de4181763c501857688a30cf12227d464cba01c024b1de1391d43d0491f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:1210",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:1210"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.IsBlowup.affine_section_cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupAffineSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2066065f7468d79eda2dc4e0220d507666152ad6460cf7ebe9638272ea4be45b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupAffineSections:475",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupAffineSections:475"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.IsBlowup.baseChangeSquare",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupUniversalBaseChange",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c37fb1b9c52bb077254a3e9a24230c47dbdcc79dc843736ede4c5461400dc1ae",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupUniversalBaseChange:3320",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupUniversalBaseChange:3320"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.IsBlowup.complementLift",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ad3370b5f4713a7e700b8a2800a51dd1edead87b9c343b24cfbc6df5465c27ab",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:4092",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:4092"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.IsBlowup.complementLift_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f6004718ab198bfa2e1430436c220f10173a8c887f312222b9ce19012ad04a8f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:4329",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:4329"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.IsBlowup.complementLift_comp_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1b0f770f2b24ef6d7923cc8842e944448bf4900a649efd13cd91549c5ee0b95f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:4329",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:4329"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.IsBlowup.complementLift_range",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5fcc1afd7437771141a1107d1e3bbdced8b26708b2c9a38bd6e132417c9065b5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:4836",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:4836"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.IsBlowup.eventual_ample_exceptional_twist",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupAmpleTwist",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "48b7accbef9d2d820de89b1ee9f8aaab89ae578bb5bc11a1ef122639f398aa3d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupAmpleTwist:824",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupAmpleTwist:824"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.IsBlowup.exists_ample_exceptional_power_gt_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupAmpleTwist",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bba231ffc560d60da47fa5ac69fe9aba49db952b87bea80f5eebcaffe19e068d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupAmpleTwist:2477",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupAmpleTwist:2477"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.IsBlowup.hom_ext",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupUniversalBaseChange",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e21030d3179a9c11091d26b4ad689bf4cb493054f0bd6d50fc42c072253d02c2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupUniversalBaseChange:293",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupUniversalBaseChange:293"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.IsBlowup.isIso_of_invertible",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupComplement",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "20c8477f21e6df45ff20c7da43978f132495b520e4a858783c2e412b8561532a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupComplement:780",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupComplement:780"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.IsBlowup.isIso_over_complement",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupComplement",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "38dd6de32c1825c60226970d0d6f2d12b24b9bd0a9d743d31a66de3c85b2ec8d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupComplement:1047",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupComplement:1047"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.IsBlowup.iso",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupUniversalBaseChange",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bdc1b7cf2ef8435828806f4ed7331f993f3dd9d307e188de9ec38443c9a87e43",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupUniversalBaseChange:2468",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupUniversalBaseChange:2468"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.IsBlowup.iso_hom_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupUniversalBaseChange",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b73aca7276adc28770c577455c11d619086be813c4445bec7948ebe4fb80b128",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupUniversalBaseChange:3020",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupUniversalBaseChange:3020"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.IsBlowup.iso_hom_comp_assoc",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupUniversalBaseChange",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5856096b1850e884a397af7c561d754e1c6220b09b3143897890b4988a793ec6",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupUniversalBaseChange:3020",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupUniversalBaseChange:3020"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.IsBlowup.morphismRestrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupUniversalBaseChange",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2c3856939a2903c4e9ed1442ee774892c68c2171362d493e27b46261e10aa976",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupUniversalBaseChange:4565",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupUniversalBaseChange:4565"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.IsBlowup.nonempty_of_support_ne_top",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "11a160566c1e4da9be300eaad1e3bb0abafa8e35202260674b64fbf2afb49052",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:5296",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral:5296"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.IsBlowup.open_baseChange",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupUniversalBaseChange",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0a238726d59018d8414fbea0b6e841903daec8ba8105dc384b61ec1e45f585d9",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupUniversalBaseChange:1499",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupUniversalBaseChange:1499"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.IsBlowup.postIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupUniversalBaseChange",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b8f4cb3537f1b3370e0003aab615ece8580517fd71cda334f70237d052f6b90f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupUniversalBaseChange:551",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupUniversalBaseChange:551"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.IsBlowup.preIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupUniversalBaseChange",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "90eca639f130c5ee2dd86c671a3487dd69a7388fe5ca1ed4d098e5ec86c9c836",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupUniversalBaseChange:4100",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupUniversalBaseChange:4100"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "inductive",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "919e2c45136bc380303be321d6ac9620ce2aa4201fce2e021d3a23c7d9a69c91",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:396",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:396"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.IsAmple",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7ed5bd396417ca33bb0b53a8f71a560a5315fa7fcb6875185d07347c9afbe37b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:1225",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:1225"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.IsAmple.of_pow",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.FinitePullbackAmple",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a0bd4f42e48c1fb284a2034930b55a23d157f12719bc1187f00caa4fb1a90317",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.FinitePullbackAmple:362",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.FinitePullbackAmple:362"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.IsAmple.pow",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.LineAmpleOperations",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "88984c156f27c7dd04a9fc830081251de359748eb7ec910a71b1ca222bd5425f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.LineAmpleOperations:1029",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.LineAmpleOperations:1029"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.IsAmple.pullback_closedImmersion",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dd0d532e8288eec46a9ca90e6d94c6814981ef3ea27d005e16e0861708f3d1f8",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleRestriction:2181",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleRestriction:2181"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.IsAmple.pullback_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.FinitePullbackAmple",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "85f4b5fcf516b9fc02e1c6a9e33593624b29c0646e5eb626ced168ea6a7798b7",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.FinitePullbackAmple:766",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.FinitePullbackAmple:766"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.IsAmple.tensor",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.LineAmpleOperations",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7a9ace0f6465e9b8bcbb951c14ee8d4ed21f62190715384df68af250133fe123",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.LineAmpleOperations:1711",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.LineAmpleOperations:1711"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.IsAmple.tensor_of_section_cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleGeneratedTensor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "96be458f022fefc388dd96e1dee375bc7b6d6418bdc679a43c995871213ab91a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleGeneratedTensor:502",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleGeneratedTensor:502"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.affine_openSections_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "804194e5250aab421da43460481e087421df5b0a82f5eef6429bf6ceb6b19b87",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:9331",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:9331"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.affine_sections_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5bcf48d9749805f2600be84a86c53ed2076aa4a2627e0abbb302710874bb8213",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:754",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:754"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.ample_common_degree_cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleCommonDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "77050910fccdef9aa84a06e1b0b7b10958db53391ced1f47b80a00fc69a2ed34",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleCommonDegree:1440",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleCommonDegree:1440"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.ample_framed_cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmplePositiveTwist",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cf066c5ee7f57d657e00c317d9935b0afca7083ce0fa9fdd12cc014721befa37",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmplePositiveTwist:484",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmplePositiveTwist:484"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.ample_of_affine_section_cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleFromCover",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aa9db343b1ac3e73a89c49b3719d3f59e172d040fbb145a6366e3a1885fac154",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleFromCover:2344",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleFromCover:2344"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.ample_projective_sections_noetherian",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NoetherianAmpleProjectiveSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3040be9b4cbcfa9f6deb3ca26336cf9e97566f980be2e07fd8abb2d460916841",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NoetherianAmpleProjectiveSections:4263",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NoetherianAmpleProjectiveSections:4263"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.casesOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "179c343e4e6a8452b3e36584ab4e0e0d575a83e91aed57836269f305b02d34ae",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:396",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:396"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.common_degree",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleCommonDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "28ed8f9d7459974746d7e2302854d15968d07d7fa1aa2658519507ab454dda44",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleCommonDegree:348",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleCommonDegree:348"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.divisible_mixed_extension",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MixedFrameExtension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "732313e07c5ab7d0f1dc6e76ec28cd7c4329f7c64419876b4f82d2e12c775548",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MixedFrameExtension:470",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MixedFrameExtension:470"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.dualSection",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleInverse",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a48d19b8e64aa650cc98e1415531c75d4a3f040f1e0cd78996e69eed1b4bc352",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleInverse:1855",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleInverse:1855"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.eventual_twist_affine_cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.RelativeAffineSectionAmple",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "56561a0bb06bbacf273400a5ec3ff8ea8d32fe17c837fb6ee0d881e3a1474467",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.RelativeAffineSectionAmple:421",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.RelativeAffineSectionAmple:421"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.exists_ample_twist",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmplePositiveTwist",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "96aab1804ab5a41d9243b50074e65b42f3fb83a48a16a8f1847538897165478a",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmplePositiveTwist:2400",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmplePositiveTwist:2400"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.finite_affine_frame_cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.FiniteAffineFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "30061d5b53cf3417ac3e7719ceb3874cacd150d718398021e450504d23c992ec",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.FiniteAffineFrames:229",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.FiniteAffineFrames:229"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.finite_cover_mixed_extension",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MixedSectionExtension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e432932e9a712745a5d6245ab8401b0734faa5d6cef524404888626cb4e979aa",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MixedSectionExtension:4061",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MixedSectionExtension:4061"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.finite_cover_power_extension",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PowerSectionExtension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9e0f785de62eb77f59aad7ca37b9a603160bcfb420df6fb807dd0f7c75266314",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PowerSectionExtension:5736",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PowerSectionExtension:5736"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.glue_dense_subopens",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PowerSectionExtension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "157bdf0e532ab83b71a69ea6c7bc5a67f23c15955bf97c40f83cc75df8a8ca0e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PowerSectionExtension:3418",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PowerSectionExtension:3418"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.inverse",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleInverse",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c1be6f93345a65407b07b88df66450ec77579872d5d2f95b2115a5af5cac5ef5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleInverse:1088",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleInverse:1088"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.inverseCocycle",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleInverse",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6531590c1819da6d7b30500de840658d496bec29e1b8ec3a60a2b02311f145de",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleInverse:908",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleInverse:908"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.inverseCover",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleInverse",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ea2a2464a1374c9758ddd56a785ec6f1c59b1de9efe076f1da38bbfd1df3a695",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleInverse:297",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleInverse:297"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.inverseCoverFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleInverse",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e42701e6940f81db4d9a627752bd4ee244e278a0c54da5a0f58e98885bc4c8b5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleInverse:531",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleInverse:531"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.inverseCover_covers",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleInverse",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1e0c8bb80fea275b63ad2b7f473e26db445b067d57d783b0144a4160c6763750",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleInverse:733",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleInverse:733"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.isAmple_of_fullSupport",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NilpotentAmpleDescent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e341c63775c83719e2589918135c1633ad6c06a8f38c385dfe37357d2d099310",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NilpotentAmpleDescent:1985",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NilpotentAmpleDescent:1985"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.isAmple_of_inverse_twist_section_cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleGeneratedTensor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "687434f75b169a4166e852015a993044ee915acb6e931a0532a8d0790963a7cc",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleGeneratedTensor:2775",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleGeneratedTensor:2775"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.locallyRankOne",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cb2fd43e8899440d106bd654d25196ad2efe21e89da3a7344ad93e1ef0ea83d9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:396",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:396"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.mem_inverseCover",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleInverse",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0a72da1f5660aa5f43db1762e71d3a8e5d18f7e7c725213fb177e4871835a1bd",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleInverse:399",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleInverse:399"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.mixed_extension",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MixedSectionExtension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a826f6f754b83f30981e6d4794c5402b172ca062d03889ffd413f8e8be4c247e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MixedSectionExtension:7062",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MixedSectionExtension:7062"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.mixed_frame_extension",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MixedFrameExtension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d29dd048530ee26485c2ed8ca2f7951b71a9d38ead4640bf400b3c94108bb85b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MixedFrameExtension:1927",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MixedFrameExtension:1927"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.mixed_section_open_extension",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.MixedSectionOpenExtension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "86e31fe0fca1e2745de76a2db21850c4bb696cc9f5b379b026be12d7ae2416c4",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.MixedSectionOpenExtension:404",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.MixedSectionOpenExtension:404"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.mk",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "ctor",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a66032054a3ddde5adfa5c61a06ed83732cbc2282fcb91641492d8f7dd75f9b3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:396",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:396"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.mk.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5181c5f8b3c1554acbf4d5a271d3294417370ee7e5bb839ea34a68abf7804bd1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:396",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:396"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.mono_section",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.IntegralLineSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "876ecbf6fddb44bd4b4b649ff8a85d591a0443d56d78fcaf8aabe7da1a3aba12",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.IntegralLineSections:6203",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.IntegralLineSections:6203"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b6248dc9583daddcfcbe6e64248d8eed163f105dda2fbc3127fe122754174a64",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:396",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:396"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.noZeroSMulDivisors",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.IntegralLineSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "107b6ea9b708b9cbb47cdd2b6fe61c64a3763eeeb0e8a2abea5192d6c4d19637",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.IntegralLineSections:4064",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.IntegralLineSections:4064"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.noetherian_power_extension",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.NoetherianPowerExtension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3faed23b698fadbd246cc39deaab7a0c561d54f95cf8b11afa802207bc75c645",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.NoetherianPowerExtension:470",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.NoetherianPowerExtension:470"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.noetherian_power_extension_ratio",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.NoetherianPowerExtension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bf1449efec666cbb48f74c550662d9f39b0fe9918db24e8d2882417f0cdcd3ad",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.NoetherianPowerExtension:3059",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.NoetherianPowerExtension:3059"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.pow",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5182671888c08c3fba36f9b3008e857b5a9f4db0d28d5482ae4d4aea77c3c580",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:9696",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor:9696"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.power_extension",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PowerSectionExtension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bf4fe9d66253bc76ce5ff2af3922efcd2c546b0de47d9437afd3740c83571511",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PowerSectionExtension:11042",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PowerSectionExtension:11042"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.power_extension_ratio",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleProjectiveSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eea28d91259d30b02c7b27a5da2bf7f1bb006c23deb093f839b5e92a541da4d7",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleProjectiveSections:716",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleProjectiveSections:716"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.power_section_embedding_noetherian",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NoetherianAmpleProjectiveSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8326eb802164baffc259486416c582ec2a5d6a9ec832cc512fa58c3f0a73bbc5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NoetherianAmpleProjectiveSections:466",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NoetherianAmpleProjectiveSections:466"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.pullback",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePullback",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "50425d69d34a170fad36ed8d4b921cc9ba34855d76b74b83e8d1c7d0d3696105",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePullback:1278",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePullback:1278"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c5a644511559f1da86b3a5c335883741441f2b91be33b11d6daf1210ac0787cc",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:441",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections:441"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_036.jsonl"
