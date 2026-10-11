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
      sourceName := "OAI.PiExponentSeshadri.InjectiveRange.range_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b0dabab50abf2b2590eff7dada7b508f031f839e1a20890e27de3c0f8763bd91",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:5505",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:5505"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InjectiveRange.surjective_of_torsion_cokernel",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f5da11cd2260d8b9485a48dbd7a522f9866cb64c7fd01d99689e4420018244d7",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:6492",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:6492"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.affine_frame",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PowerSectionExtension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1033427d9fd352b55a4194423717fe415fec4fc1bca48cb3090d1854a5d9586a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PowerSectionExtension:10468",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PowerSectionExtension:10468"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.affine_local_equation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4a3e57e49c343199faa711e2c7ef150673732d98d0e8f41d635d56adeeaaa24a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:5551",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:5551"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.frameOfLE",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PowerSectionExtension",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9e76783a108ba9791a6fb1ba63308e61a9946eb40cf3349cdee5406cd6fac6e0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PowerSectionExtension:10041",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PowerSectionExtension:10041"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.frame_ideal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ReesRelativeSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "33d598332c9969c40f7aa4bb2f7f49f0916b27b5a9984ff26d1cb5b1b9bfe785",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ReesRelativeSections:425",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ReesRelativeSections:425"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.image_eq_comap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e47cc023db500161100fef6ded40c994873c2297287ede68efc5300261fb0335",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:1867",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:1867"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.invertible_congr",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "740d5c958d7e9c0b63cdf70f5a24853dc1185ead9fd3b2ec49edf512be4211ca",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal:4443",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal:4443"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.invertible_iff_local_equations",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "78c47eb425387dcd32662fde6215b71c2b30ac340c8da087577e156a98cb5e23",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal:4111",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal:4111"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.invertible_of_cover",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "39166830b3bce38b5c58be442eb8941a5ce45d0f6ffb1efcf84e2e36cfcc0151",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal:5834",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal:5834"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.invertible_of_local_equations",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a9839054aa532561e6ed89e94403a7a5a6fb135a86dcb217476c85a34f282fe8",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:12312",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal:12312"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.invertible_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c5056d0abcef239c3df1b3b7b953c093314c1589bfe47d0b0d5270eb80d4d533",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:7471",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:7471"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.invertible_restrict_general",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7cd4a8ae7b4d9cfee6a44dbe17241062c73dc7179e7bd1cd1ce981b62baf62be",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal:5495",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal:5495"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.local_equation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2d00a855e3aeea5abc4cc68ace66f55c5c5b97dba14589b632805aa6b81e6739",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:4094",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:4094"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.local_equation_on_chart",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ba4fddd450551577d8e94f141a973c75b9dce670a8767ace59dd44eac46aaf33",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal:1756",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal:1756"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.local_equations",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2c276a07372a2c8a5c64e6513b514cdba87cf5473a3b2d038f724f8a6dc5d383",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal:3353",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal:3353"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.presents_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cb741d8da29f178858a3dece3e87dfcdf88c889e4d3058ff7b9fc6a591b7ed7d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:6855",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:6855"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.presents_restrict_general",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "30a20f9472cdc051a9d3fcd08845c3f1e213c88853f9e72353fb2c0a4fcf84f8",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal:4819",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal:4819"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.restrictLineBundle",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7dd30c7563ba137bb0e046bd078b982b238943ee87e3b227b17b73ec12cd47f5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:6145",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:6145"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "51a53ad27517bd2955b26c7d227d4e9ff6ef69c39bc85299f23f871382045d81",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:2523",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:2523"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4f302f9a8c81e619211e012ed05b0451c55f6a74a5b84b082583926128210814",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:2722",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:2722"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.restricted_image",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "71118f2837124136209da60cfda07882fd548a57c1bcb75d2214fdb73bd0aaf9",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:2957",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:2957"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.InvertibleLocal.restricted_image_on_chart",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4ab01fc73ce1e8e3023d09e559022c030ec3b118520210a2a3c1d61a05d157fe",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal:317",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal:317"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentCech.cokernel_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4c11152f5aae6e4b236673bb3f80d7b9473b02efbc25880b7bd0727fcc1144ed",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:4595",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:4595"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentCech.intersection_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9c9d9ff4a601c45bc3ce32f78effe9048efd07e2c2fac48da1145ee9bc1bac9f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:20759",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:20759"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentLattices.above_shift",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "afde0e5f12029a215bcdace7ac752a3e3bbed82ac71aecbb354a7d45e5212c17",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:9803",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:9803"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentLattices.band_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5b5d2f7520f0e7a7d89bdf9d498bca01eb523cdac42863703b2de4fd010bfd4e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:10128",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:10128"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentLattices.below_shift",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c01ccea10c14f0a1453d722bb9c62127094cfb68efd95d1b19368bee7e330ff0",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:9481",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:9481"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentLattices.boundedAbove",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a54c1bb2c11089d484001e79a66a73399cc6d9ab90c91bf2597c78fc4f592231",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:8038",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:8038"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentLattices.boundedBelow",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b59c71ecaac151ccad8457742dc5eff7adba78af10e14ace4c212223f3156993",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:7719",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:7719"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentLattices.coeff_T_mul",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "107b1a9734c5988a9ee553b1476991f12dc6cb106b54504cb494e4c2f921b43c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:9296",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:9296"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentLattices.finite_generators_bounded",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b4354ad72288d7b50ebb1f26cffeaeefe93253b61f3f33a6e5f36fd9be25e1e5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:11110",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:11110"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_oAI",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "12ffe133dc97f8c0ef6cc01ee6b890df09f92fdd093076d22ed9e4b58dfbbb2a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:7361",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:7361"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentLattices.intersection_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1d4f41e026a7675e6e510019c4999c4f4c40e75a4228d0edf37a41d616426553",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:12072",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:12072"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentLattices.intersection_finite_general",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a75c121231d4dd49f462ceee640bbe254abf43effa1ba2001478a8c145099c83",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:15540",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:15540"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0b0b18869eedc21c2cc41156552f52f6443e3e677710c5f41bf113f4d2663f1a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:13301",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:13301"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentLattices.mem_boundedAbove",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ae4c03241005891ba302f76e7e8720896deab647c58673246798b06fa8a2a00d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:8884",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:8884"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentLattices.mem_boundedBelow",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f4dc94cf76aaad15e666dae8ee77895cfaf625e8bc380765343673657ea2d6c0",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:8472",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:8472"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentLattices.quotient_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e0a21c90a0999fb4f60baa00c755561909f0656d32d30b3f5b3ac7021e891045",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:13876",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:13876"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentLattices.range_intersection_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b224e4ef75476625d1519dd425a2fbefc4d2ced5a484610d281522e812feb641",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:18952",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:18952"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentLattices.range_le_lattice",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "653858af706f942debc08ccadb07502827e388a07781f0780d242129e48425d3",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:17995",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:17995"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentLattices.torsion_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cd1018b17fc9adfc9727d85a3398fc69a965dbe09bfa2257866bb0223b154b90",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:14325",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:14325"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentTails.negative_tail",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "57616818c87e277273059f0ecfbddd945b379c2426c7ea825c1f3fe13311c828",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:729",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:729"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentTails.positive_tail",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ef59cd13fc277569df9a7617fc9112f4aa6e42d825b3acaba36b14bc3c0d15a1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:317",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:317"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LaurentTails.quotient_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3435dc8b36e79b16a49fe0366e07661b0b1cedbd474379ec31fa4301f1c15a2a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:1162",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent:1162"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleFrameCocycle.chartEquiv_toSections",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b0186b9ac6f1c4ba71059bd52139375a3b1f3c054fccf4361d144e3d58c7e2db",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle:3861",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle:3861"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleFrameCocycle.cocycle_ext",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoordinateFrameIdentification",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ed96ec5c63e806e98449214277f3babb469a3f81e7d575defa404eafb1947a09",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoordinateFrameIdentification:346",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoordinateFrameIdentification:346"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleFrameCocycle.coeff",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3ffc1217086aed12d15b06bb33addc9ad5fda879d1969d9ea0b45cb2a75dcd71",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle:768",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle:768"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleFrameCocycle.coeff_change",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "926c5ef777d35ad3acd14dd83c9be5f2d8b6bd55195bdb5d8d8d194b4e408389",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle:1491",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle:1491"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleFrameCocycle.coeff_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7126bfb3e9f063f136bf26261fad6ae47b0031e41c05119ab24025647c70b12a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle:879",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle:879"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleFrameCocycle.frame",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f43163cd8e75a60e5c2cac574388816fd40efe533e178b3f9343c6adec6935f8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle:682",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle:682"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleFrameCocycle.isoOfCoordinateCoefficients",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CoordinateFrameIdentification",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "23c3a48b1c5d64da5cf9a08409d84bb241c842a69075d4e40a8a9281405f5040",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CoordinateFrameIdentification:495",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CoordinateFrameIdentification:495"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleFrameCocycle.isoSheaf",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5075504ca94bef1347e306ae5ee76591b1d63cd9f01d31129802fa82e67019ff",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle:7332",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle:7332"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleFrameCocycle.ofFrames",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8bb5ea7a9653d7baea9f73a527f3626096882363ca590a599450c2d0369500e5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle:1786",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle:1786"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleFrameCocycle.presheafHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "07804a36c81bc7f19368762dc67486f45b83708253dc844b32bd88778daf06ce",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle:4716",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle:4716"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleFrameCocycle.restrict_presheafHom_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "221e25590a4d18e749bd674336b53dea885557ca5528c38794db35e4367f7c20",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle:6056",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle:6056"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleFrameCocycle.sheafification_presheafHom_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7ad9f400e1e11ca56500feb0e1937784ed643acb92284d9d7882eaf94cf07bcc",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle:6610",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle:6610"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleFrameCocycle.toSections",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2204eb39eb99d044ca7d3d3721f74ee869f672305f6af120f8b6473b7d9509ed",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle:3268",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle:3268"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleFrameCocycle.toSections_bijective",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "923b5a5573222a5d4b30d9414ff447a8804ed49716ede880ed355036104a2894",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle:4147",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle:4147"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleFrameCocycle.transition",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cc7281fda29b3d447b9c84eb75ae410c3bf13357b4513955c178d338eb4a894e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle:1296",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle:1296"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.Cocycle",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "inductive",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4ce83aa53d14c8b6d42924f8dff98042af52fbde79e3c5d1b32dc6bc8c83dc99",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:323",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:323"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.Cocycle.casesOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "30de84dde6d6afbfb8432b88a0f0e9c054121750b3282f5cc0d4e30f9e8e6438",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:323",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:323"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.Cocycle.cocycle",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "69b0d99e1d22405aabdd9571f1e513ccd83b91383a3e0d5c3f083877a9aeed18",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:323",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:323"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.Cocycle.identity",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6920553deaad2db98676b598af526619a9b5452b3db11e71ee56b169eb454f3d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:323",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:323"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.Cocycle.inverse",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f397d393211df946331cd8559cd18da33a24f18a5db10819315beedc5e67e053",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor:603",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor:603"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.Cocycle.mk",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "ctor",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c128790d3c41a5ceae3c9606061e5e5ffe098b763906190510a1ea6e2da62312",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:323",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:323"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.Cocycle.mk.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b1b89b78ef431290635294dfde1d5e7e4a2154e055ee2d05e6051b6d5439daf0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:323",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:323"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.Cocycle.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "feec5b3919ff152721a288d650c378a72a9c90686e7df63785403891e594b48a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:323",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:323"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.Cocycle.one",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6c5c3af12bb9b4eb13300715839f628d49474a0932991467f5e3359260c9c350",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor:438",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor:438"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.Cocycle.rec",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "rec",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7fedccf01004778b228e5a1070f5c18d8a7c6ef65c7553b23b49e5a7886f6104",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:323",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:323"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.Cocycle.recOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c229208ed7012ad65724a666f40fa0684798a0acc5626df6ea8605030630b97f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:323",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:323"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.Cocycle.restriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a88d0a1b9a0830e50f7b6d82570fc892ac2979a3e85ba64acadf059e840319c6",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:323",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:323"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.Cocycle.transition",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "58fef111c60ccef2c0f8871aba0260089dfed7cb9959e6f580bbb0d0abc242af",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:323",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:323"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.Family",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "53f935b0e3a680ecbfaed7afa83de1b6f973d071c3e1c77c9ab27cec7a1e4ff2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:1001",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:1001"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.LocalIndex",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ab1aeb6304ee708c67d6e11d72de9f1fa33aab0197b178d3d5a9cba4cdd5080a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:916",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:916"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.chartEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a7207abb5eaa606c0b0929006cb3237d1ff1103e1aaf9207a72c6af9b12f8c05",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:5637",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:5637"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.chartEquiv_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "850a8122e43a5e8eef976481e1b7147144db3e5445133169fee714f63b737139",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:6545",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:6545"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.chartPresheafFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "df2c8973d8459407aefcc60198c8d44e36ec906ff52e7d88e53a8be4f2ff091f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:7577",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:7577"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.cocycleTensorComparison",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensorIso",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a76d7da605db75eb460d4ffc5fc0e26c2c1506f0788094d210d2ae60f54eeea8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensorIso:1451",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensorIso:1451"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.cocycleUnit_restrict_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "25be5cc9377bf8e970065562961e048ef8fff009950dc16c974d64330b376b51",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor:3393",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor:3393"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.familyModule",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "58f1e1c88559240bd978bb33a07bc8c707621fe4d071c1121ceb59fab72daf44",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:1258",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:1258"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.fromChart",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c56ec9b06c00656a4ae7d2755afac02ca37a4d6d2fc27a58baa20428b15af428",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:4642",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:4642"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.globalSection",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluingSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "58b67ca65d1a126861190b9f7e728a6b981804d2b249febebeb2ff025e3a578b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluingSections:490",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluingSections:490"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.globalSection_app_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluingSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f1599d1fc6ce7adb863fdf3127f0d4a194fefc9eeed9044030322baa8a531f51",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluingSections:3546",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluingSections:3546"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.globalSection_coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluingSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "057a5d448ed6dc89744cfa886225adb1b457159545c4c2efeee9a72c21d2e06b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluingSections:4450",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluingSections:4450"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.inverseProduct",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a1845d2be64b853f03593fa22fd33be2afb23132373d62ff1881cb40f1ee3e87",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor:1129",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor:1129"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.inverseProductMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b0cd0663a5a2841f3334232ab9f4c2da4bf660d8d92b379e725984a1d7f67689",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor:1814",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor:1814"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.inverseProductMap_frame",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e4b755ea4d1cca707bc53c986fd401c966d32e9c89879d4429693c8053bdbdb4",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor:6114",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor:6114"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.inverseProductMap_restrict_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "43e439e53baf60831ebc4f64a163570a3fe1c1192c37176e63070f10b613783a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor:7755",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor:7755"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.lineBundle",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0875daed064d0927bc38f74f85cc9169d8a5c87d88b7f110890139a41a3b3740",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:8407",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:8407"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.localModule",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "117c23b7ac99129be4f330afe4128a4dd506eb70f444c9fd002125bbd744e76b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:1073",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:1073"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.openFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a9271270c293c5ffa11c4a32018043f329b611151853f24545364d4a2f8d907f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:7885",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:7885"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.openFrame_unit",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluingSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3a23dab0a3941ef160ad704d8edbe629a9bbc8dc72322c556d75cd8b64a921ee",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluingSections:1741",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluingSections:1741"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.openFrame_unit_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluingSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0cd52e821f8042329c346894631bcc5dddd9b98356b3a4b3f9ba2489c7bc2b79",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluingSections:3054",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluingSections:3054"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.openPresheafFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e89c9e9ae2aa893b65c69ed15df217f76eb9cf1ea08d08bcac1961e2b7ce643d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:7047",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:7047"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.presheaf",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "39945193115da6e62ed509c2ec65f0905b7a6dceea0fc921cabf798230c9b7b4",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:4136",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:4136"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ff008bc926711b468186a74fd23e60fd402b3375c5a1d6f44ac0beb349e2fab8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:3301",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:3301"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.restrictUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "585a1a08a3d5a726b2c2b13408d2c53e14af8d1a605a6b1a72cbc2166d69d8db",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:8810",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:8810"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.restrict_smul",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d5711433a9f3b61d7db3e332d10312b56a4ef70e748091e2125e393b2b21d734",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:3661",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:3661"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.sections",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "07c83313700ad9a5d62e8e98880bdaeb24da32525d8b1f71ce14693996cdf22f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:1471",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:1471"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.sheaf",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "faa384516d5c7f0d8f30eb6dffd523cf6d1a22da7abe401dbb4f706b0fbb13b5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:7776",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing:7776"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.sheafification_isIso_of_chart",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fb88cd433f66f357cb884735baa99981cb6a421e6b52a982381a7133f925a550",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor:8782",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor:8782"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.sheafification_unit_counit_map",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluingSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "472afcfb19c0f9105e16ff3d398ad060443a3c1c072a6a267ffd052e8eda4318",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluingSections:740",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.LineBundleGluingSections:740"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.tensorHom_restrict_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensorIso",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d5256e071d92900b4508ec972e63bebe2fa48f86c164cfe00a5ba2400e15f713",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensorIso:357",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensorIso:357"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.tensorInverseIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensorIso",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fc05fb5762c269bca820bfc47a768c3ad5a932a03c0e34c720ec870dd490bc59",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensorIso:2794",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensorIso:2794"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.trivialCoefficientMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "661f3e979b2fd6195448996fd0b87ca100ed3dc28dbf27d235df7ecee11e5ac5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor:2453",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor:2453"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.trivialCoefficientMap_frame",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b3a6bb78b064951cf46ed71ae12e558dd6ac203845d5dcbdf8259fc87f708b51",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor:4557",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor:4557"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.trivialCoefficientMap_restrict_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0f69999c33590bae7bf3ca80a5677aee11b8542095330cdecc42c793841e4301",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor:5097",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensor:5097"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineBundleGluing.trivialSheafIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensorIso",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ddbd49993e6bf71a592287333c3996ea202089e4f8fd3cc419d50a22fb9b3edd",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensorIso:2269",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CocycleTensorIso:2269"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineClosedUnit.epi",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LineClosedUnit",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "641397ee6e4bbb01a0d1b953923d49e0744bc6d70e827c7c5a5994d5fd15c3c3",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LineClosedUnit:2673",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LineClosedUnit:2673"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineClosedUnit.frame",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LineClosedUnit",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1eef08555b9af0c4e74b25ae4ceb4f41c9754b6c179b65d87eeea46ad96f9cca",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LineClosedUnit:683",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LineClosedUnit:683"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineClosedUnit.framed_map",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LineClosedUnit",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "382eab93030aaa0746a1ce917dafebb180851d0f679a750445e1efb60f5ab736",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LineClosedUnit:1193",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LineClosedUnit:1193"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.LineClosedUnit.map",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LineClosedUnit",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7da85a8e7ae07199939648706de26574ea379524c0717c13743b454c9fc39fdb",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LineClosedUnit:485",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LineClosedUnit:485"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleFlasque.freeMap_mono",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e0df1a07ede1efe21327f8622fcb625490c68286e8ab7fc3a737c82dd83e70b1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:27913",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:27913"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleFlasque.freeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "edc130e2dd23d27993c4413f7099da152be645ef6951a49300dde44104644d75",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:27543",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:27543"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleFlasque.freeOpenEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c8138b0e61a1bca9d6060055a4a292974cc5fb5c7e3776ea8f4bf7317e88fd8a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:28443",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:28443"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleFlasque.freeOpenEquiv_naturality",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8ca03bca23c0c75a84258a70cd99bd2f9fc971a4fb8fd5bd82aadeedaeed4beb",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:29268",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:29268"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleFlasque.freeOpenMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "37463e021b64efe86b3c7137301e99fe511b5e29c9e1241fa6383e409fa18fe6",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:27714",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:27714"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleFlasque.freeOpenMap_mono",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "96f9a4f30c55bcf79740594204790e4c84dbf768ead236aaf1009473da14c14f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:28272",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:28272"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleFlasque.freeYoneda_naturality",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6a12d509a6820aa7ea283253be421e6ca420ca14cfa2d7c59146e5f2243c838e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:28661",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:28661"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a3ac774f397c86b828ee53213f2469f2f8fd01ba996048284d8eae05aa7bbeef",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:30235",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:30235"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleFlasque.restriction_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9488889fbb732c673eacb1cdd133afa9fbe91207f6355745c54d6aed741c99b5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:29832",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:29832"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleGrothendieck.enoughInjectives",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5da0db3fc6bf93c25d6c44d55240e6c4235666da4154a73dd19e56b6950e740c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:27237",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:27237"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleGrothendieck.freeSheafSeparating",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d129ef989e6b7b09df67558f938b1e0ac801c3061616ceca0807dae2e03e960e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:26182",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:26182"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9e752be90f64f70c840b6770e5786c33d179d7ce07b69e999e210e4a7512a9fa",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:25426",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:25426"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d5c11a2b0a76391c2ba2499d1743921e9d08bbbec7f1969beeb52bc1597a8480",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:25817",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:25817"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "85ac0b1a9781c14829d06915e1d842aa4f8ab9b393d2562641fff75fd0812e5c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:25596",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:25596"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ae26632efb60f3654db8fea98875080b7e20d91de6bb4c0761657bbff6bcaa97",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:26017",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:26017"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_040.jsonl"
