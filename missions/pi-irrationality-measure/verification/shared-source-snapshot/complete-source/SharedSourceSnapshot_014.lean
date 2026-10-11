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
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveTupleCharts.tupleVariables",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "965b21e6f2cb698305e1dd9776094e26ec4a8a3ca71512031699e3b7ba8d2da5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts:417",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts:417"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveTupleCharts.tupleVariables_inf",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c6bd5e08d72f88fe6a09287532f7ab9be55dc83b2e420bd426ffca8124c25d55",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts:1851",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts:1851"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveTupleCharts.tupleVariables_support",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "755486a81592bf26d0992d3abf13b62a328cbf805c5261d287d05414b189bde3",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts:834",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts:834"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.PushforwardOpenSections.comparison",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f23b67bd08dc6614bc8ff69c560676e08eb692dcd57ed4120fe0be5bff79d61e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison:2478",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison:2478"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.PushforwardOpenSections.intersection_preimage",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "65e4440a3c0667c7417322b8577512fb737c74761106ed4bc147ca8968836a5d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison:591",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison:591"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.PushforwardOpenSections.restrictEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c71639548f1929001afd79a61329f48411bb427f73692172c2e17ed82c226b8e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections:3242",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections:3242"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.PushforwardOpenSections.sectionMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1238311b2916d30d428c9aac25f758cf27515c4dc9d871880c7103ade2cd70e9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections:649",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections:649"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.PushforwardOpenSections.sectionMap_bijective",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c93203a15c85341c0cca0df3ba8dda7706a64145b39c7b7d5ed4e6f3e38e8374",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections:1557",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections:1557"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.PushforwardOpenSections.sectionMap_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6301495a39bc53a8ec87d1fb60c012f17808b07e94722e22b7cd77f99421463c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections:1794",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections:1794"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.PushforwardOpenSections.sectionMap_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b84d7e5dfb9bbfd55b85b8676c00f42a2cb64cfe74b1650bdd64808cd86ce0d6",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections:2031",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections:2031"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.PushforwardOpenSections.sectionMap_value",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4d1a70cee00c0e379bc57ff19dfa3b61bed06417596f750ea274a5e6e4df774c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections:1337",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections:1337"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.PushforwardOpenSections.tupleSectionMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "87607322395cd3e7ff5ee0156f5ac55455c66e3e040958d2344ba90dfc4bf51a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison:784",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison:784"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.PushforwardOpenSections.tupleSectionMap_bijective",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3515e88c220944935b446bb258e38c46081ee87dd166edb61398b96767ff5570",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison:1146",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison:1146"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.PushforwardOpenSections.tupleSectionMap_face",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ad1527327fa8a2518e4c1d892fa1356699a67b2d3595abf109c8f056ac0d4e72",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison:1838",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison:1838"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.PushforwardOpenSections.tupleSectionMap_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b561321a48ca6bdfb9341ba9978f1340acecaa16f60b7ace112200c7c9a09728",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison:1492",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison:1492"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerreAssembly.eventual_twist_ext_zero_of_generation_and_standard_acyclicity",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SerreAssembly",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fef0de6fae14f46d4b34685dc3b9380f0b5d7b8a08c1e6a0c7b62ad551faf10c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SerreAssembly:706",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SerreAssembly:706"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerreAssembly.eventual_twist_ext_zero_of_section_cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SerreAssembly",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8765bc910f6e36ce3b54dde1bd9e42dc6a6f9fb2f5c5ca7354aefc5c54be03a5",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SerreAssembly:2556",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SerreAssembly:2556"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerreAssembly.instHasExtModules_oAI",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SerreAssembly",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ec761ab49bd14e3245ce3b8112a6a31ceae6dbdb51efe4e140525336ca4c6e9d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SerreAssembly:644",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SerreAssembly:644"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerreDimensionShift.AcyclicPresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      graphKind := "inductive",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ea80a2d8a785b2c164058f5087801731ccca2167f959d1b371ce3007a3793e68",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerreDimensionShift.AcyclicPresentation.acyclic",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e1d329681b687d41e3671f9425111c73f674a016c19833c54396a6064aa4d13a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerreDimensionShift.AcyclicPresentation.casesOn",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "289fc983b94040b880fb4793ed01bcd36e7c580dc90b04dc6d5f489357301d42",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerreDimensionShift.AcyclicPresentation.comp_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1747f2d2f18a8a2636852fbd6191b012d34d4804a6895579f17ed26c8923d98c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerreDimensionShift.AcyclicPresentation.kernel",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b83e0f1f3ee9343e679efdb10465b99b90ad7a1fe0dc6965ac8fa57468d4b700",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerreDimensionShift.AcyclicPresentation.left",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "67fe282ce8c134c46084661e5f46f0f050a1d5573f6ef370ae2fb1fa7239d1cc",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerreDimensionShift.AcyclicPresentation.middle",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "56ec23161677afbd25602fd0c59956bb7938285f68305c08b9ebc73596946bb2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerreDimensionShift.AcyclicPresentation.mk",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      graphKind := "ctor",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d685a3c868a644d3658504db67fcdcd3d63273888414a4c4e400781b49c1f047",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerreDimensionShift.AcyclicPresentation.mk.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9a9ed593a9e9bc2ca94515d484c63f73fd3b385218625803d2f00fc510f08e50",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerreDimensionShift.AcyclicPresentation.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e41b40daf9babc3d75f18fc18dc84f1cc8159431bf78e6e4ccd18357f05a44af",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerreDimensionShift.AcyclicPresentation.rec",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      graphKind := "rec",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "beffe2c6710a75b7ceb7adb32e910712c0d55ecc159fba8917298f6a72cfbcc9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerreDimensionShift.AcyclicPresentation.recOn",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7f529840d0263f41804d828013f4ea391c743ec8bc9109b79d7cb885a5147fb5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerreDimensionShift.AcyclicPresentation.right",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "268df7da4dbc710269f2f5f20a1a5a96bf4cf527c1df5a83c591efb63a49de82",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerreDimensionShift.AcyclicPresentation.shift",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "53c0b5f6658fa6de3d3b55fae85c6c8021eea5d0dfdec541e525e116d8700876",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerreDimensionShift.AcyclicPresentation.shortExact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0e17ce9c8a279b5b7c09486c1734a6be160cea052a83010cb2a0dfd6b0b69e8f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerreDimensionShift.eventual_all_positive_ext_zero_of_presentations",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "73c9692f2093da70a78bcf179c1544047a57a0eb9ac8a938dbcab93821a21870",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:2567",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:2567"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerreDimensionShift.eventual_ext_zero_of_presentations",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f36aa378bd39c56b4b5a765005a8ff67e99f17d9e65f977fe89fb852c130c703",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1483",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1483"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerreDimensionShift.ext_eq_zero_of_biproduct",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "17416d907201b8a54b0889b6e4540b959e6918d6dc50ea9c60cd036650ab72fa",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:684",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:684"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerreDimensionShift.ext_eq_zero_of_shortExact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6d80f761830d7c1f77b6730dbc61f160bec13be35d59b51a19936f79a89150ac",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:310",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:310"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerrePowerDescent.eventual_twist_ext_zero_of_lineIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SerrePowerDescent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1dc4ea1aba76941326df2e71b2e0cef0205f595c8f5b80bb376c00b6de16ffd6",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SerrePowerDescent:1076",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SerrePowerDescent:1076"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerrePowerDescent.eventual_twist_ext_zero_of_power",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SerrePowerDescent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0b9177943fb19dfdea0eecaf2a0a192679e3293c9efdb484336deae26a67f84c",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SerrePowerDescent:1974",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SerrePowerDescent:1974"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerrePowerDescent.ext_zero_of_iso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SerrePowerDescent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c598c7175d3a3fbf0f2f6096af4251303b4c735f8f8e2cdc8f33696b7ba02605",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SerrePowerDescent:427",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SerrePowerDescent:427"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerrePowerDescent.moduleTwistLineIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SerrePowerDescent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "787610dc988252cecde18a11edc031fa3832bb69547076664f9cd91600cb369a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SerrePowerDescent:821",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SerrePowerDescent:821"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerrePowerDescent.residueTwistIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SerrePowerDescent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a5a9430165c773e63f8ec23f58b812a97a1bb2385f09622e216f9bb596d6139b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SerrePowerDescent:1610",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SerrePowerDescent:1610"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerreSectionLifting.globalSections_surjective_of_h1_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SerreSectionLifting",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "09c83789e4269e605d4a0dac332ae2a5bb09b020502ac0e2ac0ba41fc6992ac4",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SerreSectionLifting:347",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SerreSectionLifting:347"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.TwistPresentations.acyclicPresentationOfGenerators",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "520f3a38e39770e89adf3e423e73f159795da302b98a7bf888cd68b12ca1a16d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations:4919",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations:4919"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.TwistPresentations.coherentTwistFamily",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a10066bb731ad5edbcb887ce55f02e5797b94cd8af97fdd1bcabd4aef6360e57",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations:4757",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations:4757"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.TwistPresentations.presentationKernel",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "67d829456341f0ee815e4eead695a847bcd2802b574aac436665d30873319cdc",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations:1370",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations:1370"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.TwistPresentations.presentationKernel_isFinitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d07934c580232368c5ec33fb429658df70197c5f61c3fd9878847b8eb89cf14e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations:3313",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations:3313"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.TwistPresentations.presentationLeft",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fe55965af8cd5903e3f26f456085878ebf6bb0094addf52aa8458e80c864a075",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations:1555",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations:1555"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.TwistPresentations.presentationMiddle",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5642b80b9edb0f69e7a8b77a9df16c78b308e6ea2ec25271115a4b41e40fc67b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations:1443",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations:1443"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.TwistPresentations.presentationMiddle_ext_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2ab51753370460ae18668de858fbeb123cc027ead49b6d9d650353d33ace8821",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations:3858",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations:3858"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.TwistPresentations.presentationRight",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3f68eceb815447321b9948e39e42a1ca0c02f61d63888ccc256e37ee1cd2ab02",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations:1748",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations:1748"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.TwistPresentations.presentation_comp_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3d48d6d5769e43431f8b6b0cd35dbe3e7026b4614f8eacfc38ba6a0bc31f6dfc",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations:1928",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations:1928"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.TwistPresentations.presentation_shortExact",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0c6047b165905bf32b33823d26af018208c4e37c6377c72ad0b259f29c59bff6",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations:2182",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations:2182"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.TwistPresentations.twistFreeIsoBiproduct",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6e8e293e7cf524fc3e45ec5556498280b9a7a76f48e85343d919be095b9b6b71",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations:740",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations:740"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.TwistPresentations.twistShiftIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c6ce7c839120ff69ec6e147d934657ec51c4eeb9dfcc3f641b15a4f37e21f9ab",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations:502",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations:502"
    },
    {
      sourceName := "OAI.PiExponent.GlobalPolynomialCoefficientLaw.CoefficientLaw",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GlobalPolynomialCoefficientLaw",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2f2042962ac2ad0aef1aa82fd85b623f488df955b9f830f7ef0039b8e423925f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GlobalPolynomialCoefficientLaw:427",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GlobalPolynomialCoefficientLaw:427"
    },
    {
      sourceName := "OAI.PiExponent.GlobalPolynomialCoefficientLaw.coordinate_law",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GlobalPolynomialCoefficientLaw",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b9b60aee8a780b8dc2d75a673d9e6f82afbd402f9281a582d79fb24ae6f39f80",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GlobalPolynomialCoefficientLaw:721",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GlobalPolynomialCoefficientLaw:721"
    },
    {
      sourceName := "OAI.PiExponent.GlobalPolynomialCoefficientLaw.exists_power_frame_of_law",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GlobalPolynomialCoefficientLaw",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "46e9585756f2dc4b77af36bffe7772a9c0b131cbeaf1f56381a0908557e60122",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GlobalPolynomialCoefficientLaw:1374",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GlobalPolynomialCoefficientLaw:1374"
    },
    {
      sourceName := "OAI.PiExponent.GlobalPolynomialWeightedBound.coefficient_bound",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GlobalPolynomialWeightedBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d97f99beee36e1c30617d90d56b3318f78ea8c09ebd9d4b88d79a703f6dd45bb",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GlobalPolynomialWeightedBound:560",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GlobalPolynomialWeightedBound:560"
    },
    {
      sourceName := "OAI.PiExponent.GlobalReesRecoveryComparison.affineChartNoetherian",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalReesRecoveryComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9e58efc723a876c0ae7a84edef031188fed5fb4c291a989665cc031ac116204f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalReesRecoveryComparison:1718",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalReesRecoveryComparison:1718"
    },
    {
      sourceName := "OAI.PiExponent.GlobalReesRecoveryComparison.affineProjection_quasiCompact",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalReesRecoveryComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "773c0b8d11b463fb6f555aecd38f3cc1d40ac3898555d767541bed39e104e9c1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalReesRecoveryComparison:2000",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalReesRecoveryComparison:2000"
    },
    {
      sourceName := "OAI.PiExponent.GlobalReesRecoveryComparison.comap_app_bijective_iff_affine",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalReesRecoveryComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "beadcd126abcd095b8088e0a1dfa6b45be1c75eba49e2617696676c160922179",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalReesRecoveryComparison:3347",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalReesRecoveryComparison:3347"
    },
    {
      sourceName := "OAI.PiExponent.GlobalReesRecoveryComparison.comap_app_bijective_iff_affine_raw",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalReesRecoveryComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e6414ecffba3a91af9bc4374564bfc28eede73046933a9538fa7c29ca2b71c94",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalReesRecoveryComparison:2279",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalReesRecoveryComparison:2279"
    },
    {
      sourceName := "OAI.PiExponent.GlobalReesRecoveryComparison.eventually_ordinaryMap_app_bijective",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalReesCanonicalRecovery",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fbc1c4ba8d54f42d885be68fbac8b24587753087c33b79dec714999c2890da49",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalReesCanonicalRecovery:383",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalReesCanonicalRecovery:383"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.OpenSections",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "62ab9c2d43280c0690f2f2a438b18030cd91460227c81c697de1f18d9b78f939",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:667",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:667"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.affineOpenPrincipalEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2cdd5ab9292c93c364d95f2e5f4056f7b6d6ba91ae995b74e6b366bae2a03f36",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:13967",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:13967"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.affineOpenPrincipalEquiv_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6b9b443183ee3c043579a72adbea61e2d8bf51c60f7d4af72bfd488721d1d7f8",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:14701",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:14701"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.affineOpenTopEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c1bd7cf37c8ed9d8203c3d9935f508ba8736cc4c6aee4505fc55af29b3e56de0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:14402",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:14402"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.affineSpecSections",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e64d8167fe9d4bf5c68af65a4b7bdd94548016a82d31562eabf509875a654427",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:2906",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:2906"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.affineToSpecModule",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8c175b95a604369e59eaadcae23b20f1935b046968aa5f051d6ebba5dacdb59d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:2266",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:2266"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.affineToSpecModule_quasicoherent",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "04dcff47d8c2c1deec2b4c2b5dda452bcf37354334ff5d639b211f4e9d51cd8e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:2376",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:2376"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.affine_basicOpen_denominators",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9ad22136100e58e17e6e472d00f3027559f8a6632809a0997396b91f316118ce",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:5782",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:5782"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.affine_basicOpen_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5a352104607c6559ae22c6e7689ed55a85e2a6f0a6abbe3ecb7207ca89fa3aab",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:8736",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:8736"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.affine_immersion_zero_on",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ab149596e536a3a2c61e3841b3e536b575b1e990f3affbfc94348740b5057bfa",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:9900",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:9900"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.affine_openRestriction_localize",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4c488ded6012c4a9096fa5f79dda8a1c3793ad945bb2b99387e1c6a8107cdb2c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:4660",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:4660"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.affine_open_section_extends",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bce1af34a5fe46a24d09202e2047b09b3b33e50691373ae1ec0ff6b439082662",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:15292",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:15292"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.affine_sections_localize",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "acaa1bb01e9502bbe8abf78f52ed9d6202f9d077f7e24557232a55e9276519cd",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:2564",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:2564"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.clear_finite_overlap_discrepancies",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "466ec716381eb3e62864088921d257a7b56a5bf8d2a29d9cb50db8e0cd0ef02d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:18104",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:18104"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.compact_open_section_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d972a4b58a42160c1cd9a84cd98c6b1b344f96f979abb7e4b3323f59ff2e64c5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:11554",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:11554"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.finite_affine_local_extensions",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c7de36c5e4475a415a7445ada6fe73adbed79faaec7154c73543eb6c36108716",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:21350",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:21350"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.finite_cover_power_gluing",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "35bbd64d9414cd3716cacc0a09827bc1847b6fd2c3e13fd672c33c8318282170",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:20344",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:20344"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.global_section_extends",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4a936b57bf0d7a84f8ade46c86d443023bb81db308351074d1022e0795939845",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:22175",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:22175"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.global_section_extends_native",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "71fc8c00babe3dd8d9105383c0f1db3b6c0d8d2fb89f3178b0d87d8e01457650",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:23218",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:23218"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.instAddCommGroupCarrierOpenSections",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "81f1275cdf0c8bd8c6a306e31850319e2b6ef3a1da31d851bf521d171c7ae398",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:726",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:726"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopCarrierOpenSections",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c61fab96a45d2f6b4dd9e54730d697529aa717b03dde1b4c4b798dd5c5bbf055",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:845",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:845"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.openRestriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a8d758ac7135a0d2375e4e7554ac07b3fa74023b53c969b1c7ae2172783a94df",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:975",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:975"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.openRestriction_comp_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "897c023daf57146f25dda8aeabcc7fe10fb682fec2564dba260ea10f10c5cb36",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:9294",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:9294"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.openRestriction_zero_congr",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9fb12e2f36287dad2b244a0feea50baa3ac93567d64d24312da842687bd2385d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:9665",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:9665"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.openSectionsCongr",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5be1b6b0cb27420a2763d50c39ee765ad9ae56cb6869340dd6d03c3ac2f4697b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:4217",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:4217"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.openSectionsCongr_naturality",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "11d42d726f27aa4c38fa8c67f6d093912130b04f406616a94d7901c2aa1a3710",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:13397",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:13397"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.openSectionsCongr_restriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1a89e3a16f99242d09496a7f49c011390dc9e937d76324eea55a125c5ab1a061",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:4392",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:4392"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.overlapDifference",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "de9c79f15eb63ac3d232974f88f158d8deb98f66c5bc5c2e8f31978637db09b3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:16330",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:16330"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.overlapDifference_restrict_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b70cd665c942e71a6ccffe49c80cbf0cd6cfdf26e18ef3e7cd00bc81dc9a950b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:16538",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:16538"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.overlapDifference_smul_zero_iff",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "41932d303244911d1e0e0524ef847bc02b607b9d55ef2bcba15ab2cb81a106e7",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:17676",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:17676"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.principal_open_image",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f5e221659c59bc0b697a3710dc5fcc056a175bf259d1e9993ae29fd0bb6d6211",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:13704",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:13704"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.quasicoherent_pushforward_iso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4ebfcc6ad7adf4ca476945c66430878723c8e9a74ece50c2c6cdb8f6640815b0",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:1555",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:1555"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.restrictScalar",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "014733666f87d6f3257cdadc469ab5c282441190e7160a93b7af74ee647bd6c9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:245",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:245"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.restrictScalar_appIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cb7869bd6e13b9fbce13f8cdf6340ae5095dcc1a758f8f12123aa28fd64f447e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:6945",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:6945"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.restrictScalar_naturality",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b19da7b5505c10b5327cf6ecf303d2d378b6b6c07d88bab8f7b204601bb28500",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:373",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:373"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.restrictedOpenSections",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8a6476ff83529c91a661ac0bfb1823d5a141e47043c62ec4eefbd6ef0039a275",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:7538",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:7538"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.restrictedOpenSections_naturality",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3451d567cdb4e01cb55dec35961df2a6c40e511ee4a70a4ddce4b758b1325d3e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:8415",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:8415"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.restriction_of_glued_power",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d38ef1a1616c84a9d80d8930cd586743590f6fe1704cac9b7347adf86b054c81",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:19216",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:19216"
    },
    {
      sourceName := "OAI.PiExponent.GlueGlobalGenerators.exists_finite_global_generators",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlueGlobalGenerators",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e6f38beac444514282e6376bbe01f1bd774a357cb9f4d33fee1e2c05de9812d9",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlueGlobalGenerators:2896",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlueGlobalGenerators:2896"
    },
    {
      sourceName := "OAI.PiExponent.GlueGlobalGenerators.globalEvaluation_epi",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlueGlobalGenerators",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0deb9a532293e3f6ca47316f87e88ddd17c38c3a6beb16c1b7a7bd47eae0d445",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlueGlobalGenerators:796",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlueGlobalGenerators:796"
    },
    {
      sourceName := "OAI.PiExponent.GlueGlobalGenerators.globalGenerators",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlueGlobalGenerators",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "494c2607a454774e1064381e47a2bcc90aabc6259900422f2972d5904e23ba8b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlueGlobalGenerators:2484",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlueGlobalGenerators:2484"
    },
    {
      sourceName := "OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlueGlobalGenerators",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "455e4937f595ae848e32e96fca9a5f4ac0e5b22ac60da2ac67701352e7cb185c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlueGlobalGenerators:2650",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlueGlobalGenerators:2650"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.Cochain",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "500a52ff8931926ef5d76b2eaaf2afd06d535b1bd4ff01367ab64d43c50d042e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:8810",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:8810"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.IntersectionPiece",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d1f1f2d97a300f7e0cf9b424d41f58b95a254a3b92f3b3006582f299c7eca31a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:6968",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:6968"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.augmentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8a8c94f3630885dc5baf4a4c006bf1415eaff15cc7dad59b68bd10ac1101e666",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:11771",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:11771"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.augmentation_natural",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "325237539c391d01eebf7d6b1d0e4478e27fa6bcfe1042af05bd6f85d010f45e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:15208",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:15208"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.cochainMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "14edcbfe449c740119253fa15d0fb2cdb3ce39babd1708b916ed5eaba53fdada",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:13851",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:13851"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.cochainMap_differential",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "215d797c45de0399a9486150cd144329d841728075f5ee5ef7a361fc23880cf1",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:14186",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:14186"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.cochainMap_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "880b2f41640a4080883faa8ca0bff97db9042f08008d5ce52e997fb6c3896f88",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:16656",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:16656"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.cochainMap_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3146e785aa2a856130ec95ff4c4f07f64c159aaf8e106617f6922c0e8efb4949",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:14589",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:14589"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.cochainMap_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "57cafc8410724146b1bcd94f1daa35e5bc5e527a6f9c43661afbf5c5fc8b58d6",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:16086",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:16086"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.coverProduct",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7512a99489388bd57cb3c4e4ec0fc986a9c70d2b75f3c03acd419214ac252199",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:5822",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:5822"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.coverProduct_dvd",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "45f828b15411b925eb28e383acb6c34c66f8045dca9bc8ffef4c1e9aeaba9d50",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:6758",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:6758"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.coverProduct_factor",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "68e13de4004716c83754cd2362b6d62cb0231287b6c5e155b3c08ad34afcd839",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:6309",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:6309"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.coverProduct_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "af1294659cd591e3fdb4400352a4eac67677cb4acd3088a013b8f44b07f31c6d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:5881",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:5881"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.degreeRestriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5f80ecf5924ccd71056121a021630a75696fca27b5df139b078abd6a77060a7b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:4602",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:4602"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.differential",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a0b3d465f2eb219e7cf174b9414a264b785c24c2e555a2ad7d099696b9fc3fee",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:8929",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:8929"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.differentialHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d5a6ffac184d61a118ad981bc3a1899784a732251c1b844368af4335eb94f7b7",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:11434",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:11434"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.differential_augmentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6f94b63a36b863f0127ed17543e7eab26b710c0b3bdb707848c8d43d50c31b3d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:12574",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:12574"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.differential_squared",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eeaf2a51c1cba2ab31afeea1def40bbdeac1bf06696765d33b38a7e27cb3c189",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:10761",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:10761"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.differential_sub",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b1e684b84ab916d110fc585e5415358fd801c9b81cd5b145588328b04d49de56",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:9435",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:9435"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.differential_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7e3fc408c8ef5d81be57663fa307682af1ec92419cdd62441435b820983d9b97",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:9199",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:9199"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.divisor_isUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "abda57cc9ada972f613132272dc5246a5b7081f798952f6b9a99a3c363a246c8",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:350",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:350"
    },
    {
      sourceName := "OAI.PiExponent.GradedCech.divisor_powers_isUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "54c442dff0935ebb33ddff6a859e2e4bd8c396247b1f5561237a9cf849aaf6dc",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:811",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCech:811"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_014.jsonl"
