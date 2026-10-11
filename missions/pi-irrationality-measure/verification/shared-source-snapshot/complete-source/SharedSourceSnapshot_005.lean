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
      sourceName := "OAI.PiExponent.CoordinateSliceLength.polynomialPrimeClosedPointEquiv_algebraMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e149af53b9cfa096a53cf7d74f4df5be6ac2b31ead5c8c903f0400da12709f87",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:4578",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:4578"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateSliceLength.polynomialPrimeClosedPointEquiv_map_ideal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1afb054a6e617e9770763ad5cfbfc470652170e9f7caadd8bbbe652ab5862c27",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:5512",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:5512"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateSliceLength.rationalizePolynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0c73b97f7704166eaffeaf42044e61d0eb58947f5319c4fa972a89850d290438",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:1161",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:1161"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateSliceLength.rationalizePolynomial_X_inl",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7b01e96f2ce1afa82d8c7a90a3f0734642f720574053bd8f21152c9ee93e1560",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:1491",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:1491"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateSliceLength.rationalizePolynomial_X_inr",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d64655b5c7b1b0c6aa8ae856291511b90e602b34fb59538c0416e46004946782",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:1717",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:1717"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateSliceLength.residueSlice",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9b93729e2e91f1df5ae3e41ed5114d4c25e4b90c514613b96746963fe135910b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:7892",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:7892"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateSliceLength.slicePoint",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e76544845cac0594a369ce22a9ce82645fabff72cb467a882a0754e421d6a7ca",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:7735",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:7735"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateSliceLength.slicePoint_mem_minimalPrimes",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bab98045e35ccc419b9b68829f6870d1a084dede9a943c8f64b482ce09f688af",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:11659",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:11659"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateSliceLength.splitCoefficientResidue_isScalarTower",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5bb83af8892b8deee4829e045ea6e77192d704173176ff71c49a22968c8a1527",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:6556",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:6556"
    },
    {
      sourceName := "OAI.PiExponent.CoordinateSliceLength.splitResidue_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "74bb062d0d599d1dbf2795b3e7baba37cf9c1eb93dd9eb1b369a41cba8287dbe",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:7075",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateSliceLength:7075"
    },
    {
      sourceName := "OAI.PiExponent.CurveBlowupImage.blowup_restrict_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "badba0be15a8a9c41f4b711151baa6411adfb212a3d3569d98758f457adb92ae",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage:4705",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage:4705"
    },
    {
      sourceName := "OAI.PiExponent.CurveBlowupImage.exists_image_outside_closed_points",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveImageOpenLocus",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1db0b1a3073eb41470e05067472929b4ba26ca436902a3a37b5d393fb8d8a285",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveImageOpenLocus:1243",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveImageOpenLocus:1243"
    },
    {
      sourceName := "OAI.PiExponent.CurveBlowupImage.functionFieldIso",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.OpenIsoFunctionField",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a234774dbc712ecb012ea6b88a5b920ff972e64647029be8be9b0a4e7f66840d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.OpenIsoFunctionField:950",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.OpenIsoFunctionField:950"
    },
    {
      sourceName := "OAI.PiExponent.CurveBlowupImage.functionFieldMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.OpenIsoFunctionField",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e6ea89fb93c42e27d3c1aaba3dc168ce1b791515b0d43375046ff76acae07552",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.OpenIsoFunctionField:267",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.OpenIsoFunctionField:267"
    },
    {
      sourceName := "OAI.PiExponent.CurveBlowupImage.functionFieldMap_fromSpecStalk",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.OpenIsoFunctionField",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ad74b774a01bf416bc13b25ccc7775447dccf1b518372eb56ebffa3a738129e5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.OpenIsoFunctionField:1412",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.OpenIsoFunctionField:1412"
    },
    {
      sourceName := "OAI.PiExponent.CurveBlowupImage.functionFieldMap_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.OpenIsoFunctionField",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "984d716d1651898dad38b6553e6999b7b62c19cb5238aada29d7470753b02c29",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.OpenIsoFunctionField:489",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.OpenIsoFunctionField:489"
    },
    {
      sourceName := "OAI.PiExponent.CurveBlowupImage.genericPoint_eq_of_isDominant",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImageBase",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0ee5492093382ad175610a60cc44d2f5ed71378f6843066138dddf53f59f832a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImageBase:2956",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImageBase:2956"
    },
    {
      sourceName := "OAI.PiExponent.CurveBlowupImage.imageCurve",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "283febd31c7e7ba1f75af97b9385e1dcabc880ea1df3fe784dd4dcdf9105bc97",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage:473",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage:473"
    },
    {
      sourceName := "OAI.PiExponent.CurveBlowupImage.imageFunctionFieldIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d0795ac5365b15d17999c174affe8d63d13412b16d3748f590b47cc1b7777635",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage:3421",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage:3421"
    },
    {
      sourceName := "OAI.PiExponent.CurveBlowupImage.imageFunctionFieldIso_generic",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "423954a01e30aefe8938eb455769aa1699661b9a71aee3fd98be575217546755",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage:3942",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage:3942"
    },
    {
      sourceName := "OAI.PiExponent.CurveBlowupImage.imageMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9345b60400432ceb26a8a243b8ce9f9a1fc961b340d974994a62eaf14cff8945",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage:970",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage:970"
    },
    {
      sourceName := "OAI.PiExponent.CurveBlowupImage.imageMap_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d1038db724c0c1db59419da49430925e4bbc9c154744c4c2df67d038eaf24fb6",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage:1206",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage:1206"
    },
    {
      sourceName := "OAI.PiExponent.CurveBlowupImage.imageMap_isDominant",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3ef1052b4df9b7a25a87aa96e8cd83d9449ef0891596bd50c7cbf541013cb7a0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage:1729",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage:1729"
    },
    {
      sourceName := "OAI.PiExponent.CurveBlowupImage.imageMap_isProper",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "59ad24c6a1f48766fe556248ab8dcad89381167dc14b0f2075c917491a3ab7fc",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage:1502",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage:1502"
    },
    {
      sourceName := "OAI.PiExponent.CurveBlowupImage.imageMap_preimage_nonempty",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "988e78af7e5baafa858104cb356e49d3cae7f5fe52bbfbf409595b84286fff0a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage:2886",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage:2886"
    },
    {
      sourceName := "OAI.PiExponent.CurveBlowupImage.imageMap_restrict_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4b197b12df8f022054fd7d3dfd0c9277869b6ff3d2c96652e3fea873a804159d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage:2478",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage:2478"
    },
    {
      sourceName := "OAI.PiExponent.CurveBlowupImage.restricted_curve_isClosedImmersion",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImageBase",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f1daedd3c180268dc88c368a03ad3980526dc6d626c07453aea5f17846e67d0d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImageBase:2647",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImageBase:2647"
    },
    {
      sourceName := "OAI.PiExponent.CurveBlowupImage.stalkMap_isIso_of_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImageBase",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "326ad5cc276acd8a31a95e6eb012d4c077895bad3b91ce31fe52c903b4f7332d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImageBase:3272",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImageBase:3272"
    },
    {
      sourceName := "OAI.PiExponent.CurveBlowupImage.toImage_isProper",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImageBase",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "776ab11e22fd4c994baa6065f3522765503f9fa2f9821d4735bc994566a9a19e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImageBase:1608",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImageBase:1608"
    },
    {
      sourceName := "OAI.PiExponent.CurveBlowupImage.toImage_restrict_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImageBase",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "40074ae2592d456938d666c16e5db9f94b859dfc10eee4fd1655c7bc5f12c267",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImageBase:1825",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImageBase:1825"
    },
    {
      sourceName := "OAI.PiExponent.CurveCenters.Centered",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f483da26020d0aa6b35e623bb987c94d8be256e131fe8807785c88219697e16d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters:289",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters:289"
    },
    {
      sourceName := "OAI.PiExponent.CurveCenters.Centered.constant_coordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "13ff194f27f318049c396b00fcbb15d9214ea66c803250396de238f9496bbd4d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters:3886",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters:3886"
    },
    {
      sourceName := "OAI.PiExponent.CurveCenters.Centered.coordinate_nonneg",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bb13c13d764dd9297b4b3864c8106433bf737f716b36d2f99b4fb401add73a9a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters:4241",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters:4241"
    },
    {
      sourceName := "OAI.PiExponent.CurveCenters.Centered.exists_nonzero_difference",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "adf08a5346149cdad265af63d73fdf8da53a72c9f106028a62633d82fb7be4f5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters:5000",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters:5000"
    },
    {
      sourceName := "OAI.PiExponent.CurveCenters.centerPlaces",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "05c80770a3764b1041a6dcf59862eb7c463e12ac7501da3225b1c5189e6ddfa2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters:2527",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters:2527"
    },
    {
      sourceName := "OAI.PiExponent.CurveCenters.center_index_unique_of_constant",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "acb41ea90fdbb715d42e33bf556e7a7355a540856136dd14810e1820e6250fa7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters:4594",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters:4594"
    },
    {
      sourceName := "OAI.PiExponent.CurveCenters.exists_transcendental_coordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "349018a9161035fb26e16bac0b099d16a964f13d636285117ff086606ff258cf",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters:667",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters:667"
    },
    {
      sourceName := "OAI.PiExponent.CurveCenters.finite_centered",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e60bc3d7bcb943eeb1d69c753bded61770ea25566e3e27f47fea427d04ed9dcf",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters:1453",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters:1453"
    },
    {
      sourceName := "OAI.PiExponent.CurveCenters.finite_centered_family",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c4b05cddbeb00308d092f75d5aac88f0b0417e2131b2779bd353401fcf920b0d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters:1969",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters:1969"
    },
    {
      sourceName := "OAI.PiExponent.CurveCenters.mem_centerPlaces",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "197790b42ea6315697646d43e3acddb03a68807e7030f9e4dfc2f352b91690aa",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters:2848",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters:2848"
    },
    {
      sourceName := "OAI.PiExponent.CurveCenters.transcendental_sub_constant",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "57a225ce91aac6409a5b9d8d22443d9009148ab235a04b1ccadcebb591afa17f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters:432",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveCenters:432"
    },
    {
      sourceName := "OAI.PiExponent.CurveComponentRigidity.NormalProductComparison",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentRigidity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bb9f1420a2313daf6628586dcd506abeabd856f5833f57a330b61b6a72f61b79",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentRigidity:673",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentRigidity:673"
    },
    {
      sourceName := "OAI.PiExponent.CurveComponentRigidity.PersistentNormalComparison",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentRigidity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8078dff71b12d6dc45e432e39e5c2c9c76653f21f582af14b97a63991e6ae367",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentRigidity:1305",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentRigidity:1305"
    },
    {
      sourceName := "OAI.PiExponent.CurveComponentRigidity.coordinate_constant_of_persistent_comparison",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentRigidity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "298f87e7ee58dd18d8144792b8260609c7a88a5e4834a032c53382c345947922",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentRigidity:2092",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentRigidity:2092"
    },
    {
      sourceName := "OAI.PiExponent.CurveComponentRigidity.residueY_ne_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentRigidity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eb21868b4590978fbec7e559e75a9235d100dc2707a2dea8633ab1ba5f3ac79d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentRigidity:400",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentRigidity:400"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactFamily.center",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "978986751621facce68d3ec5c8ecb8cc06329119ff0e193f514ef3886d448f31",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily:1578",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily:1578"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactFamily.centered",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8252bb53551c4ef65564f88c9541f808f7b5a1aa166bee69a9df41b2970691fe",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily:1945",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily:1945"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactFamily.contact",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "12ea61042aa09eb68ec3843111749f9da3a755cb4ae1f55c04557bf95b2694fc",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily:2609",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily:2609"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactFamily.contact_nonneg",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "196dce02851fe10941e6b5fe2e84829f6b29b07b57ef8006049d1614a10acf12",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily:3958",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily:3958"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactFamily.contact_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ac22b309b130a0327f7931245c58c28eb11cb10b0d1cc02fa0255afd7afa44f8",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily:5818",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily:5818"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactFamily.contact_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a03f5ff4fa0f0559f15df8f2a90ca2f623459b597532b8564b6e057219ab1c75",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily:3245",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily:3245"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactFamily.fibre",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9845e96dfca104e1011ce11af05906f0205238f51650fc100c9d92cd087c8998",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily:394",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily:394"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactFamily.fullCenter",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ad952cb9062a7e2f2259927b4fbdd1bc27655b6d3444a1975ddea53ffae5fc39",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily:319",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily:319"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactFamily.logWord_order_lower",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5524fa36f02d5eac2f2a9de9740937aff710003e60239e0a7bd98478d557ef80",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily:4587",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily:4587"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactFamily.mem_places",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3d087dff3972a34f0a46e6d951d1a6063a15aeb2cff3b4b527b12fece18a1bad",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily:1151",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily:1151"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactFamily.nonconstant",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6653ff20c6b35009ac0a3d900f92d9de894511eb8687839fa3152e6b8a00b897",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily:2381",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily:2381"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactFamily.ordinaryWord_order_lower",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "236d7d400b751fbcf14e8e833b48d09e47691e034cbb98094736f109a51ec07e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily:6795",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily:6795"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactFamily.places",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "180057de50257c67495fe4e8e09c7cf7bcd98a0d89965bec86e45132cb6df469",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily:828",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily:828"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactSum.constants_real_nonneg",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7a82a725f2bc9d7b3c28838900558ac51c90217fcbc12e99d8f92d33608c76d1",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum:10481",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum:10481"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactSum.contact_sum_le_of_principal_sum",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b46ae493c999d4d229a8245de008b8e2a6e6625558fdd660484151508cbb42e9",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum:522",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum:522"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactSum.coordinateOrderDivisor",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "661fee3c1cdf608165167d0f01dd272a375b6225247b26d6c8be338a1565e1cc",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum:7173",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum:7173"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactSum.coordinateOrderDivisor_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8e9688acb978a937469a6aa98f18b2c1008eb3acbea1f6fef6ac1cecd91642f1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum:7542",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum:7542"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactSum.coordinateOrderDivisor_degree_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f8ac9562028cb5ab9a61e415f286cc36d421f840fb73f30ced14e965934bd324",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum:8260",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum:8260"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactSum.coordinateOrder_constant_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d289c89c2fffb3f1bb2a622df63369c5ce2558e0bdc53315c7e4a1b7bed48c43",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum:6734",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum:6734"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactSum.coordinatePole_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "690a68a404d82e835268f3310c1e18fe37ab2850c7e78bae47de97f10586ab40",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum:2810",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum:2810"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactSum.coordinatePole_finite_support",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "795e623733ad20208d785ee9045714f24225d3a366672e2264f11fe822b9eeb4",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum:3287",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum:3287"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactSum.exists_constant_of_isAlgebraic",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "688365640b45bd2e21137e7b6ab9bf2e0f29c2bc71e728f1821e7da1ebf6554b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum:3866",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum:3866"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactSum.polynomial_contact_sum_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a2185515ca61ec1d58032e00b6cfc48eb3a53ba16dcb3a56b7e9769da9e41767",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum:11880",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum:11880"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactSum.polynomial_eq_zero_of_excess_contact",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "92afb4696c668b671d18ef7ae20ed355d0ae8cc0a2887594fd07fc96f3f08f64",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum:14017",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum:14017"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactSum.polynomial_order_lower",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "87cdf8cecc525c4be65cd8015887d1ea9e5bdccf22e96fe2c12435854e768097",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum:10990",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum:10990"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactSum.weightedDegree",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "be759ff660420d017076c15102792276c3d3527b9a9cb516a69a72cebd5c7204",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum:9717",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum:9717"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactSum.weightedDegree_nonneg",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "356ddc1a71b9254207b219b6ab43f28083d3ea8642895a0582c27d8273ed8050",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum:10011",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum:10011"
    },
    {
      sourceName := "OAI.PiExponent.CurveContactSum.weightedPoleDivisor",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "50079b77ad5525eebff3c2d3fc67edc74a4d57850623e03747bdce560bdab4be",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum:8758",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveContactSum:8758"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.componentEulerDegree",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveCycleEuler",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "04edf66181fb7914fcf26037665744db6e9f62e3105d09b0d4712f3e75fb3296",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveCycleEuler:397",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveCycleEuler:397"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.componentEulerDegree_tensor",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveCycleEuler",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3d8a208fa6ca58bfdf9ea75917de7730ff6f78279fe3db3b0c552410af9c2b53",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveCycleEuler:1109",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveCycleEuler:1109"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.componentEulerDegree_zero_of_dimension_le_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveCycleEuler",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6d540d56e0d1f05d65f0b6c4d9d674b829738fc34830005c2933cd2b627c46af",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveCycleEuler:2832",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveCycleEuler:2832"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.componentIntegralCurve",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentsDimension",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e97597db44e9137ae7927c0a0e9f417ba3b7c35f81bc5bc0134601937e2573c8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentsDimension:898",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentsDimension:898"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.componentLocalCutLength",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentLocalLengths",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4317e47b1680b12389678e513dfac93576fd7989b4f9b0d2a3ca2e708ea68443",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentLocalLengths:958",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentLocalLengths:958"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.componentLocalCutLength_eq_zero_stalk",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentCutLengths",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "02a342d7f5a8922d9910129999b9322da7a6f023ae1c00351105241934524c07",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentCutLengths:533",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentCutLengths:533"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.componentLocalCutLength_eq_zero_stalk_at",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentCutLengths",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e4a3f76486f646fad30075664b70ff7c7a22f51e9e4600693e4eb8b8b0af7067",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentCutLengths:2823",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentCutLengths:2823"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.componentLocalPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentLocalLengths",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fbc579499ef1bdca40d209328ac2a5f51577bd8ebb7d915d966cc19e7d5528db",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentLocalLengths:750",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentLocalLengths:750"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.componentMultiplicity",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentMultiplicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a4ffe4f68d682f3a8da22ceeb2a92b33248c2fa120685cc882f70f02f22a0e2d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentMultiplicity:1677",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentMultiplicity:1677"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.componentMultiplicity_cast",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "54ff534beb2caef7acf3d54362ada52d985ed0ffbee8d638b4b8c267226a9490",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalMultiplicity:400",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalMultiplicity:400"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.componentZeroPointEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentZeroPoints",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "36d949be6bff160a3eaac0acaf04b65fb31bf12956a80262e7d3a54e3b4247b4",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentZeroPoints:1628",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentZeroPoints:1628"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.componentZeroToGlobal",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentZeroPoints",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d6fb60b388756297406d265931fdd77d5defa4cbd1d414cd885688071bd837b9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentZeroPoints:438",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentZeroPoints:438"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.componentZeroToGlobal_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentZeroPoints",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8021b923b243cbdc2aa426fa78ae12723717a3f717d716f460fe37cf3d4ef010",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentZeroPoints:1254",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentZeroPoints:1254"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.component_dimension_one_or_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentsDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6eaaee6bbdd67ff5ee0fa0c100b04c6ec296841121cd06adaf987323b9d8e410",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentsDimension:2002",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentsDimension:2002"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.cutQuotientEquivOfSurjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveCutQuotient",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "97ec14f326286eaaeb9f193e9027c43884e18e863b91dbe28b711f1705ab00d5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveCutQuotient:262",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveCutQuotient:262"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.cut_length_eq_of_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveCutQuotient",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7e714cab7a9854c0d3c1e223aff8272b517ef5883fd563eba10170925a869fb7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveCutQuotient:1123",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveCutQuotient:1123"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.cycleEulerDegree",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveCycleEuler",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b441af2a6919012074230b8dceb4a2d2ba3ef2f449bdd5118c783414b93c872d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveCycleEuler:746",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveCycleEuler:746"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.cycleEulerDegree_margin",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveCycleNumerical",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1f5a48e6f3bf8d9c3cee5d483da07361911ef565b89b4519fe4a7c7817f2c78b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveCycleNumerical:2059",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveCycleNumerical:2059"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.cycleEulerDegree_tensor",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveCycleEuler",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "05436181fe094fee242e93cebdf44ee4fff34a3f7a6558bc8b5efa73fa6a8710",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveCycleEuler:2386",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveCycleEuler:2386"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.exists_pullback_frame_sectionGerm",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RegularComponentSection",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7144a77905c860af52bd22504881203c28a5d8955a0bf8f6ad7209dcfcd94b4e",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RegularComponentSection:667",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RegularComponentSection:667"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.finite_componentZero",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentZeroPoints",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "df0f5ac757b7848063be75a3e3ee5cb13f3caacdf413ef4be190ce7f7a0ffcea",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentZeroPoints:3159",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentZeroPoints:3159"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.finite_componentsThrough",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentLocalLengths",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4a73b00107ea369643d3204dee5980a0e838fed9ec1d9693df0fdc03cac024e0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentLocalLengths:373",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentLocalLengths:373"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.fromSpecStalk_bot_eq_genericPoint",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ReducedComponentStalk",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b2fa49c7b2b11b44bcf66a511e0536ea8fe636c9c756926306d24f7843e521cd",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ReducedComponentStalk:1462",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ReducedComponentStalk:1462"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.fromSpecStalk_generizing",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e236b7a430aa570dfe75c4407897eea2360b15e3fc1338559ef2cf2cce2b2cd5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks:3386",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks:3386"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.genericPointsEmbeddingEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "de4bc7a7125fb72ef101c731e4f292175ebcc55e658f5d869188284508537a8b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks:1896",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks:1896"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.genericPointsThroughEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f3de945468b594d1f0a47225e9b6fdc98409975ec899786a83a8bdcdd0a906f6",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks:3822",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks:3822"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.generic_embedding_iff",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1fcb928095d1ecf147fe008cf2fdfac727115c8849c6f869ab54a836e8266f91",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks:1263",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks:1263"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.generic_iff_no_proper_generalization",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "db3966a81e82419fcd5658a52b36ccc2ab997ee50773e694e832bd5a7b7a9875",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks:193",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks:193"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.generic_stalk_isArtinian",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6d465b94ee01d07e0d8d8c9fb9b2c07fe2f10e0213a1b10c2f929fb33681ce5f",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentMultiplicity:261",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentMultiplicity:261"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.localMinimalPrimeGenericStalkIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalMultiplicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b6e200a30dd0a222f5de27b508193f26721aa0cef75c3ebd6a828aeab0b216ed",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalMultiplicity:916",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalMultiplicity:916"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.localMinimalPrime_length_eq_componentMultiplicity",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4255c752867e55e363225fee3d52f627bd7a42c321925920f185140e3816a4c0",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalMultiplicity:1492",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalMultiplicity:1492"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.minimalPrimeCutSum_eq_component_sum",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentLocalLengths",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f8c6811af1fad2cbcd608f14a70ae0ec266de876b0c90addf7928374d7df1e74",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentLocalLengths:1229",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentLocalLengths:1229"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.minimalPrimesGenericEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d807a50cb1e12e4a853b795859e340460768ab2efcad34edcc9061eaba5e9030",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks:2755",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks:2755"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.reducedComponent",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentMultiplicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "168e5cd668d88a853db32dbae44a338e3a721392e24f4d74d76b68970527afb8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentMultiplicity:2288",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentMultiplicity:2288"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.reducedComponentStalkPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ReducedComponentStalk",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bbcf2c4527ca098a6475737aebaf406e3f168016ce4a2d2864c30e35d160f842",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ReducedComponentStalk:2137",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ReducedComponentStalk:2137"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.reducedComponent_closed",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a4e9218bd1fc2e2a0a78299d3ef59a014daa4996d31588da3c57633d21c79916",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentMultiplicity:2759",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentMultiplicity:2759"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.reducedComponent_cut_length",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveCutQuotient",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0e401ed7ebbcd2df78ad698bbaf5a867bce4f8869dd110bb5895005422db51d6",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveCutQuotient:2056",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveCutQuotient:2056"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.reducedComponent_integral",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "56fdfd3b115a63e8cae1f471a176b9bb94261a2537e61903a108097f14039048",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentMultiplicity:3112",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentMultiplicity:3112"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.reducedComponent\u03b9",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentMultiplicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "af15ec0f30db636782ad7a0a15e307c8382b0f1dff7c401273efda84a42a4e38",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentMultiplicity:2509",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentMultiplicity:2509"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.reducedComponent\u03b9_genericPoint",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ReducedComponentStalk",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f0057e2e2acb385815810b3a6e2e1f99d79bffbf092c5d1520338065ed320f39",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ReducedComponentStalk:883",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ReducedComponentStalk:883"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.reducedComponent\u03b9_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ReducedComponentStalk",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0f929dda803ca76fc444f688a6fe38e251b24353dd3bfd1f975beda98d6483d2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ReducedComponentStalk:669",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ReducedComponentStalk:669"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.reducedComponent\u03b9_range",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ReducedComponentStalk",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "57e43430757d0bcc7e2bacd4c14b7786a34db62d0c2842230eef5b1706611828",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ReducedComponentStalk:280",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ReducedComponentStalk:280"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.reducedComponent\u03b9_stalkMap_ker",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ReducedComponentStalk",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1a3f6dce78dd0d3791569253e19c49343dd8c87260e68f0aa91c63f19c7fbeb3",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ReducedComponentStalk:2437",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ReducedComponentStalk:2437"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.reducedComponent\u03b9_stalkMap_ne_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ReducedComponentStalk",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cf3ba7f0e5d2b4b4c7c374bbbc3beedc3699c12dec37bf9403e73b1ae002c471",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ReducedComponentStalk:4864",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ReducedComponentStalk:4864"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.regular_component_section_mono",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RegularComponentSection",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bcdb5d12e82e59fdda3df44f24e66f373020dda678af67752004d4d650d0618d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RegularComponentSection:2859",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RegularComponentSection:2859"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.regular_component_section_ne_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RegularComponentSection",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f9c4fb8d431c94b4207a64d0228df4d96b59c8fd9a0c35ef4668385d725eac0f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RegularComponentSection:2171",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RegularComponentSection:2171"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.regular_section_tensor_euler_eq_cycle",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveCycleEuler",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "388809ea508123cf62fb6ecaf3f1327828cb377fb6a181b13939649f71ec962e",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveCycleEuler:3468",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveCycleEuler:3468"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.regular_section_tensor_euler_eq_lengths",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveRegularEuler",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a4fb6f6d73f7b50593f972d9bb166562e0d28cab4b5c9a71fc2a64f2efc1a3a1",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveRegularEuler:379",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveRegularEuler:379"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.regular_tensor_euler_add",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CurveTensorEuler",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7dcd21c9f929c43ff89daf9a38115071252fe7d3a74d5aebda3eb0220b070f47",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CurveTensorEuler:300",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CurveTensorEuler:300"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.sectionGerm_nonZeroDivisor",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalAssociativity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4570734d1a800ac75c69592cb7144c96d3bd50bdc6712e23e8528814e474df22",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalAssociativity:801",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalAssociativity:801"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.sectionZeroIncidenceEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentIncidence",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c6496b24664180bfef67674dfa0ff42adb774aaff7a4fe2bf61aec7e96c1ac24",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentIncidence:271",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentIncidence:271"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.stalkLength",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveCycleLengths",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e1e010f440757f1b7adf369d8fd345461a68862fad8b2fefb4f25c0d8022837c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveCycleLengths:403",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveCycleLengths:403"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.stalkMinimalPrimesEquivComponentsThrough",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "51c7f1321f888917b298333a7741517bbe90d91acb7588acc0bdc207f0e13c31",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks:4625",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks:4625"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.stalkMinimalPrimesEquivComponentsThrough_point",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f3c98c53cb9b928044a6caf6192953508fb694941ff46cd54c657f37302d4e77",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks:5002",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks:5002"
    },
    {
      sourceName := "OAI.PiExponent.CurveCycle.stalk_krullDimLE_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalAssociativity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4927b4ef5db18bcf868c400474d0647ddf78dc14ff1dd404b4abb9d22cd65a91",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalAssociativity:473",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveLocalAssociativity:473"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_005.jsonl"
