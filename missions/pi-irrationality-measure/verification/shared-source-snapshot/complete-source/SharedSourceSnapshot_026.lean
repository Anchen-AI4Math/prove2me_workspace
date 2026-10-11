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
      sourceName := "OAI.PiExponent.SeparablePointLength.contractedPoint_eq_ker",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b810d3519f57174198c08db833d7acb580fa69039435166e35398892a8aa51a6",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:2515",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:2515"
    },
    {
      sourceName := "OAI.PiExponent.SeparablePointLength.contractedPoint_isPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "facf7b03c8634dfcbc34d25c7a34919ba2704acccfb62999c8341db0b1545baf",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:2245",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:2245"
    },
    {
      sourceName := "OAI.PiExponent.SeparablePointLength.length_quotient_map_of_unramified",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c708fd9bc774200a668e0cc846b3a79bd9bab18e0edabe0428c122d82d7af113",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:1348",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:1348"
    },
    {
      sourceName := "OAI.PiExponent.SeparablePointLength.pointLocalAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ddc9fb12c07cf10513a537eab4bb98dbf640a364e5a33c6d7c6e3a8a5626dd13",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:3126",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:3126"
    },
    {
      sourceName := "OAI.PiExponent.SeparablePointLength.pointLocalMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c340fe7bec3f2fc18dfdf5a4fc47062cb32b917d16aec287c100c2cbe983cb73",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:2802",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:2802"
    },
    {
      sourceName := "OAI.PiExponent.SeparablePointLength.pointLocalMap_algebraMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "81d8580ac8587436621d5e4862fe77f3d5668b103ce677bd95b5b655598b4bad",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:4759",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:4759"
    },
    {
      sourceName := "OAI.PiExponent.SeparablePointLength.pointLocalMap_ideal_map",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2ae981a907c26a00f4ea44fe7ca84e9cd0f4c7ce8b449857cca2a722c602f650",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:5266",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:5266"
    },
    {
      sourceName := "OAI.PiExponent.SeparablePointLength.pointLocalMap_isLocalHom",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f73053a60d53d40bb3d2a144cbb06afd4fd6d9099f8a021bba27fd7f7d00c505",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:5116",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:5116"
    },
    {
      sourceName := "OAI.PiExponent.SeparablePointLength.pointLocal_essFiniteType",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3b219bbd5039b5aef27f31ce5e263436f233300a8417f626df00c9fa7aee7b11",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:4303",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:4303"
    },
    {
      sourceName := "OAI.PiExponent.SeparablePointLength.pointLocal_flat",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ee54f1dbffc35bbe2439b330d95c7a25ae23c270ff631d05411dcb73a9f096ba",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:3433",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:3433"
    },
    {
      sourceName := "OAI.PiExponent.SeparablePointLength.pointLocal_quotient_length",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "01935673bea7566a8d3a3de0c49785ccb4c00ae2abdd2e5234854a36bb716acf",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:5728",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:5728"
    },
    {
      sourceName := "OAI.PiExponent.SeparablePointLength.pointLocal_unramified",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4def710e1a5061bbe38f6cbc8cb87117974caccfdb60dc77aa71d27cb78d9dc8",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:3801",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:3801"
    },
    {
      sourceName := "OAI.PiExponent.SeparablePointLength.point_liesOver",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f6a1e26c574a56c441c7f19c2bc631d15beece0e4475249bb35450fe7b0a474a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:2385",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:2385"
    },
    {
      sourceName := "OAI.PiExponent.SeparablePointLength.point_mem_minimalPrimes_map",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ac59d4c05e0c646a05c30dff98cbdb76dc8c52983ed7e753b1c66b904cb2bbc9",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:6999",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:6999"
    },
    {
      sourceName := "OAI.PiExponent.SerreVanishing.ext_eq_zero_of_affine_cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.SerreVanishing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e4f5d5044e91865b54ebf53faebd365b1af07c2f00d688c0b245a514dd420859",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.SerreVanishing:522",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.SerreVanishing:522"
    },
    {
      sourceName := "OAI.PiExponent.SheafSectionGluing.glue_after_map",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SheafSectionGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "35c0e8be865b5e1b2ad3edc2599f3fd4d677ad7657c419a1177c4e6cf0313e12",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SheafSectionGluing:1248",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SheafSectionGluing:1248"
    },
    {
      sourceName := "OAI.PiExponent.SheafSectionGluing.mapSection",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SheafSectionGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c3cf52b1aa39e5806f8ac773dbc6283e72fd57405f410b83835080c831c55111",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SheafSectionGluing:340",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SheafSectionGluing:340"
    },
    {
      sourceName := "OAI.PiExponent.SheafSectionGluing.mapSection_congr",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SheafSectionGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6b576c39c6ceac49927bae9f9b650268b76774ebf1f61bbff89075d6f25bba76",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SheafSectionGluing:1037",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SheafSectionGluing:1037"
    },
    {
      sourceName := "OAI.PiExponent.SheafSectionGluing.mapSection_naturality",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SheafSectionGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "05a566696bee347336f92bcfb1fce56f070e6a0a97fc25cc91d01d9c25034261",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SheafSectionGluing:578",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SheafSectionGluing:578"
    },
    {
      sourceName := "OAI.PiExponent.SheafSectionGluing.overlap_difference_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SheafSectionGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "11c5a4b30804e1357fbd59988bdbb0887fe38c94c6fc0766cb9f2c713f919d14",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SheafSectionGluing:3282",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SheafSectionGluing:3282"
    },
    {
      sourceName := "OAI.PiExponent.SheafSectionGluing.restriction_of_glued_map",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SheafSectionGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4313720570105bc36d8000646314f950c16d37170e18485b74fe30382aa312a8",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SheafSectionGluing:2235",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SheafSectionGluing:2235"
    },
    {
      sourceName := "OAI.PiExponent.ShiftedFreeGrading.component",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3b34faba30e3f50c1d3916242624e1973d4b299427b372c61985185023af20cb",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading:584",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading:584"
    },
    {
      sourceName := "OAI.PiExponent.ShiftedFreeGrading.component_eq_zero_of_not_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f493e59c9ecf548e83f5c5d640b49ef7aa12ad362f25eaf4bde8a4a4d8341ac3",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading:947",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading:947"
    },
    {
      sourceName := "OAI.PiExponent.ShiftedFreeGrading.decompose_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c9f358eb44d3160ceaabce0b11e19cc569e4924311b4878709fbee5af81eb8ce",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading:3936",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading:3936"
    },
    {
      sourceName := "OAI.PiExponent.ShiftedFreeGrading.decomposition",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9a265e935fd43c90412106638661c83883b55b27d8778a3bb027d907118ac780",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading:3324",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading:3324"
    },
    {
      sourceName := "OAI.PiExponent.ShiftedFreeGrading.decompositionMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5a830ea936f7ea41075228d2749aec6741b6f882289ef304500159bb0de4e619",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading:1461",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading:1461"
    },
    {
      sourceName := "OAI.PiExponent.ShiftedFreeGrading.decompositionMap_homogeneous",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "14b5341143cb0e63eeb42d21c1e859da7a3739b187598e8152b1b823529528d9",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading:2819",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading:2819"
    },
    {
      sourceName := "OAI.PiExponent.ShiftedFreeGrading.decompositionMap_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6d0144167ed1a1937575f63d2f259995e695fc26a4b46b1f0e5f77137a0b8e49",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading:2373",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading:2373"
    },
    {
      sourceName := "OAI.PiExponent.ShiftedFreeGrading.piece",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f65b38eef5b5eaf51c61eae14a414d61df58e961d3ad3ef986ce51bd90af0e87",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading:350",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading:350"
    },
    {
      sourceName := "OAI.PiExponent.ShiftedFreeGrading.support",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0204c2345b1ac1a4a2cf7fc56a7f103c140c569ef161d66056b32a6da2dd5c4e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading:777",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading:777"
    },
    {
      sourceName := "OAI.PiExponent.TaylorRectangular.derivativeWord",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TaylorRectangular",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c6630fbee861d5798d833c8e0d93793e72fac6201dbeca875ef2013e85039bf0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TaylorRectangular:1818",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TaylorRectangular:1818"
    },
    {
      sourceName := "OAI.PiExponent.TaylorRectangular.derivativeWord_cost",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TaylorRectangular",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dc231e419a2498e2b4150cfd4e0a5fb3fbe204c17ec426025d1cd18b5789759b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TaylorRectangular:3054",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TaylorRectangular:3054"
    },
    {
      sourceName := "OAI.PiExponent.TaylorRectangular.derivativeWord_cost_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TaylorRectangular",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "df172563e1bdf0379e52a9dc9504500ab43eb24a9a8d21e2dc77d1e642222f46",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TaylorRectangular:3695",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TaylorRectangular:3695"
    },
    {
      sourceName := "OAI.PiExponent.TaylorRectangular.frameWord_append",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TaylorRectangular",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f7a3214f9fa5c078e248b0891e0b325b3e367bfb261c40aebbc163ca2d8d4f32",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TaylorRectangular:2033",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TaylorRectangular:2033"
    },
    {
      sourceName := "OAI.PiExponent.TaylorRectangular.frameWord_replicate",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TaylorRectangular",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c3afb99c6aa3b6df407411efb9b5cdb6e33691e66bcd208706b8550df3d723d8",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TaylorRectangular:2314",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TaylorRectangular:2314"
    },
    {
      sourceName := "OAI.PiExponent.TaylorRectangular.frame_residueTaylor_ideal_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TaylorRectangular",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b7ef2e31c656e881e59ea047e15a2f0da073c024780a35b22d35ea8881f6eda9",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TaylorRectangular:4248",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TaylorRectangular:4248"
    },
    {
      sourceName := "OAI.PiExponent.TaylorRectangular.mixedIter_eq_frameWord",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TaylorRectangular",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ddd8b0dd85a14c1a6cdd84ab6d5e821b49c7ad02d57e2edb545861c3b7cfe891",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TaylorRectangular:2582",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TaylorRectangular:2582"
    },
    {
      sourceName := "OAI.PiExponent.TaylorRectangular.rationalFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TaylorRectangular",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d5f6e4679b7734bfe1c3e44d5a29b39d4b16114856153f81c864e7b46aa47bd3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TaylorRectangular:1287",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TaylorRectangular:1287"
    },
    {
      sourceName := "OAI.PiExponent.TaylorRectangular.residueTaylor_mem_rectangular",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TaylorRectangular",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "40f954d2b22504585e7b5a566af80fff4772f854ee45cd0eda9ce00b991d863d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TaylorRectangular:434",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TaylorRectangular:434"
    },
    {
      sourceName := "OAI.PiExponent.TranslatedPowerCover.Ring",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.TranslatedPowerCover",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "06d660ad4d12d5f5bb9e45a8e5a56a8b98dce160ec18c94edac0293e09550e55",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.TranslatedPowerCover:316",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.TranslatedPowerCover:316"
    },
    {
      sourceName := "OAI.PiExponent.TranslatedPowerCover.basis",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.TranslatedPowerCover",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d8d604fbbf73085735f7bff0bcbd383d2953c209c75d12a63858fb3dae5c2e6d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.TranslatedPowerCover:1688",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.TranslatedPowerCover:1688"
    },
    {
      sourceName := "OAI.PiExponent.TranslatedPowerCover.decomposition",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.TranslatedPowerCover",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c0828b2bc584a27737b7cd7553b698f7540d9fd9c580cdcf2362204634886d12",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.TranslatedPowerCover:814",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.TranslatedPowerCover:814"
    },
    {
      sourceName := "OAI.PiExponent.TranslatedPowerCover.instAlgebraMvPolynomialRing",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.TranslatedPowerCover",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fc5677e3bfe75e20b9c995114861c299e414091bc81f7fd5709be2e7222b6049",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.TranslatedPowerCover:623",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.TranslatedPowerCover:623"
    },
    {
      sourceName := "OAI.PiExponent.TranslatedPowerCover.instCommRingRing",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.TranslatedPowerCover",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "738b489b2ef4af208ac75d3833586355c9a0f8af3e9f389494599fb1cab3f664",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.TranslatedPowerCover:394",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.TranslatedPowerCover:394"
    },
    {
      sourceName := "OAI.PiExponent.TranslatedPowerCover.toPolynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.TranslatedPowerCover",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "358fd55f816a7253686322e30575ef9914ffee02c13245e82b7812a45c9dc164",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.TranslatedPowerCover:513",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.TranslatedPowerCover:513"
    },
    {
      sourceName := "OAI.PiExponent.TransverseSliceComparison.comparison_of_normal_basis",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseSliceComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "56c7e9a231a1966de441919c05d6d975fc36f7723fcc2186640ba1e949686d44",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseSliceComparison:4225",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseSliceComparison:4225"
    },
    {
      sourceName := "OAI.PiExponent.TransverseWeightedMultiplicity.rectangularCutoff_budget",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseWeightedMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "49a0897efe30800619bd1eb19282bd175d9445f9ba2151a7a2e5fa568f04e387",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseWeightedMultiplicity:1324",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseWeightedMultiplicity:1324"
    },
    {
      sourceName := "OAI.PiExponent.TransverseWeightedMultiplicity.rectangular_weight_product_comparison",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseWeightedMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "01a8fa82966de862786125229f8bb3aefb098b547f71d4fe419fb6448df9120c",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseWeightedMultiplicity:1903",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseWeightedMultiplicity:1903"
    },
    {
      sourceName := "OAI.PiExponent.TransverseWeightedMultiplicity.weight_comparison_of_rectangular_count",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TransverseWeightedMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f4ce0c201e22f68820eb6c829a900dcee582d898870e86606cc5794910aa513d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TransverseWeightedMultiplicity:2891",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TransverseWeightedMultiplicity:2891"
    },
    {
      sourceName := "OAI.PiExponent.TupleCechBound.FullSupport",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e5c80a58aff98bc279b8dfdb8e09543e3013d1644958ad0e53a2406f0d35e1bf",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound:273",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound:273"
    },
    {
      sourceName := "OAI.PiExponent.TupleCechBound.contraction_closed",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bfbc5249fb84e4bd06ddaee71b4fe46e6fbf7b477cbeffd10253d748725cfd2a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound:625",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound:625"
    },
    {
      sourceName := "OAI.PiExponent.TupleCechBound.differential_extend_missing",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d8239220f0ac7c614f14d185b423bd343258bb92a92f7da60f6c2d88598e6042",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound:2121",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound:2121"
    },
    {
      sourceName := "OAI.PiExponent.TupleCechBound.differential_extend_pullback",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aeb0207411021ac4914b472c0a3b93bd0d927d100bf7f6b73eb96922592ada1e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound:1377",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound:1377"
    },
    {
      sourceName := "OAI.PiExponent.TupleCechBound.extend",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "391d52c60d61f83726e23fb3c94198602c3c9fa5dd658f7a80c4f1eca84a703e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound:924",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound:924"
    },
    {
      sourceName := "OAI.PiExponent.TupleCechBound.extend_missing",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d402b1b1fb0e434e5c565ef500429b6c1f0b684da3aeeff57e39e19e479c7a64",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound:1766",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound:1766"
    },
    {
      sourceName := "OAI.PiExponent.TupleCechBound.extend_pullback",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2f85246f53acb74cab31e4ff9f9a23fc8bcd7af7ea753f2eebff74240fbd79ee",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound:1110",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound:1110"
    },
    {
      sourceName := "OAI.PiExponent.TupleCechBound.fullSupport_primitives",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4b274924898947724352afc70b80ed751999c2fa560b234a8b33f5d0ae3e2f96",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound:5200",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound:5200"
    },
    {
      sourceName := "OAI.PiExponent.TupleCechBound.fullSupport_primitives_aux",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "943d27768984194034137ea633e93e9399299b4a641795ac9c20764742b2b7bf",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound:2499",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound:2499"
    },
    {
      sourceName := "OAI.PiExponent.TupleCechBound.pullback",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6014162bfdbec4ed0b242512ae118ae9ee004be5a1d81f8011e2fba091243287",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound:375",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound:375"
    },
    {
      sourceName := "OAI.PiExponent.TupleCechBound.pullback_differential",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e4ab5ea70b04f93b80e6bb239a47cdfe9d0ef9199e7008e997b64d20162e59bb",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound:478",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound:478"
    },
    {
      sourceName := "OAI.PiExponent.TwistGlobalExtension.exists_global_twist_extension",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f1ff3de90bf8914f10f29dcc68276b9e40515b474e4ec1fbe8c0ca1b4b3b4a0c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension:7157",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension:7157"
    },
    {
      sourceName := "OAI.PiExponent.TwistGlobalExtension.finite_cover_twist_gluing",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "473455565e299756281bf2bcf6fcd78e6850b731c9113f500820195805540fc6",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension:4588",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension:4588"
    },
    {
      sourceName := "OAI.PiExponent.TwistGlobalExtension.finite_local_twist_extensions",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8a642a7abd7102863643f1f96bf7d70e10ba53719364e0b438e9ba49d2d5fab5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension:3131",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension:3131"
    },
    {
      sourceName := "OAI.PiExponent.TwistGlobalExtension.global_twist_extension",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "28e9b5133ab5eda407b3ea70d885d091e4575d0714aa158a3c179b957117339e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension:8374",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension:8374"
    },
    {
      sourceName := "OAI.PiExponent.TwistGlobalExtension.global_twist_extension_native",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6124c7ec233b50314710dbecf759c680d316b418a70d44ead919a2d3a957073f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension:9166",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension:9166"
    },
    {
      sourceName := "OAI.PiExponent.TwistGlobalExtension.local_twist_extension_ambient",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9168d226a405fbfa549c4da395e46f7bb477b18a0036ed1d3f87d2935c49af28",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension:1115",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension:1115"
    },
    {
      sourceName := "OAI.PiExponent.TwistGlobalExtension.mapSection_twistSection_add",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "03550ac5010c482d337676bb0d8860454a9d5111759ea0570e90e54acf141f57",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension:4152",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension:4152"
    },
    {
      sourceName := "OAI.PiExponent.TwistGlobalExtension.section_open_image",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "da88390d1aee233131c692d0e89997ba93f3a13bf8f032d4e3fe25e826f8ce5b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension:593",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension:593"
    },
    {
      sourceName := "OAI.PiExponent.TwistSectionClearing.frame_local_input_zero_on",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5b62e06f7d76f5ee58204400456361aa13f689c81cd584bb197a8a31e43b79c2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionClearing:3032",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionClearing:3032"
    },
    {
      sourceName := "OAI.PiExponent.TwistSectionClearing.frame_twistForward_ambient_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0681bcfc0ac4ae01bc9f75f2068584b538b79d124d7b7f967fd5d4e45b4616a6",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionClearing:6153",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionClearing:6153"
    },
    {
      sourceName := "OAI.PiExponent.TwistSectionClearing.frame_twistForward_zero_on",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1f85c7b06530e257c136aba2a14dd08b0a88b5c42fbfccc592321c98cfa1504d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionClearing:4414",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionClearing:4414"
    },
    {
      sourceName := "OAI.PiExponent.TwistSectionClearing.hom_section_restriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f138f5c85b099a73a3963e4615de2d5d0118ece1deaa54a78588738a87f96cbe",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionClearing:5827",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionClearing:5827"
    },
    {
      sourceName := "OAI.PiExponent.TwistSectionClearing.iso_section_restrict_zero_on",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9f6cae21463becacef9ff7d4d0c36653e87f70228540d0ff86416228e1dacfa0",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionClearing:2548",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionClearing:2548"
    },
    {
      sourceName := "OAI.PiExponent.TwistSectionClearing.twistForward_section_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "525ce551803589dc128293c719a7272dd18695b2156782dccf1745ff6217603e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionClearing:7673",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionClearing:7673"
    },
    {
      sourceName := "OAI.PiExponent.WeightedAffineFrame.affineChart_isoOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.WeightedAffineFrame",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f29ff87f39b076bb574afca224f282de6cc1fa085110a0eedeb5a94f9ebb3e48",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.WeightedAffineFrame:779",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.WeightedAffineFrame:779"
    },
    {
      sourceName := "OAI.PiExponent.WeightedAffineFrame.affineFrame_nonempty",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.WeightedAffineFrame",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "91844d78fb2c71614584ca8c208c68ecebf0b374407e1c5b69a4845a512af9af",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.WeightedAffineFrame:1260",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.WeightedAffineFrame:1260"
    },
    {
      sourceName := "OAI.PiExponent.WeightedAffineFrame.frame_nonempty_of_isoOpen_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.WeightedAffineFrame",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "08de115bb8742cc72cf1e7593ac5df9fe553cf645e8e15f535c6ffd9abf55a57",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.WeightedAffineFrame:328",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.WeightedAffineFrame:328"
    },
    {
      sourceName := "OAI.PiExponent.WeightedBezout.finite_length_of_rank_bound",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezoutBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3070d312dbcc122929a64dd73873460e6c5f373f891066fb75ed48867c09f953",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezoutBound:1157",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezoutBound:1157"
    },
    {
      sourceName := "OAI.PiExponent.WeightedBezout.mem_pointIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3891fd6576d60c89ef72438c82fe21919c4da01cb59bf4ce35ef445f6798dc52",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:3729",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:3729"
    },
    {
      sourceName := "OAI.PiExponent.WeightedBezout.origin_minimalPrimes_map",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "767cb53234e45a55c67052aef6a37b227411509870d5302cb5823e8b06582902",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:8363",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:8363"
    },
    {
      sourceName := "OAI.PiExponent.WeightedBezout.pointIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bd7829f9799685ddd6eb3f389dc75647e681cc67012bb2691ce6caec870ecc09",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:3425",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:3425"
    },
    {
      sourceName := "OAI.PiExponent.WeightedBezout.pointIdeal_eq_span",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5a6b3f3612ef44c7008e9d22c20c2b87b03420dd407fb355d6037730040fd657",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:3870",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:3870"
    },
    {
      sourceName := "OAI.PiExponent.WeightedBezout.pointIdeal_isMaximal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "46a79363a8f432af8ed95159f1ff8d4851f6ed1d0c5534bc507c75091a4682ef",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:3551",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:3551"
    },
    {
      sourceName := "OAI.PiExponent.WeightedBezout.pointLength",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezoutBound",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9728588d4bd1a7a3d7cf7341ab0f01c065c471868029b321fc98a1d932f25c56",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezoutBound:421",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezoutBound:421"
    },
    {
      sourceName := "OAI.PiExponent.WeightedBezout.pointLength_mul_le_of_substituted_degree",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezoutBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7de25660386403d6961c35e7c5c44c6b1252b3063d575bfd394d47d3757b50cc",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezoutBound:3637",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezoutBound:3637"
    },
    {
      sourceName := "OAI.PiExponent.WeightedBezout.prime_over_pointIdeal_eq_origin",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ef254aa1ddc83c0fb1323181ee8e43e7b031d5a5b15d60ce6b4282b6bed81a30",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:5837",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:5837"
    },
    {
      sourceName := "OAI.PiExponent.WeightedBezout.rational_pointLength_bound",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezoutBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e97e61cbfe21fc74ad03469c4c2f66743d498e5f1c1526624c1976f452561ff1",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezoutBound:5426",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezoutBound:5426"
    },
    {
      sourceName := "OAI.PiExponent.WeightedBezout.totalDegree_aeval_le_weighted",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bdf7d2f2be8ab9511623fef49ab70d57392595a2336bc4bd38022fec47bdbd9c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:1933",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:1933"
    },
    {
      sourceName := "OAI.PiExponent.WeightedBezout.totalDegree_aeval_monomial_le",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "75757a1dbadbca154bb4fad5be241feab6f7fff89d92788b46bab21e644362db",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:1064",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:1064"
    },
    {
      sourceName := "OAI.PiExponent.WeightedBezout.translatedPowerSubstitution",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "262f91de09f22b338433e7370e24fc8cdfa4f15630ca7e6f84be6d63acc06b8f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:391",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:391"
    },
    {
      sourceName := "OAI.PiExponent.WeightedBezout.translatedPowerSubstitution_C",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "51c8ff60c2cee362ebc0cf6f46a91b8cf44ee397b3220211c7fb3dd64c2705fd",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:854",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:854"
    },
    {
      sourceName := "OAI.PiExponent.WeightedBezout.translatedPowerSubstitution_X",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c037fc67336b81f2dc9fb17d30dec795424a978bdce0e239ae6d0b17e04fbab1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:607",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:607"
    },
    {
      sourceName := "OAI.PiExponent.WeightedBezout.translatedPowerSubstitution_comap_origin",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "04b0180b4b7060b6c49c0b2064c1d7ac5781daa18d49a9e5fdbd0b042e8146e8",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:5259",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:5259"
    },
    {
      sourceName := "OAI.PiExponent.WeightedBezout.translatedPowerSubstitution_eval_origin",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b44a699d0ff0dc646981d0c43d4aa63185ac5e54610a0ae81b7c3a50ce4ff806",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:4963",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:4963"
    },
    {
      sourceName := "OAI.PiExponent.WeightedBezout.translatedPowerSubstitution_factor",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "902db32018898b4c9544c0722212deb81c793a5a749f8e99d0526bcfa07b3225",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:2925",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:2925"
    },
    {
      sourceName := "OAI.PiExponent.WeightedBezout.translatedPowerSubstitution_totalDegree",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1bac61a01a50fc3b763db84b56932b0a773ceee4f48ef1cbffaaaeab0e28834f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:2442",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:2442"
    },
    {
      sourceName := "OAI.PiExponent.WeightedBezout.translatedPowerSubstitution_totalDegree_real",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c1ae7f49806be7d226a34b69638859d19384a1e40c7a3e39e2ab975531117575",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:7325",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:7325"
    },
    {
      sourceName := "OAI.PiExponent.WeightedBezout.translation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "84070f3d2e171e0366e36f12aad1056787b48d820d4390e4c3166e77c7d5bd73",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:2753",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:2753"
    },
    {
      sourceName := "OAI.PiExponent.WeightedBezout.translationEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "892ab2df8cb3e3a8f12eb7066b9a8f3f5051d0e54a803882090b546929153598",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:3193",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:3193"
    },
    {
      sourceName := "OAI.PiExponent.WeightedBezout.weighted_bound_of_scaled_natural",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezoutBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "352dabcaa0848f328c93e1a19030d989d15a75660c703cc38ae9fa316c5c555b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezoutBound:1736",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezoutBound:1736"
    },
    {
      sourceName := "OAI.PiExponent.WeightedChartRingEvaluation.ambientOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedChartRingEvaluation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "67a232fa4ad48f0e91df7fe352ea361a3acee7ce65584ac5b5585e15b2d79c22",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedChartRingEvaluation:3467",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedChartRingEvaluation:3467"
    },
    {
      sourceName := "OAI.PiExponent.WeightedChartRingEvaluation.ambientRingEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedChartRingEvaluation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "69770e99e0390fffe6c411b7cda02db33a27aa7221b227b64a841bebf43846c1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedChartRingEvaluation:3613",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedChartRingEvaluation:3613"
    },
    {
      sourceName := "OAI.PiExponent.WeightedChartRingEvaluation.ambient_chart_pullback",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedChartRingEvaluation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "28109b4b51755454e479276b0dcd13a9be979ca3c52f38e9b0d6d0a0fa9d85ab",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedChartRingEvaluation:5535",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedChartRingEvaluation:5535"
    },
    {
      sourceName := "OAI.PiExponent.WeightedChartRingEvaluation.chartFactor",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedChartRingEvaluation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c888f411a85da5f2570b794ca5eb62cb929c8d9d217d1d61f1cb73c3a06110a9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedChartRingEvaluation:4011",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedChartRingEvaluation:4011"
    },
    {
      sourceName := "OAI.PiExponent.WeightedChartRingEvaluation.chartFactor_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedChartRingEvaluation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e7e740829d2eea83cfed42501e7389bf34cec3ff5916c1a19ad8a5e96820d4e8",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedChartRingEvaluation:4677",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedChartRingEvaluation:4677"
    },
    {
      sourceName := "OAI.PiExponent.WeightedChartRingEvaluation.chartFactor_pullback",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedChartRingEvaluation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b19096c8a3d2aac5b8a3eff16ebd4318551a0361df9b16a2c7d42f87c2cc3e3d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedChartRingEvaluation:7346",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedChartRingEvaluation:7346"
    },
    {
      sourceName := "OAI.PiExponent.WeightedChartRingEvaluation.chart_pullback",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedChartRingEvaluation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9e0295432fd92af226907d9085a55f4f4b3e9626829c24323cff276051bf413b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedChartRingEvaluation:1130",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedChartRingEvaluation:1130"
    },
    {
      sourceName := "OAI.PiExponent.WeightedChartRingEvaluation.evalAway_polyToChart",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedChartRingEvaluation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c204a02f9f6022dad6987fcf5a9c44679aa7071dfc862698590b7cdae7295efa",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedChartRingEvaluation:2452",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedChartRingEvaluation:2452"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.affineChartConstant",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactification",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9e2395cbe4ca6590ab6bb1ab9014dc435ed9bed34b9d6478d4b79cacaea3baae",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactification:2549",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactification:2549"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.affineChartCoordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactification",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5d92cd23679ace3ebfd34208c052dbc94d761d97ad318676bcce66d6ade5db49",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactification:1737",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactification:1737"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.affineChartMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactificationGeometry",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ea01397334cbc7391ab156906f809651df22f9e7f4d0901f471a87a62e80d16b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactificationGeometry:351",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactificationGeometry:351"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.affineChartMap_comp_projectiveMonomialMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedAffineParametrization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ac29b1a43ed6d5cc21296918a9b0e1a9f4627a8ff44ba5322a58c9f89808ee19",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedAffineParametrization:2538",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedAffineParametrization:2538"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.affineChartMap_isOpenImmersion",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactificationGeometry",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4b2185a86f079ad9a0abfaa7d39eeb04f7de438d3a1edf4d8932d8c7864e933d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactificationGeometry:741",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactificationGeometry:741"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.affineChartMap_range",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactificationGeometry",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e208765136538c5d2cb7d6689d43149ebdb030c2ff9b5e39c84130c3a0346e07",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactificationGeometry:1172",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactificationGeometry:1172"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.affineMonomialMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialMap",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "23ca1087f445dacd9d5a25a70413d63f0e6898f5967bc07d345a449b64b4e939",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialMap:334",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialMap:334"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.ambientGrade",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ce1441cff425958c58b7806636cde2552a3537d599680cd2ba1aef08c257f69d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage:450",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialImage:450"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.chartEvaluation",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactification",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "08e20bfb6dd3ae4cc60a99d4b919160d66f5720c74c0b454bc46bdde2953c81c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactification:534",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactification:534"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.chartEvaluation_comp_awayMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedAffineParametrization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "984fc7097abe7624072f79236ced8482c48581ed209d60891b71ba1568820b26",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedAffineParametrization:1632",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedAffineParametrization:1632"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.chartEvaluation_constant",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactification",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6a739a742cbeb786a25f512cf4fc1dc417f8d04bcbf2ac6cd480b160f2450aa9",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactification:2797",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactification:2797"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.chartEvaluation_coordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactification",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b3c4aae2bf6555116857874d3dba107e242f830404bc656d03795c1f7aaa60e2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactification:1954",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactification:1954"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.chartEvaluation_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactification",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "61e58a0b47aa23f82617a300aae46c08449c3c9cda56c68758a4db3c7029e7a8",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactification:1222",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactification:1222"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.chartEvaluation_mk",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactification",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a9dec0a1d424de20b052c95c23097eb784484779c10eac0599d0aa145f3b4429",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactification:743",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactification:743"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.chartEvaluation_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactification",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "12ade1fc292a047710ad2c71c6852862fbcc121d576f7f5bb471e3c358c166f8",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactification:3084",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactification:3084"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.constantChart",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactification",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5e9deb078bb8f376dc50324cbaf6b851ef3f798e69cc6dcee6ffca86fc008d6d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactification:393",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactification:393"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.constantChartEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactification",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fa43f3369254e9d41d26cbd271820bb98085dea9e0baffb6fc2e862af7371725",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactification:3788",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactification:3788"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.constantProjectiveChartIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactification",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "28a921a068f685e2d57887bad8f49baa3eb9d925a8c3bf536caf3b45201ce13f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactification:4169",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedCompactification:4169"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.coordinateSection",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.WeightedProjectiveLineBundle",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ff56b93be9236309a6b0b9642e5683a18e1685c7b15079c517653199b4b7bfd0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.WeightedProjectiveLineBundle:669",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.WeightedProjectiveLineBundle:669"
    },
    {
      sourceName := "OAI.PiExponent.WeightedCompactification.coordinateSection_cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.WeightedProjectiveEmbedding",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "84fbea7528595ff1b1efddba2c39f5573d319cc519b249619521ff0eeec1751c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.WeightedProjectiveEmbedding:728",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.WeightedProjectiveEmbedding:728"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_026.jsonl"
