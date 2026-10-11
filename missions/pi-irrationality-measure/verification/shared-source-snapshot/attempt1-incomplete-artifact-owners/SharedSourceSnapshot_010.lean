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
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.laurentToFull",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9aa1fb0a46099b04b089cfee2495ed21b4c1b4dcbcf1562887677032006863cd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:3405"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.laurentToFull_groupAlgebraToLaurent",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0ff5955431ea7df766eebf69971281c1c888dbd892f0f74c86c492656468b7fc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:4032"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.laurentToFull_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c7e94c998d60e27fc68f19c68225d5e65b9330fa2eed213d85eb6e34667f15f5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:3628"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.laurentToFull_overlapLaurent",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "64514ca26aa920f9a47b2d7ac5df149f1a8df088cb1afc962005eca7debc0057",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:5179"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.laurentToFull_single",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ac48f2637d3f2fe3e58a3dc1a9143b9b0c70b9416a38772852c1bea2b3dd2f4b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:3846"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.overlapLaurent_change_pivot",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9836b8121962e9e57f6be9b8c99cc0c432ce0f4ac64cd57ada1ace2ed4032afa",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:7346"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.overlapLaurent_change_pivot_pow",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8a8a7e8ba7487bf52e6065f5375178cb1ff3533ab023c588e1e6e9b8579661c5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:8372"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.overlapToFull",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8919f5244a792cab54752550bcaeb132c98310a7ca2aeeb6f007ddbf7b3cd2b0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:4758"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.overlapToFull_C",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3d4adf0b6ac9b2c24adc0a198cb2349101acaca057c3f63d44205217ffb1ca13",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:5858"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.overlapToFull_X",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "81d4e50a038c8911c3ae890c6270eb051aaa9017abea2b5106c9161cde5692bf",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:5512"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.overlapToFull_natural_of_generators",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3045327c1e5a658cf46d19702245b593b51f2475f2f13b042b2191d218574fca",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:6409"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.overlapToFull_ratio",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f64dd36f4d7c49cac552211656a001c93ad5e92df489272bd8ece73820ca5bba",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:12099"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.standardExponent",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e69d7fc37a3d62d75fa7efc9bee7234c2a22a754fc911b258ff32ae8dba68ba9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:408"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.standardExponent_other",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cae8225a80f682d07fb9983d7d8dbc3fef613b1bb604858ce8e5d44aa9f3ac12",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:643"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.standardExponent_self",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "66cbb466df718972add4675e9ead761b7be723e397dc39df3df8ee0bb0bcc390",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:499"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.zeroDegreeExponent",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4d2aa955ffcf54593632e28df40bbc8e630b0c4c1c7098f6d9f50058d2313ac7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:811"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.zeroDegreeExponent_coordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "38871c95a512780cc9cf92dcb0fe26356532c84743fae37edf2c4840a20de12e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentTransitions:2334"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.ChartExponent",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4332e5ef21de03b52b26cfa1f0f80dd7afcca70e1160bdb90f881ec3483314cb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:398"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.VertexMonomialSet",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ee2b0ad8f87f775c338a2d5ed9b3ce310b39177b3ff06b1eff5721290c5b46db",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:465"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.chartGroupAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "072bed5274ce90e6c2f95497b11524b24f935f195dc8f269ecf920817be1a8df",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:7271"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.chartProduct",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "edb87342158aa775f8cdc7a08134d05e484767d89455939426bd63c1a9b84404",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:8172"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.decode",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e922a6b27603f6951ee31a1c51ca71d6d56959dbfdad0111a481528031b082b6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:1668"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.decode_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "39f7de9e08432568d8a39811cc955fd1f1d238520ebfcaba7ffbbefbdd5c45bb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:1814"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.decode_encode",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cf8a6a2951a5b96fa73fa28c4267b82a8dda24a17dbdcb9f3479e7c6b86ec41a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:1970"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.encode",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7645f375b2ff30f33681c595f222371ee0fb06e5fba46a8d534e18d70232ef46",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:576"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.encode_decode",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3fcc37fe4e9022d027e7207869e177a29323eb9117fd55eab9d32a2bb381206f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:2130"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.encode_other",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "597c8f3706fee758fe6aec8fd5df686d282a97793b11456160711fce987a45a1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:1258"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.encode_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6f6fbfff09ee41d47b84fee96e1db5df0fad50b182e499751d0d1540c7741c71",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:1447"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.encode_self",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8817d2cfd97300ba7490909b5d8216847570232a188c8eafce29f0d2dad8ee75",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:1075"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.exists_cleared_exponent",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a866ea011a0a27e977d0df7ff477d1b35d05331fb11d3cce6698a26c5b47256a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:16879"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.exponentEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "50afe35acf502cc5a0b819c192a4d396e0fe6e74782a2e58ab95d03be4a9edd3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:2876"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.fullEncode",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b3a811c0141a40b590f1e57b25cb8815be0d0b731d5a0207d3c62c2de81aa4f2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:5858"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.fullEncode_other",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1350488f0dea1bd2b15f6471144247bd71066db013f44302d227019ffc4eb5b4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:6540"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.fullEncode_self",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a4758f4b2f55676ea08275050a0a46b89f15a960ca796d4b459bc241ea5432f0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:6341"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.fullExponentEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2625bc6a222d27a0840e9edc14bbd48b1770090125d3395f9e718ab1c89627da",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:6745"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.groupAlgebraToLaurent",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f57e5dabcd73cb4d505db8770052445c4cfb1629f617f27f6dd19487d384d18b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:7985"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.groupAlgebraToLaurent_coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "44092829a94f9de895d8eeb726cd45d20e63b01a738aef063c6b27f59b342ffe",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:13493"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.groupAlgebraToLaurent_smul",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0cc4687fd5b7b6ae0c14bbdce4d2fcfde470058e64e78c0c40471bd599683699",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars:1573"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.groupAlgebra_product_isUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ea1dbb1ffcaabddab9cac7762ed2e1f2a746f45f91bafad1ba38792dacead653",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:9034"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.groupAlgebra_single_in_overlap_range",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1bd8c49e5396d83b12124ce702e6516e511a61fe2eb4db3a92b2f0c3f8f74316",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:17978"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.groupAlgebra_single_isUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "78dfb9a334121a06a4bca4495ac5136c44bac7eb6f2237568d1f8c30fff7799f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:8307"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.laurent_single_in_overlap_range",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0e9d449b8f65e18b18416980250770a717f7b013e41424ae56e4c387cbd1bb07",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:19230"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.natExponentHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1a93b983a378c191dbeefafb057367817638ca67e93a4927eb1eca00708110aa",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:7360"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.overlapLaurent",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "51ccf4d9373e30e31484dbebd30ba43dd5530649936034a91db870cc1734ea54",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:10494"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.overlapLaurent_constant_mul",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cdfc8face43a6e691743f7395a67a4aabce16981972ef6dd7f70e15cd487e1cf",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars:1777"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.overlapLaurent_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "38e86d3db1d3dd9776100189b486ed7956b67d5b80c5e0d53caa3acf8996be0c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:10738"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.overlapLaurent_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c131ce91a0fabe2156606941a3a35b892a9893143f8749a53f13cfc920bd6f95",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:13755"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.overlapLaurent_surjective_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "07ecb1c45a94dd4a7d78fc666006fbb59940dd6ee70fc8143659102d5a8db240",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:19859"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.overlapToGroupAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7c2c70e803a521f9dc8fea810eccaa7693a9d20b37c72730e33616ca48736857",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:9367"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.overlapToGroupAlgebra_base",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e6a65e31e95e13f9f7bdc25cf6f5ec44169a75bd6d9ec4c31f3f27ecab47199c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:9641"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.overlapToGroupAlgebra_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "96eeeaeef27b38b951e3062d0bc2e8351e59af79ce7535d8b080813b60b3fb94",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:9978"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.overlapToGroupAlgebra_nonnegative",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1c2c75eaead812adf7a8001e107f7529c8f7dd463fe2c2896f9b56266b8f9106",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:12496"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.polynomialToGroupAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f9d398b77fb734d06e02627f491fae5c65a62405ab4d232ec5c96cfd9e02bcc0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:7542"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.polynomialToGroupAlgebra_X",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "89f462db35077fa482c773ec90a08429a17c5c365bb8982e553021aa0459b774",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:8672"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.polynomialToGroupAlgebra_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dba14e6d0ba57d4614644eb11ef73a173cca245185b2897c4b7236e40f64db99",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:7721"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.polynomialToGroupAlgebra_nonnegative",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cc67d5fd51b08faae6373f1738840e55ec185f65ea22b441dbed84820f16234a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:12133"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.polynomialToGroupAlgebra_product",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8c21e50d6f8c99ece4ecbc71614e0d410953c5f8ace2bac15ffd8f83da5b488c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:11123"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.productExponent",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6b68ddcb3fd5b369ef57f4a80acacfa9eda6c90ed4c0e0c749f0772bbd6beae2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:10971"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.productExponent_inside",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8a0d6ceeec89a0b5012710906242609b7c972ae661d54d0258384022589e8bef",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:16594"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.productExponent_outside",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fdb21118b2fa07e4a0f20839fe70d77d59808718165a3e7aa43cec843656bf8f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:11756"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.vertexLaurent",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8cc6e24f426b8968070226436ba53ffd6954a1d06bf98bcd9d0eeae3e98f4f08",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:3492"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.vertexPolynomialEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5f265d6dec152fb13d80edddd0f04f5da9a972fc12125961d9a4c4778662d821",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex:3167"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveTupleCharts.coordinateFiniteOpen_tuple",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "59547eade5b7057764b36fb94b90d90bd3babe1dcfa076b7758ce86253913ed6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts:2516"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveTupleCharts.coordinateOpen_isAffine",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e50b3e22d30b2f1ed556ec9dc9fcabec25ea6745e64e19a6bf8033168f801cbb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts:4743"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveTupleCharts.coordinateTupleCoefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8c05fe9c91829aa98bd814b290cf1d5dfb04d15c420eff0e9275708741ea3db5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts:5082"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveTupleCharts.coordinateTupleCoefficient_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a5aa4af8591b6cca152d6cf539b4f8114e3b1edd41409433f173d5c6564e60a8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts:5493"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveTupleCharts.coordinateTupleCoefficient_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "652ecf046a5b20359f4c8a5d6bf1009f3ee4f5651cf0cfdd6c7d385c883f6025",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts:5831"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveTupleCharts.coordinateTupleCoefficient_surjective_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6d8654828f8aa778b0e2c9fe3d4f5767da5ffcb4b9354cf1d871c326b494f987",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts:6590"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveTupleCharts.freeOpenHomCongr",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8885d99908ace79502f31501e1efaf170870c86807067e7c24839c3d7e96db35",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts:3354"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveTupleCharts.freeOpenHomCongr_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7f809207df440639b9c8dd8b1a1fd852597e3fca13159e60c8acf7c27cc4e0be",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts:3907"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveTupleCharts.mem_tupleVariables",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0d1b776871cda3c33805842e316288eaa53b0732602184befa912ce8bdf6484d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts:608"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveTupleCharts.tupleVariables",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "965b21e6f2cb698305e1dd9776094e26ec4a8a3ca71512031699e3b7ba8d2da5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts:417"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveTupleCharts.tupleVariables_inf",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c6bd5e08d72f88fe6a09287532f7ab9be55dc83b2e420bd426ffca8124c25d55",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts:1851"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ProjectiveTupleCharts.tupleVariables_support",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "755486a81592bf26d0992d3abf13b62a328cbf805c5261d287d05414b189bde3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProjectiveTupleCharts:834"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.PushforwardOpenSections.comparison",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f23b67bd08dc6614bc8ff69c560676e08eb692dcd57ed4120fe0be5bff79d61e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison:2478"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.PushforwardOpenSections.intersection_preimage",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "65e4440a3c0667c7417322b8577512fb737c74761106ed4bc147ca8968836a5d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison:591"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.PushforwardOpenSections.restrictEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c71639548f1929001afd79a61329f48411bb427f73692172c2e17ed82c226b8e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections:3242"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.PushforwardOpenSections.sectionMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1238311b2916d30d428c9aac25f758cf27515c4dc9d871880c7103ade2cd70e9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections:649"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.PushforwardOpenSections.sectionMap_bijective",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c93203a15c85341c0cca0df3ba8dda7706a64145b39c7b7d5ed4e6f3e38e8374",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections:1557"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.PushforwardOpenSections.sectionMap_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6301495a39bc53a8ec87d1fb60c012f17808b07e94722e22b7cd77f99421463c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections:1794"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.PushforwardOpenSections.sectionMap_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b84d7e5dfb9bbfd55b85b8676c00f42a2cb64cfe74b1650bdd64808cd86ce0d6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections:2031"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.PushforwardOpenSections.sectionMap_value",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4d1a70cee00c0e379bc57ff19dfa3b61bed06417596f750ea274a5e6e4df774c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections:1337"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.PushforwardOpenSections.tupleSectionMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "87607322395cd3e7ff5ee0156f5ac55455c66e3e040958d2344ba90dfc4bf51a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison:784"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.PushforwardOpenSections.tupleSectionMap_bijective",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3515e88c220944935b446bb258e38c46081ee87dd166edb61398b96767ff5570",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison:1146"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.PushforwardOpenSections.tupleSectionMap_face",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ad1527327fa8a2518e4c1d892fa1356699a67b2d3595abf109c8f056ac0d4e72",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison:1838"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.PushforwardOpenSections.tupleSectionMap_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b561321a48ca6bdfb9341ba9978f1340acecaa16f60b7ace112200c7c9a09728",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison:1492"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerreAssembly.instHasExtModules_oAI",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SerreAssembly",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ec761ab49bd14e3245ce3b8112a6a31ceae6dbdb51efe4e140525336ca4c6e9d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SerreAssembly",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SerreAssembly:644"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerreDimensionShift.AcyclicPresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      graphKind := "inductive",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ea80a2d8a785b2c164058f5087801731ccca2167f959d1b371ce3007a3793e68",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerreDimensionShift.AcyclicPresentation.acyclic",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e1d329681b687d41e3671f9425111c73f674a016c19833c54396a6064aa4d13a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerreDimensionShift.AcyclicPresentation.casesOn",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "289fc983b94040b880fb4793ed01bcd36e7c580dc90b04dc6d5f489357301d42",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerreDimensionShift.AcyclicPresentation.comp_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1747f2d2f18a8a2636852fbd6191b012d34d4804a6895579f17ed26c8923d98c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerreDimensionShift.AcyclicPresentation.kernel",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b83e0f1f3ee9343e679efdb10465b99b90ad7a1fe0dc6965ac8fa57468d4b700",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerreDimensionShift.AcyclicPresentation.left",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "67fe282ce8c134c46084661e5f46f0f050a1d5573f6ef370ae2fb1fa7239d1cc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerreDimensionShift.AcyclicPresentation.middle",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "56ec23161677afbd25602fd0c59956bb7938285f68305c08b9ebc73596946bb2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerreDimensionShift.AcyclicPresentation.mk",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      graphKind := "ctor",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d685a3c868a644d3658504db67fcdcd3d63273888414a4c4e400781b49c1f047",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerreDimensionShift.AcyclicPresentation.mk.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9a9ed593a9e9bc2ca94515d484c63f73fd3b385218625803d2f00fc510f08e50",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerreDimensionShift.AcyclicPresentation.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e41b40daf9babc3d75f18fc18dc84f1cc8159431bf78e6e4ccd18357f05a44af",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerreDimensionShift.AcyclicPresentation.rec",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      graphKind := "rec",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "beffe2c6710a75b7ceb7adb32e910712c0d55ecc159fba8917298f6a72cfbcc9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerreDimensionShift.AcyclicPresentation.recOn",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7f529840d0263f41804d828013f4ea391c743ec8bc9109b79d7cb885a5147fb5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerreDimensionShift.AcyclicPresentation.right",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "268df7da4dbc710269f2f5f20a1a5a96bf4cf527c1df5a83c591efb63a49de82",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerreDimensionShift.AcyclicPresentation.shift",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "53c0b5f6658fa6de3d3b55fae85c6c8021eea5d0dfdec541e525e116d8700876",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:1050"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerreDimensionShift.AcyclicPresentation.shortExact",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0e17ce9c8a279b5b7c09486c1734a6be160cea052a83010cb2a0dfd6b0b69e8f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
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
      sourceName := "OAI.PiExponent.GeometrySupport.SerreDimensionShift.ext_eq_zero_of_biproduct",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "17416d907201b8a54b0889b6e4540b959e6918d6dc50ea9c60cd036650ab72fa",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift:684"
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
      sourceName := "OAI.PiExponent.GeometrySupport.SerrePowerDescent.moduleTwistLineIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SerrePowerDescent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "787610dc988252cecde18a11edc031fa3832bb69547076664f9cd91600cb369a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SerrePowerDescent",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SerrePowerDescent:821"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.SerrePowerDescent.residueTwistIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SerrePowerDescent",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a5a9430165c773e63f8ec23f58b812a97a1bb2385f09622e216f9bb596d6139b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SerrePowerDescent",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SerrePowerDescent:1610"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.TwistPresentations.acyclicPresentationOfGenerators",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "520f3a38e39770e89adf3e423e73f159795da302b98a7bf888cd68b12ca1a16d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations:4919"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.TwistPresentations.coherentTwistFamily",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a10066bb731ad5edbcb887ce55f02e5797b94cd8af97fdd1bcabd4aef6360e57",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations:4757"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.TwistPresentations.presentationKernel",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "67d829456341f0ee815e4eead695a847bcd2802b574aac436665d30873319cdc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations:1370"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.TwistPresentations.presentationKernel_isFinitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d07934c580232368c5ec33fb429658df70197c5f61c3fd9878847b8eb89cf14e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations:3313"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.TwistPresentations.presentationLeft",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fe55965af8cd5903e3f26f456085878ebf6bb0094addf52aa8458e80c864a075",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations:1555"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.TwistPresentations.presentationMiddle",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5642b80b9edb0f69e7a8b77a9df16c78b308e6ea2ec25271115a4b41e40fc67b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations:1443"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.TwistPresentations.presentationMiddle_ext_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2ab51753370460ae18668de858fbeb123cc027ead49b6d9d650353d33ace8821",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations:3858"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.TwistPresentations.presentationRight",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3f68eceb815447321b9948e39e42a1ca0c02f61d63888ccc256e37ee1cd2ab02",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations:1748"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.TwistPresentations.presentation_comp_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3d48d6d5769e43431f8b6b0cd35dbe3e7026b4614f8eacfc38ba6a0bc31f6dfc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations:1928"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.TwistPresentations.presentation_shortExact",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0c6047b165905bf32b33823d26af018208c4e37c6377c72ad0b259f29c59bff6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations:2182"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.TwistPresentations.twistFreeIsoBiproduct",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6e8e293e7cf524fc3e45ec5556498280b9a7a76f48e85343d919be095b9b6b71",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations:740"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.TwistPresentations.twistShiftIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c6ce7c839120ff69ec6e147d934657ec51c4eeb9dfcc3f641b15a4f37e21f9ab",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistPresentations:502"
    },
    {
      sourceName := "OAI.PiExponent.GlobalPolynomialCoefficientLaw.CoefficientLaw",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GlobalPolynomialCoefficientLaw",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2f2042962ac2ad0aef1aa82fd85b623f488df955b9f830f7ef0039b8e423925f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GlobalPolynomialCoefficientLaw",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GlobalPolynomialCoefficientLaw:427"
    },
    {
      sourceName := "OAI.PiExponent.GlobalReesRecoveryComparison.affineChartNoetherian",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalReesRecoveryComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9e58efc723a876c0ae7a84edef031188fed5fb4c291a989665cc031ac116204f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalReesRecoveryComparison",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalReesRecoveryComparison:1718"
    },
    {
      sourceName := "OAI.PiExponent.GlobalReesRecoveryComparison.affineProjection_quasiCompact",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalReesRecoveryComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "773c0b8d11b463fb6f555aecd38f3cc1d40ac3898555d767541bed39e104e9c1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalReesRecoveryComparison",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalReesRecoveryComparison:2000"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.OpenSections",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "62ab9c2d43280c0690f2f2a438b18030cd91460227c81c697de1f18d9b78f939",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:667"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.affineOpenPrincipalEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2cdd5ab9292c93c364d95f2e5f4056f7b6d6ba91ae995b74e6b366bae2a03f36",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:13967"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.affineOpenPrincipalEquiv_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6b9b443183ee3c043579a72adbea61e2d8bf51c60f7d4af72bfd488721d1d7f8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:14701"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.affineOpenTopEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c1bd7cf37c8ed9d8203c3d9935f508ba8736cc4c6aee4505fc55af29b3e56de0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:14402"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.affineSpecSections",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e64d8167fe9d4bf5c68af65a4b7bdd94548016a82d31562eabf509875a654427",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:2906"
    },
    {
      sourceName := "OAI.PiExponent.GlobalSectionClearing.affineToSpecModule",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8c175b95a604369e59eaadcae23b20f1935b046968aa5f051d6ebba5dacdb59d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing:2266"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_010.jsonl"
