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
      sourceName := "OAI.PiExponent.GeometrySupport.CechExtFinite.sourceIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9d823a32c1eed908d97cd142e660566851c7e2b7a6ae2f16dfa6c460630b1680",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:11059",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:11059"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechExtFinite.zeroComparison",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dbdb3c3f7918ebcad6661bdd1f6266757b647bc353538ef05009996d4e403a1b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:7673",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:7673"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechExtFinite.zeroComparison_middle",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6f60a493e4099ef4bfb27527578f78b3c7d57b171ab27eada2445b19c79fdd0b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:8625",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:8625"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechExtFinite.zeroComparison_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3d0fbb114eb9fb94c2c1c3ab59342d5769ee974aad2253410c9cda524c864fa7",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:8108",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:8108"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "inductive",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "495cad9fe2f420bbc87366d4b390bb536f0ce52750209075fe0c5284db88fa48",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:1241",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:1241"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison.casesOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "41ec986cac6af1482ff56183a73583bfb302a85cfac5ef060b78bc849eb68221",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:1241",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:1241"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison.cochainOne",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f1eeee05a66e17440c21b2257cf9eef055bc6c5da50835bd75832f05f1e3a35c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:2757",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:2757"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison.cochainOne_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c80a7e256881c3d1e8c1bf8aff6cebc7d9920b8d39f6d26dd21a6c69adc11a4e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:3289",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:3289"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison.cochainTwo",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "66b62f1d45dc33d966e1528e3e35fa7f9c04503fb71da863f20a488ab18af5b1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:3020",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:3020"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison.cochainZero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3af83fc0533968551ba346117580ca22efe3515803c1fd894790d874e86a3fce",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:2366",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:2366"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison.cohomology_one_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a357555b4554274b048675ddfc4395dc6483c3328de25cf59f596ae0c3539fc8",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:4833",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:4833"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison.hasPrimitives",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0a284c1669bc4c4c70b7c8f1a31ce20baf16a6d35a9a2914eccf76966f93e7f0",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:4344",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:4344"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison.map_differential_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c84e8a3eee3562de87d9b61147ba87d9163d3ac63b159b989e1b7276799f032e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:3880",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:3880"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison.map_differential_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d80ca815b7cb01c8ecb613aa7dc5efb0dcc698530790e9095090519cc0d2e4f6",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:3431",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:3431"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison.mk",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "ctor",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1741d9bcd75fdf3d57e4f5449501be95767d5c2ac7cbaebf3760da3b4ffbcf1e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:1241",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:1241"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison.mk.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "624100f581874d4dec1eddb89ca724ab1b36248ee3a83130892550f43a3dbc40",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:1241",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:1241"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "604bac9f523b45ac88875c57b2e0dd156e42698a386e992740afd3d1420237ae",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:1241",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:1241"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison.pair",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "35816fb597ef9c1f8290e0910c1259b39bd4c2963df52bd6e06b978ade0458c5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:1241",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:1241"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison.pair_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0eedc4fe3c241a56b54b10fab988a102f836585698a20f451c2315e998e1758e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:1241",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:1241"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison.pair_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6f6a9b84fd1a700796c03e4f157dd69235163128eee9fc8b3193b12905003d5c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:1241",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:1241"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison.rec",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "rec",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "422f76da3404129c928875fc2445c61daf1f7d664c1fc77d916af9f6d7c54bea",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:1241",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:1241"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison.recOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0282b465068bde9dce12edd8a6a8f843a512fa484ad016acac932391d4cdae96",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:1241",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:1241"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison.triple",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c0ba775b66760be4f0569893ac28012c5f2ac79746903dd3db21b778e81ef139",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:1241",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:1241"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison.triple_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a33c2299685063f4887ecf5d448df859b176860d00e5eafd42139883ae4d9df9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:1241",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:1241"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison.vertex",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "effffe946dc269323f11b876b004e6af15d0d6a13d2f12254fbc06863d87bea3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:1241",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer:1241"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.Cochain",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cd591eddc00d8510937999c60afbbb17e676cf317bba4560ecdf361f36fbd464",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:997",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:997"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.HasPrimitives",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2a7a6fad2db55b8b7e831050c00e67faa99939a8a4fe97fb82d9e33051dbf8c0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:1287",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:1287"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.affine_ext_succ_eq_zero_of_injective_cech",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "98638be1036fcef91529b333cdc6b36a4fe9583e29fa4fe28e4e6fe39150701a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:18026",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:18026"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.augmentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "13595a30bc86e6443fb0004a3cc01ba28e9c7807fe0d8c791919240b53fc62fc",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:12834",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:12834"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.augmentation_closed",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eadd8d237245a827f5f3506a3cedc47032d8605ad1cc770300cfaa65ca85dd3e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:13023",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:13023"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.connecting_cocycle",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fcef344aff4a708be4534ff60af80840c5c53e82f181588be4ee0a633ecff73c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:5907",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:5907"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.differential",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "654abeb48a1c9d6026863549aa98bdb853ed95507c715069c03a0e0eec8c19a2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:1094",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:1094"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.differential_squared",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f9d06005c77116c840cd58a1480d739690b1731fc41882c9de4c3dde9cc69bb5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:2960",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:2960"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.differential_sub",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aa6132c18e01e2b74d817425af4cb9fcb2642fccbd89f45cc4ab2d087bf2256d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:4172",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:4172"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.differential_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ebfbb02bd6bec4a86a114f6a7665df0417f170aa5552eb966dca144f78e238f5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:3949",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:3949"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.evaluate",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a7e89ee6ba3d68b1b3969619543bf3aed54172ef05d2c55e0ed2eb41c88d84ec",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:2206",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:2206"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.evaluate_differential",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cdb015cc4a99702108e50e86c300d00150d80d9cea63e608a43ad770a8fcc3cc",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:2467",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:2467"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.ext_one_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b86cd4f7ac3941ca8060371352822027ad62900f72c405edf7fed8f46dfe002c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:15310",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:15310"
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
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:827",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:827"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.glue_zero_cocycle",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b76d48400fd89473a867112769d7058eef9e5a707cb65d90dbf4e92fafd4da8b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:12471",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:12471"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.intersection",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cc48c209d1e1fda18142f507f395581a76b0b462cc568d980f924023cf01f806",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:564",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:564"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.intersectionLE",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7aecaf43880c1d650603a41c52052bcb86af76e179dc22b9474e0c2832185fce",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:640",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:640"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.lift_cochain",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9cbd160438241d98f13161cd1be8204fb87f6cb1fc222f8913ad4975be53f898",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:5008",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:5008"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.lift_kernel_cochain",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ad52066035bbd3559ed65e5d081adaa1cd2fbe0438b2509f0675e709ebc39e14",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:5462",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:5462"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.map",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ab7c7694d8e26cdc25715d8c8a2a098d6bfaba483320b8c75bc3338eef3dbb0c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:3515",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:3515"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.map_differential",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a5a3a769ee9a718026b78f7cf19f9cb590b0d9f3e01141c4d4645c93ad729d66",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:3644",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:3644"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.map_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a8637964691f0c31018ee48dfb9fb6705caf2c75224bdc0fe3a77773beac2ce7",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:4798",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:4798"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.map_sub",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0875cf865d228cdb64f987aeabc4b593eab06c999b6ddd9bcdee4267426c19bc",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:4586",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:4586"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.map_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "541e5aa420a76ceae4ee79c08d468433d787e3943ce43cb5e983fcc9c6728083",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:4425",
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
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:1446",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:1446"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.restrictHom_sum",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "42613a89ef15aa67127e10156c81a6ce7244460b181c37752becd88ded301d14",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:1719",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:1719"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.restrictHom_zsmul",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "187d2a484a7a9a847881db8f5c2be068ccce6cbb86f54bb1a28fa788cf1122a8",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:1983",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:1983"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.restrict_cochain_congr",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ebd03572b593ac28063938d0493b76dcd4a1eb0b76204d8382bf5f59796f1a79",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:8262",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:8262"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.sectionZero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e044a2105824620074e84ba6575fda70584e6cd9a5e94757844086d1b68ca1ea",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:10336",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:10336"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.sectionZero_augmentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7c52cedd31461ab773d2652390f3cf37e12d12ac463d9d5f1c5843c7405d115d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:13632",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:13632"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechHigher.sectionZero_compatible",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3c206b54656f0e860408cd9b4b099604c29de2a59b779eaa5ba86b210c630162",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechHigher:11009",
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
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:1448",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:1448"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechLinear.boundaryToCycles",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4d03c18598052deaaab429915e55d5c9aaa750212a09cd6a842da99968de721a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:4362",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:4362"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechLinear.boundaryToCycles_primitive",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "13eaf223ab19c582773911e2431cce7fce71077c94f52ce1bd70fa20cbe16b0b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:7909",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:7909"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechLinear.boundaryToCycles_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "39327b0c0b2f205a38d92cabd0470e241b7d792b76618c91dfc9aa19bdec6128",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:7362",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:7362"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechLinear.cochainAddCommGroup",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c6f794a647afe3dbca621afa73dfb0d947729fbd0ec55059e01b11efb17a0078",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:1567",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:1567"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechLinear.cochainGlobalModule",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "67ea07a8c895c89763fc9ee6c25514d2d98849b5ad9e422d640ef79fae190436",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:1769",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:1769"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechLinear.cochainModule",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6b134ad9aa8835a03a7920a8b7c6cf5fac9a44e550405e7ce8a976665132e2cd",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:2131",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:2131"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechLinear.cycles",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d3773aafdf1af872794de0818af25436c6db19db78ba296ed1bd6988cac2da14",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:4109",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:4109"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechLinear.differentialLinear",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ddf166fab6c1d0db5da3587c77e99d8aea5d67f134fcb929d95a7b8473a418da",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:2324",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:2324"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechLinear.mapCycles",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2876294912bf3e93c29026d361fb50aeb827ff17c0ae23af22977236c5df9b05",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:6300",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:6300"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechLinear.mapCycles_boundary",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b15d1f67e17843763d530b27dc8e03d81aa4de7e5c66fd03e2da69eb9026b22b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:7079",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:7079"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechLinear.mapLinear",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "478c89c4b5cdbca267cacd20194800e5ac98bbfb112527463871352dc7dde928",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:4797",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:4797"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechLinear.mapLinear_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ae69d1aa37aa6bbb3cad3f415beb0b881dff4821d16143d3c380ccb02e0c2ed4",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:5592",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:5592"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechLinear.mapLinear_differential",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d468ca5307a380ea5ea40bac7021abcb91c3a6826e452fbe438e62e374d7572c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:6038",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:6038"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechLinear.mapLinear_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9194efba702c73b34de6d8acbcf729c0fcfb80d97125699be32230af5cf82624",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:5840",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:5840"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechLinear.primitive",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5bd8935d93687c1359d30d454cd8540b952cc1347dc9dbecf27bc34b9645ad07",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:7652",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:7652"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechLinear.primitive_spec",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "31203c9b5746d838b49b27c39f9bb12fd8ede142a5dda325edd6a05c7f6f361d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:8277",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechLinear:8277"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechOne.hom_ext",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechOne",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5cbf5f6f32eff579bf8fd335224fb32a82f9691774fb03f252b8561435447641",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechOne:3066",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechOne:3066"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechOne.hom_glue",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechOne",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "51d844d64d668495632a8b23eef7396d234576498f2c69a086371c829e38a34e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechOne:396",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechOne:396"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechOne.lift_of_ext_one_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechOne",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "60413d094e13677bc52c10f6cb893129f1005c301ae1d5c12b95f398b395b381",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechOne:3729",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechOne:3729"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechOne.restrictHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechOne",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3d6173cbc52d750da5ea08dd36c7dd07ab4a73a59960b054556e98caddacfe43",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechOne:1597",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechOne:1597"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechOne.restrictHom_add",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechOne",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "85024de58185a23e2cb44b0fde658df27ab72a0780cc56257bb6836f28517fcf",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechOne:2566",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechOne:2566"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechOne.restrictHom_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechOne",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "72d70312716cf48fb8f80ec69cba3470ce53c0c8c2eb09feb84721df12bf16c3",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechOne:2319",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechOne:2319"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechOne.restrictHom_restrictHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechOne",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cf5f588a85ab793cd5415b42ec0c6ae6d8e608eb3b669ce4111eccf6c3f55a48",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechOne:1762",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechOne:1762"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechOne.restrictHom_sub",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechOne",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7e6004308d7c1500711d75c36c6ef18bb8ad068895f5e6494b4b4700d4cf530a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechOne:2816",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechOne:2816"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechOneConverse.hasPrimitives_of_cohomology_one_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechOneConverse",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aed3c7c40695ae85f39d27821f6dc1e52545602dc91986e6296f6b72abbf5463",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechOneConverse:2578",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechOneConverse:2578"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechOneConverse.hasPrimitives_of_ext_one_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechOneConverse",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "23d7a430517f50673a1e5301462d5fb59b4bcb7e7c2c3727e61e77a83dbdbf74",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechOneConverse:562",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechOneConverse:562"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechOneConverse.instHasExtModules_oAI",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechOneConverse",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b3ed639071f795546b59809dfe10a4ee40fd222ac6ca4f58b5a35cc0f092a5de",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechOneConverse:2347",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechOneConverse:2347"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechZero.augmentationLinear",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechZero",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "446c4faf86c26bae6986bd31f63c411b87914d1b33c1c6a0e0daf0d7d630198e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechZero:2629",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechZero:2629"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechZero.augmentation_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechZero",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d15237ac4dcbb34b464214554ea16bff321b6ccab1ecb3284bfc6d0de232385d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechZero:1958",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechZero:1958"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechZero.augmentation_exists",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechZero",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "74e4f435a62f7d1a20832cf7dab5bf24740d0589ea739a47bf6fd4d974161259",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechZero:1537",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechZero:1537"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechZero.augmentation_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechZero",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6cfa3e7d6bc4ae1153e748c730437f1cba8b7545da00ebeefc709bb613138258",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechZero:1198",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechZero:1198"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechZero.sectionZero_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechZero",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "411908a7d00c19e6eb822a4ac5bf6cb7a3420bc93f16f5dd6a8558e58700bfbb",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechZero:1009",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechZero:1009"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechZero.sectionZero_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechZero",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "233d2938c04fd5a2f8f903cb11ea08301ec963e4c3c6cb2853bd14ff76ae15b7",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechZero:501",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechZero:501"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechZero.sectionsEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechZero",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6d3228a5f084381706f03e7242d77dd5622f8729d6180ac0b06fc4a6fb0c18c0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechZero:3791",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechZero:3791"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechZero.sectionsEquiv_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechZero",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e3a16f233af33aeff726ed78a2b5ae5e0d0fa47782ada9cf5b4b4f57d6ba0bd6",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechZero:5488",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechZero:5488"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechZero.sectionsEquiv_symm_mapCycles",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechZero",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e3a97da771bd4d4fcd763c6bef4088ae5c055ad2fc5f85ef0c2cc8cf37379e18",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechZero:5865",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechZero:5865"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechZeroAdditive.augmentationHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechZeroAdditive",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "88a67c626b929666d48cbaaba3a19d94436d75b71cd5560747f9cdf2161eb5e9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechZeroAdditive:962",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechZeroAdditive:962"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechZeroAdditive.cycles",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechZeroAdditive",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "70fd21b19ef343e10e2607072585a0e010c5c238355b50fa2bac87d5281dac0c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechZeroAdditive:743",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechZeroAdditive:743"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechZeroAdditive.differentialHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechZeroAdditive",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "650c8b4c898e9c86340337938bbd04d05dbf07267e192beb78e24dfcda6ca457",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechZeroAdditive:457",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechZeroAdditive:457"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechZeroAdditive.sectionsEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechZeroAdditive",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c33578ad2214021c25908cd837d6af8fe1eeaed33925e89528169961e80a99c6",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechZeroAdditive:1331",
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
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRecoveryMap:757",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRecoveryMap:757"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ExceptionalRecoveryMap.twistedMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRecoveryMap",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0e3dbebb22cd508fad33cdbfcf55bf26fdf385c2897e471cde4d8647901ee156",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRecoveryMap:1913",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRecoveryMap:1913"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ExceptionalRecoveryMap.twistedMap_app_bijective",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRecoveryTwist",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fdfa2133eb5d1d2f950899ae1db595557aa1e9450780ef4d09130106b3debaa9",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRecoveryTwist:558",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRecoveryTwist:558"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechResolution.coverVertices",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "97080913275f5f391f24e642ca2e640620e2d2849e3ad39531e3955874312dd2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution:2447",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution:2447"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechResolution.evaluation_freePresheafComplex",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5622fa84ea0cec2221cfa7ec108f08c4b29182ef7528254b64d6fef5ba87985a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution:3798",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution:3798"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechResolution.exact_of_objectwise",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "32172cf30468f143725168d85de6a81d4c60c7d4c0e9271a127365be96be8e78",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution:3363",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution:3363"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechResolution.freePresheafComplex",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "87f53d6ff3fa1802d1b717672f58868817ee9b1d7f9a0be9805ff2fe1c071617",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution:3118",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution:3118"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechResolution.freePresheafComplex_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cb01406781038de652c8d9f29626649160a571c95cfa44aaa575459769d3ec73",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution:4311",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution:4311"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechResolution.freeSheafComplex",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "28fac6ae3f025edc8c335dffb9eae71be3e61938f4f088fbe3a318bfa15c374d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution:4723",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution:4723"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechResolution.freeSheafComplex_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "17a09ff5480cf7783c0e1474d3662b4a3deea4e6750d26e7c322b542dfd4602b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution:5023",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution:5023"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechResolution.freeTupleComplex",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "78fb7e1d2f90b3c474ad7ad5afc032523f2fa618208d434c2f422ed57394de7a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution:1464",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution:1464"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechResolution.freeTupleComplex_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f24c856c0cbd09d7aecad585994dae5f46d739eb94f663d11cacc484db116934",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution:1626",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution:1626"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechResolution.tupleAugmented",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ddc4862799e73437aadf2fefcfd7addfaf4fd932623b0f0340146602205a4b36",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution:512",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution:512"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechResolution.tupleExtraDegeneracy",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7eee836050c2bab2b6dae4d56e89a8519e33e7e4fa87342d15c78df83829f304",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution:650",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution:650"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechResolution.tuplePresheaf",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e508443109ec35908aaae04da004f7d78d20d5a9d80e4bf4d2e671f7b67e125e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution:2712",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution:2712"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechResolution.tupleSimplex",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f68082d216c6e57e9ad648153549a4c3414d328911eacedcac5e8e622dafa5b7",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution:323",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechResolution:323"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechSections.affine_ext_succ_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "135fa78280ea79ebcc5bac02da080c12fdff8f70e2ac25f46867e16089d171e9",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:8951",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:8951"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechSections.boundary",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8c67e23e9c22471d449a14960cf8831dcd3af277395f8f1bb47424e66694c471",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:5446",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:5446"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechSections.boundary_eq_sum",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cae04e8f64b14038a589d10c416b548bb57248c6911b4fc70b412dadbab44504",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:5637",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:5637"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechSections.boundary_squared",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a2aeff043375e370588206a03723c617f6c13e91f0a9570c9397ce24a708621f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:6131",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:6131"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechSections.canonicalTuple",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "210953b1c61cbb7c9519471374bbca15e9adb8c23e55b5a16c4aa1ec353bf4c2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:500",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:500"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechSections.freeFace",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c73adbeb7ed7c1d6e3d33411b2d52755d77d6b760a22f2b46a7f829a8e1c4f5b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:4505",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:4505"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechSections.freeTerm",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8859a1dee6d0402dc81f8f1a39d1e1bfacf8ca2fe4ce4cdd8593ac596f323cfa",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:2024",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:2024"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechSections.generator",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c5544e0bfe8c47617ce553ab1d78bc4f3add3eb701d6aba14646045ecc698833",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:2881",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:2881"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechSections.generator_face",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6c38c1f46de681f2da818db5fab5c7033a000352c000eded944bcfbf6679096f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:4732",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:4732"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechSections.hasPrimitives_of_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "705e7d5477a504693017f99a40ddc0a92694824f8f0d4a254986f374214c6cbe",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:6999",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:6999"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.FreeCechSections.injective_hasPrimitives",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a93031437111ba6700734d2cc15d3fc8656451adea9d22e795717f4b82be7bc0",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:7856",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections:7856"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_012.jsonl"
