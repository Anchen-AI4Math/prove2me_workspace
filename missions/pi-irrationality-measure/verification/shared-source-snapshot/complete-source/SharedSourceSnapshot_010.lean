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
      sourceName := "OAI.PiExponent.DeterminantContradiction.tendsto_collisionRate",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dcdf0c06a3eaa79f6a86cd88b5311fb99a6b931bce99942529abd5d0177511c0",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:5117",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:5117"
    },
    {
      sourceName := "OAI.PiExponent.EventualLowerBound",
      expectedModule := "OAI.NumberTheory.PiExponent.Statement",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b829022a3b694653fd6c8327a850dca3a59721e08cff08304aec78466feb5af2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Statement:451",
      commandUnit := "OAI.NumberTheory.PiExponent.Statement:451"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.affineGammaEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7210b221d25c7c17fa41a5e3652cd6e467975d8ad8dc2e7f27aa462959b26f5c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart:695",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart:695"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.chartFunctionsEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0d0b80d4a29572d725d6697285a9142583de307c808858cca4d0dd0757a6f97c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart:881",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart:881"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.chartFunctions_naturality",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "568fbb536fa6ecdb78691e2f0c65ae828109bb48526714ed7c0a652077e8e677",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction:1504",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction:1504"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.chartOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "25880177313b2d0153e29d41c25fb3ab0f77b29455ffdc920bb2b311790e2f41",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart:610",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart:610"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.chartPowerIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eccd8d4995b1143d4c6e387c971dbceefc8439e21ba2e6552f0a00463a225111",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart:998",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart:998"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.chartPowerIdeal_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d537c3cd87ad32c4d0a2d560aff065818af46b57bc1d9abf3b74b43765e71615",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart:1174",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart:1174"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.chart_square",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "561aa495e82976a1ac4e974710e4740c45f69a497d5585431d45c0d63df5360f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction:1072",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction:1072"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.exists_representedSectionsOpaque",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedOpaque",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "078305cfda3324326d6bea63aef832f57cffe881ff48750977b4a982b48bc351",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedOpaque:862",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedOpaque:862"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.functionsOnOpenEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a193ec4ac67ba6e81dd4a1728f6807f6311e7a07c4d4a40fff81b8972a74e525",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction:1360",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction:1360"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.functionsOnOpenEquiv_global",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalChartPullbackValue",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7ea7133da34a5c41bb249a2e8c8e0ff288a872396180247dc221be0a3f152590",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalChartPullbackValue:281",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalChartPullbackValue:281"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.functionsOnOpenEquiv_naturality",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e87145881472e9de6d2bc3acc2e8aabbc0a3a0e54946a64831214e026dd8109b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction:2955",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction:2955"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.functionsOnOpenEquiv_pullback",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalChartPullbackValue",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "241c74b4991f88e4a685eeb0a848492484d28f1889b40c712f9d3e729cd59326",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalChartPullbackValue:1194",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalChartPullbackValue:1194"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.idealChartFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a24d123f4abd07bee18bb0bffe2933eebf5c6ea9698c960bc0ff4ea601611445",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart:5297",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart:5297"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.idealMapAddEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c595556f99bcc4b74a2aa29c607f9fdb856bc14876d9335d745322942deacf3c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart:3522",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart:3522"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.map_chartPowerIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6232bfcdc9481715ca8cfbedd2a684f4676337dd1959164fda323b3cd6734295",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart:1987",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart:1987"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.opensRange_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e1d40e62f43a6bb3554fadf44d49d169c67dc3ce48527f7b25f1906bb9584382",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction:856",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction:856"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.representedSectionsEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ce1c94169db2d9cd81f44d5bd223280ada3c9d8ed94e912720d24d8c861cfe89",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction:5345",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction:5345"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.representedSectionsEquiv_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedValue",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dd0543e84aae7fadbb731f1860e494b7020a7926f5158485e8b0746a9a427794",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedValue:764",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedValue:764"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.representedSectionsEquiv_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f8dba668df3d06aea03db02084b17047553a3cffb58a6e574be0716fed60162d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction:6893",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction:6893"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.representedSectionsOpaque",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedOpaque",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c6e72cb4a0bce32873a9f14f80130b5e7c7ec62301fbaaeeec5229df51252e2b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedOpaque:1086",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedOpaque:1086"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.representedSectionsOpaque_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedOpaque",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "92e855a5a51ac51e77c7d872939a18cfde3b2d65afd604c93486927b33ed107a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedOpaque:1525",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedOpaque:1525"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.representedSectionsOpaque_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedOpaque",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c76d32fc07209138084b1d3885ea2f01e4fda44ee36634be849a3b14d082024a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedOpaque:1283",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedOpaque:1283"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.restrictedInclusion_value",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3f58d108f1344dee839f32ccdb3737bec8174bdeabfa4bb4ae5e3a5d159b3589",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction:3497",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction:3497"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.sectionsEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0ef45270f0a574af2b57af6b21332d5a3f3d89a9ba7eee179ca0460528ba2219",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart:4154",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart:4154"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.sectionsEquiv_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fe016cde209fd183d3342fed09cda0b7b64ff1627f0a13cd84fc539417c5f198",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart:4758",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart:4758"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.sectionsOnOpenEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0733b9670f425c187456c7531119d94bcf53912f09ff987bed7a4f8fc12ed607",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction:4539",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction:4539"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.sectionsOnOpenEquiv_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ab5c9d3057fec81f9062154c17255e141374da9648644c9dd77ffbbb642aa256",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction:4785",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction:4785"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.sectionsOnOpenEquiv_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "005434052a5e26b2aa386d2d6ed6d31de5bb1ef0440879b15d21170205607f82",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction:6062",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction:6062"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.topIso_restriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4cecc5be85552e55681485b1b6989c0fa389d958fb8a90e724a4b15c342fbc4f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction:2417",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction:2417"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.admissible_degree_eq_neg_contactSum",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7cd4ae10667f6865a1693d6601fefd64277239dbc127018c692adfafdd523d2d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:24124",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:24124"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.centerMorphism_eq_centeredLift",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "16830e3e098b671afc382f8ee7cef0fca4bbf3a3002343cac6c5e0c56e1f3f72",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:12536",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:12536"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.compactIdeal_comap_ne_bot_of_generic",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6045a3c59af28e73488d29c441b2ae7c14fec218fbeb177809e5090c04f73ed2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:11032",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:11032"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.compactIdeal_degree_eq_neg_contact_sum",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fbac95d070a2a0ed56c96f1a4ca38560c2c69b331384048e6f721df105a786b9",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:19103",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:19103"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.degree_eq_neg_idealDivisor_sum",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4ef6a75b8dedc4f11b8656ee1a80f8e1b27528d2442082187f203bdb1d8bea49",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:17974",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:17974"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.divisor_eq_localIdeal_length",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b25001590537fe6b93a7b07ea7274e48b978639bd269bbea841f6475cc1a9446",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:15490",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:15490"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.idealDivisor",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "40756300b124a5894f21841ffecba8e837bb19845cead01c07bcbdd8f6b9c6ca",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:17095",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:17095"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.idealDivisor_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7ab4c33ca3d19cfc342a76fc739fbb51470aa45e64ca0f3fed8b9a5928832fc5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:17321",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:17321"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.inverseSection",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "05af169dc32b99b6b70d70624da2960d49e51271f929e7023c06d9ca7e28efd3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:1167",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:1167"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.inverseSection_zeroIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5a265193299a2713e7544a75c9570182f3e003d91e274ccec282a0a5f20ce2cb",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:1341",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:1341"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.inverseSection_zeroIdeal_eq_comap",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "623d8d903cf6bb8d47c4281280897a38971750b7708383460b48f25f2860cc5f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:2723",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:2723"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.localIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d83be64c645d4863ab481c51d11a2c448e2833e30e433f7af6ee6059b9916364",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:6885",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:6885"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.localIdeal_compactIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ca24c4f4691d974daf691836c87cf2c52fb5a08b0352f7fde531b8ef7991de09",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:7730",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:7730"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.localIdeal_eq_top_of_not_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "32aa732cb12bada5bbc831d097487b774c92af8fe2e295367d1b3fb0f7a4af38",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:8358",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:8358"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.localIdeal_length_eq_logContact",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9a184eb26a92d5fa3534d8224385e47223e9386f644b0a734b8885de55a52f23",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:13401",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:13401"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.localIdeal_specIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f59f061194ab780604021d33a406bfa3970c8312989087eb12e46faeb0fa5b8f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:7112",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:7112"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.map_powerIdeal_eq_top_of_transcendental",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5f14f3fdf495207589ba9b4a1ce2f47ce3a77cc3e240633f04cb52ab430725a3",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:9165",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:9165"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.pullback_inverseSection_ne_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "44c12ac3108a631c77624099b191a85a3bd594daa55c3f6e67081fccbc97105b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:5648",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:5648"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.pullback_inverseSection_zeroIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d2b0aec9d933f832d9ee811ff9cb62e0e76d1da6a18ff84300a83b6418a32dae",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:5203",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:5203"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.zeroIdeal_pullback",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e4239e607b3246e7822b69320efed54304f0cf312381bb7dbc563682cec95645",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:3139",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:3139"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.zeroIdeal_spec_top",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4de3636247a6930a8f9d6b81ac2dd3a4fdb4cd23ac35a1079c44c5ce05fa5f3e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:6090",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:6090"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.zeroIdeal_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4f78693c0ad88da01df82d94d0ffb81b12350e531ba3d97991285973cf1b510d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:4735",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:4735"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalRepresentedTypes.Frame",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedTypes",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "75180fd31196c1810ca116026a7dedbcd97734a7b8f167c2e6bf6a03838e8c60",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedTypes:402",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedTypes:402"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalRepresentedTypes.Sections",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedTypes",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "05fc6fa8abec24fe7fb3933c20eb5bc0266983277c39522c0f0df24db0729ddb",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedTypes:626",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedTypes:626"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalRepresentedTypes.frame_nonempty_of_open",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedTransport",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4f100ef035603b3d6a289dc5c74ceed3738ad460a4172d5ac5f52c15e313fedf",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedTransport:545",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedTransport:545"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedTypes",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7c0320ab0b347a1a8848129f1249ef003d4a5e49bc60ad6393592d25fd157463",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedTypes:802",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedTypes:802"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalRepresentedTypes.representedSectionsTyped",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedTypes",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aa6a80b68efc6097b4acb336103ebe9f7179bf5c9f0beb13bd4e55558086b20f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedTypes:1347",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedTypes:1347"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalRepresentedTypes.representedSectionsTyped_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedTypes",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1c681922f04e570edb0e2a2b3a43e2b4c7110dd9839abfbf8168417202427fee",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedTypes:1508",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedTypes:1508"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalRepresentedTypes.representedSectionsTyped_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d175d3c001aa4c86a8913ac85962d9bc96094a586ffb30004413e1ccb144dfec",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedRestriction:1531",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedRestriction:1531"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalRepresentedTypes.restrictSections",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "07d4b725c586c9cf55d8137d49747495dc638ca178c3a44d37a30a4ba60fc0ec",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedRestriction:612",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedRestriction:612"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalRepresentedTypes.transportSections",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedTransport",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "03c2f603594d9fb8bee1ccd1459a5629fa16c98be41a42f2d533502443287409",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedTransport:735",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedTransport:735"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalRepresentedTypes.transportSections_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedTransportNaturality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0e21df20969cb3e393cedeb638ed4ed737ef5c444b12d0dfee9c862a5838bcfe",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedTransportNaturality:609",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedTransportNaturality:609"
    },
    {
      sourceName := "OAI.PiExponent.FibreContact.contact_zero_cons",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FibreContact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "11f5a262139d934ed9445b3b6c5373c844a8c91b7afc9b965460086887582ba4",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FibreContact:327",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FibreContact:327"
    },
    {
      sourceName := "OAI.PiExponent.FibreContact.coordinatePole_one",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FibreContact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "55974bc854d80e05db22fa6b282f65e7dfeafca1672994b7f71d7fb9b8f97e4c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FibreContact:4558",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FibreContact:4558"
    },
    {
      sourceName := "OAI.PiExponent.FibreContact.coordinates_one",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FibreContact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fd1cb22d73303826ea56d42b307186589476f36974fe5c10ef9910c62af699f6",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FibreContact:1570",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FibreContact:1570"
    },
    {
      sourceName := "OAI.PiExponent.FibreContact.logarithmic_contact_eq_ordinary",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FibreContact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8c295314d1162e205ea0b6302a8e3fced3341980cf1a22333a563c1afbd21345",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FibreContact:2129",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FibreContact:2129"
    },
    {
      sourceName := "OAI.PiExponent.FibreContact.weightedDegree_one",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FibreContact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f03701b8433d3e6b490d34b74f4ea2a1f845df0067999d6a397193b13bba2dba",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FibreContact:5354",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FibreContact:5354"
    },
    {
      sourceName := "OAI.PiExponent.FibreContact.weightedPole_le",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FibreContact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "85412dd8a24764bccb1c8c6cdf29038dc4b75a4e308da1599f194bb8fbcf0be3",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FibreContact:3122",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FibreContact:3122"
    },
    {
      sourceName := "OAI.PiExponent.FibreContact.weightedPole_zero_cons",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FibreContact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2dd92ee55137db05fa8060c5be8ceafcc1d03b84fd05da410f234278e3bfb3fe",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FibreContact:3421",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FibreContact:3421"
    },
    {
      sourceName := "OAI.PiExponent.FibreWeightSeparation.positive_indices",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FibreWeightSeparation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "126b029e1e7e79580557da6b03c04aabd089df9f3858203e43eccaaf36aae45a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FibreWeightSeparation:175",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FibreWeightSeparation:175"
    },
    {
      sourceName := "OAI.PiExponent.FiniteDeterminantCollision.det_finite_row_sum",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FiniteDeterminantCollision",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f568027b4a3bba44e01587dcef3b63e22bf916156842f3cd0eda29ed52bd70e8",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FiniteDeterminantCollision:217",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FiniteDeterminantCollision:217"
    },
    {
      sourceName := "OAI.PiExponent.FiniteDeterminantCollision.finite_collision_bound",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FiniteDeterminantCollision",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ca99120874d6b38ad3334e707ab8c4306274e02244131fa5ea8e3127a5a7b49d",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FiniteDeterminantCollision:2054",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FiniteDeterminantCollision:2054"
    },
    {
      sourceName := "OAI.PiExponent.FiniteDeterminantCollision.norm_det_le_factorial_mul_pow",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FiniteDeterminantCollision",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4b91faf5f17de27ecf8f39f3138205db7605f404dc809226fbfe907e0292d64e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FiniteDeterminantCollision:1085",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FiniteDeterminantCollision:1085"
    },
    {
      sourceName := "OAI.PiExponent.FiniteGlobalPresentation.affine_kernel_exists_finitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "139598ea3ec42b92ea76d83e50e063bf6c18a5acca0f39ed1433f21f9c9948cc",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:7720",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:7720"
    },
    {
      sourceName := "OAI.PiExponent.FiniteGlobalPresentation.exists_local_finitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d01a24a9a520936bdc146df489132dc59b3b4ac276b03447142ec8ace56985ff",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:11248",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:11248"
    },
    {
      sourceName := "OAI.PiExponent.FiniteGlobalPresentation.finitePresentation_of_le",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "542f61824804bbdb4b9643d71d11a318c28ccf88a393a9e5c274c287724fa87b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:13231",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:13231"
    },
    {
      sourceName := "OAI.PiExponent.FiniteGlobalPresentation.free_isFinitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "453d5dd30dfae445c9177ab69ef2f4d8525ab3e12929301f682e152d6752cba2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:9434",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:9434"
    },
    {
      sourceName := "OAI.PiExponent.FiniteGlobalPresentation.isFinitePresentation_of_affine_presentations",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a8b0873a32e667ecea68290ac11324b67cdf5d71789b70f90f2973b668ddd703",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:6737",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:6737"
    },
    {
      sourceName := "OAI.PiExponent.FiniteGlobalPresentation.isFinitePresentation_of_localPresentations",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a8a567948a56d9d5c467ff9d91292f8977e5040b33b6fdb2d45915356735f442",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:12428",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:12428"
    },
    {
      sourceName := "OAI.PiExponent.FiniteGlobalPresentation.isFinitePresentation_of_locally_iso",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9ed99b63d5bbcde40ff690730d8db2ab2dc83f8e73857532a694b37a7ce4f6f7",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:14541",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:14541"
    },
    {
      sourceName := "OAI.PiExponent.FiniteGlobalPresentation.isFinitePresentation_of_presentation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8772411ccfaeacc4c9c14a084b3beedb6d4f6cdbdc22fd1e89445c7f29534184",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:1581",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:1581"
    },
    {
      sourceName := "OAI.PiExponent.FiniteGlobalPresentation.kernel_generators_isFinitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a4049c2a8b662d2f90cbcace2a2a2c17a196abfc897b10c1726eb11ada44c41e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:10901",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:10901"
    },
    {
      sourceName := "OAI.PiExponent.FiniteGlobalPresentation.kernel_isFinitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4a442ae403a4621d0959c2b16479b6e364d6b43c3cbc617ef654aa579d861097",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:10063",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:10063"
    },
    {
      sourceName := "OAI.PiExponent.FiniteGlobalPresentation.moduleTwist_isFinitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "15c878a8ab8bcee039192a6ac9d546508c5ee0e0fb5ca74f80cf9b3362165c49",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:15289",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:15289"
    },
    {
      sourceName := "OAI.PiExponent.FiniteGlobalPresentation.presentationOver_of_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0cdb80246d755112bd1c99e61dfae6ae020b4df5e0b87f0439500da0fff50c3a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:5743",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:5743"
    },
    {
      sourceName := "OAI.PiExponent.FiniteGlobalPresentation.presentationOver_of_restrict_isFinite",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1eba5c90a95f65ff37268d8d331e3476e75432e92304e000ac277e0978cc8b1e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:6426",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:6426"
    },
    {
      sourceName := "OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4c58dbd0f53d8caf61e3a29285d4871b6e55b514a297a38fcb30ef05f9377a40",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:879",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:879"
    },
    {
      sourceName := "OAI.PiExponent.FiniteGlobalPresentation.restrictIsoOfLE",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "696f0248487ded9764f1bebfe8070111ca1d1073f3a0978fafc3271a0f5416ec",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:14085",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:14085"
    },
    {
      sourceName := "OAI.PiExponent.FiniteGlobalPresentation.spec_exists_finitePresentation_of_sections",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8a055fc675cdcacb7c4b8ba58f76a8f9ea2d41bd2bc6b0b675d73917d6ef1f95",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:4116",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:4116"
    },
    {
      sourceName := "OAI.PiExponent.FiniteGlobalPresentation.spec_kernel_exists_finitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0723b3d7474ab61a4393b9f74e6ec34a0399d27dc3bc3a3b3725a707b2d72204",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:4797",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:4797"
    },
    {
      sourceName := "OAI.PiExponent.FiniteGlobalPresentation.spec_kernel_isQuasicoherent",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b12d123e083ed5e5f441ce92ad4ffb77209c90a0b419fb70888a0ba75ad68862",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:2938",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:2938"
    },
    {
      sourceName := "OAI.PiExponent.FiniteGlobalPresentation.tilde_exists_finitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4bd2c7a1e7617b55eb746f0afb630d166858a12b04d14d07bf4e5c2e97cfbfbd",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:1999",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:1999"
    },
    {
      sourceName := "OAI.PiExponent.FiniteTupleCech.Cochain",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d49f095708b22bd5732bc3a2a6e1828b82b1d55152a207e2631c2942f7e02734",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:617",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:617"
    },
    {
      sourceName := "OAI.PiExponent.FiniteTupleCech.assemble",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b647667423b5537bf206c518abd3285af3b121e7090fdbf8d7595d2358b3f6a4",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:3212",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:3212"
    },
    {
      sourceName := "OAI.PiExponent.FiniteTupleCech.assemble_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6ce7592d1e54d70854b6af4d80310f17eeabfaf9620a9f8e7fa098ab2a5df1ce",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:3454",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:3454"
    },
    {
      sourceName := "OAI.PiExponent.FiniteTupleCech.differential",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "473e96a39f47514a7a917ea3cef70d20124e17bd3d2ae7302151ea88522d38e4",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:690",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:690"
    },
    {
      sourceName := "OAI.PiExponent.FiniteTupleCech.differential_add",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "78b56d8303d1acd4fa288b7679a56678da95bed49b0f799d1d57913b6f2a1e72",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:1004",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:1004"
    },
    {
      sourceName := "OAI.PiExponent.FiniteTupleCech.differential_assemble_below",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "23316eb07bea5743c38212a9b0f1378b3beb10a802fa240db87c884a02052d15",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:4396",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:4396"
    },
    {
      sourceName := "OAI.PiExponent.FiniteTupleCech.differential_squared",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e6e18531ac1512da1cf8f89b3d59dfa21a65c7cc5da92e6cffe1fe123a1055ce",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:2310",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:2310"
    },
    {
      sourceName := "OAI.PiExponent.FiniteTupleCech.differential_sub",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "206658d838efffc3b4779f841a96d16cd537d816315370fab86418f19dcbde03",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:1237",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:1237"
    },
    {
      sourceName := "OAI.PiExponent.FiniteTupleCech.evaluate",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "20f8517ae8a7b25b76d282a01e6bbb0893bece7e0bce31d4223c5af2cd8d8f90",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:1757",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:1757"
    },
    {
      sourceName := "OAI.PiExponent.FiniteTupleCech.evaluate_differential",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "48114a4fa0edbd470493ac5041a02b89593dfb6ef412c718a11741d3dcf931fd",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:1967",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:1967"
    },
    {
      sourceName := "OAI.PiExponent.FiniteTupleCech.level_correction",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "567bc5286c2099ad7a25f79391985b4cb462fee98ee64384395475d5318e2c3e",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:4908",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:4908"
    },
    {
      sourceName := "OAI.PiExponent.FiniteTupleCech.liftTo",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "178b87044fb97526d46d6fe690c092c3ccc68caa549483cbf31338260b97b0e9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:1612",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:1612"
    },
    {
      sourceName := "OAI.PiExponent.FiniteTupleCech.mem_tupleSet",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f9e8bddc0e24239d655e1f5d11b9f7ba9f3c118784a6f39e48266272e70cc20f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:1470",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:1470"
    },
    {
      sourceName := "OAI.PiExponent.FiniteTupleCech.primitives",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "df6f8134a3efc211c1ee4022d0811b21d5d97935ebe013dce68747e64ada5b5f",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:6753",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:6753"
    },
    {
      sourceName := "OAI.PiExponent.FiniteTupleCech.tuple_card_lt_of_missing",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8666eab9e58e72efa6522aae98ca85e99bf8deab151634f754c930e9ba42ff03",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:2796",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound:2796"
    },
    {
      sourceName := "OAI.PiExponent.FiniteZeroEuler.finrank_eq_sum_localizations",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteZeroEuler",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0d44fce4db2476637fe91d18e642643eb6f07535db5454d0fb2ad3a4a8ef77d1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteZeroEuler:275",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteZeroEuler:275"
    },
    {
      sourceName := "OAI.PiExponent.FormalBranchContact.branchCoordinates_constantCoeff",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalBranchCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c21e19223e3cee226a6191ea17843a13596e4cd630ee9a9ea63cb1f5a99a93f6",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalBranchCoordinates:737",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalBranchCoordinates:737"
    },
    {
      sourceName := "OAI.PiExponent.FormalBranchContact.composedLogTails",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalBranchCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4b65ce4799e7a9e4a6536f7c2ea6af579ff037f884f315ab79abc7cda54885b1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalBranchCoordinates:203",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalBranchCoordinates:203"
    },
    {
      sourceName := "OAI.PiExponent.FormalBranchContact.composedLogTails_strict_contact",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalBranchContact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b224ec39f710af525a10e7a4420827b3125b45a02f6a639f0c14ca323b879d4f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalBranchContact:248",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalBranchContact:248"
    },
    {
      sourceName := "OAI.PiExponent.FormalBranchContact.composed_logTail_order_ge",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTailOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7332418337616b79d0b62fa0072df58c720a03e0c1eb1e1356ed6505fdac1a5c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTailOrder:382",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTailOrder:382"
    },
    {
      sourceName := "OAI.PiExponent.FormalBranchContact.composed_logTail_strict_contact",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTailOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a1de65506137d7e348c0ed5d99b3d568e2054fe5a4f490c0ac9ce2d002b5afb5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTailOrder:1060",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTailOrder:1060"
    },
    {
      sourceName := "OAI.PiExponent.FormalBranchContact.contact_truncatedBranchCoordinates_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalBranchContact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a836f891d811e3ddfc6a93c5ebcf3a3d084d9f40fb63a7a02697fa9c86900958",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalBranchContact:1540",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalBranchContact:1540"
    },
    {
      sourceName := "OAI.PiExponent.FormalBranchContact.logTail_order_ge",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTailOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e7aa9ac070be108295cef4b0e51d562fd904a48193498e9380f7b086b6e46bc7",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTailOrder:236",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTailOrder:236"
    },
    {
      sourceName := "OAI.PiExponent.FormalBranchContact.truncatedBranchCoordinates",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalBranchCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8d660ac3b2665a6480c6d89ad9e62a44905ef8969ef746f08330f8e2cc5d3448",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalBranchCoordinates:399",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalBranchCoordinates:399"
    },
    {
      sourceName := "OAI.PiExponent.FormalBranchContact.truncatedBranchCoordinates_eq_add_tail",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalBranchCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "81fb288ebb62d5cffa0e04477bbcb1ff12a10b69900f87d9bb8459d56c2be2bd",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalBranchCoordinates:1221",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalBranchCoordinates:1221"
    },
    {
      sourceName := "OAI.PiExponent.FormalBranchContact.truncatedBranchCoordinates_not_all_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalBranchContact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1f2150d0becf3f8960a56b3491e8151264c4608235e60602faaf3f97ddbc9a4d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalBranchContact:846",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalBranchContact:846"
    },
    {
      sourceName := "OAI.PiExponent.FormalBranchEvaluation.branchCoordinates",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalBranchEvaluation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8716e47c271c986e70d1799fd274d4ad596ec5304cd614b3a862b3baf02401a9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalBranchEvaluation:280",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalBranchEvaluation:280"
    },
    {
      sourceName := "OAI.PiExponent.FormalBranchEvaluation.branchCoordinates_hasSubst",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalBranchEvaluation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7168f458010869d30e007644f33916b1abf6643bf77350ffea6f769523f95f88",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalBranchEvaluation:538",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalBranchEvaluation:538"
    },
    {
      sourceName := "OAI.PiExponent.FormalBranchEvaluation.formalJet_subst_branch",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalBranchEvaluation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1702e1b1c8d2a9c309c63ace7643e46c83d459d50db84a677744806a3a4aa83a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalBranchEvaluation:1735",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalBranchEvaluation:1735"
    },
    {
      sourceName := "OAI.PiExponent.FormalBranchEvaluation.polynomialFrameWord_branch_order",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalBranchEvaluation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "034f26cf3da101429c0e47bd5f48eebf1f594deeddcc14de421dbb19e4f5da7a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalBranchEvaluation:3168",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalBranchEvaluation:3168"
    },
    {
      sourceName := "OAI.PiExponent.FormalBranchEvaluation.polynomialFrameWord_branch_order_toNat",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalBranchEvaluation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "026bb6007bbb16722e6eb5657fe8e3147ba10dd3729b368643b20cd6abd13b3c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalBranchEvaluation:4318",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalBranchEvaluation:4318"
    },
    {
      sourceName := "OAI.PiExponent.FormalBranchEvaluation.subst_liftSeries",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalBranchEvaluation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "42b20c1b805e3fe3866d6cc039bddc6a3f604b3ce1b778cf2ec3171afb71d727",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalBranchEvaluation:1474",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalBranchEvaluation:1474"
    },
    {
      sourceName := "OAI.PiExponent.FormalBranchOrder.rational_order_subst_of_jet_vanishing",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalBranchOrderRational",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "64cc1e3655a790844239c65b6aaed9f45ee4822aeff7e6bbb6b792cc17fb3187",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalBranchOrderRational:1872",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalBranchOrderRational:1872"
    },
    {
      sourceName := "OAI.PiExponent.FormalBranchOrder.rational_order_subst_of_mem_weightedIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalBranchOrderRational",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9041a17947f7e39b111dd02075f22eb5f1a8b7c3e44d38efa1eaf220c780cf02",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalBranchOrderRational:3136",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalBranchOrderRational:3136"
    },
    {
      sourceName := "OAI.PiExponent.FormalBranchOrder.rational_powerSeries_order_subst_of_mem_weightedIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalBranchOrderRational",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2ab0d24b791b96b1c8bf8b785db88674072e2572477a8dac46b20fadffc236e8",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalBranchOrderRational:4124",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalBranchOrderRational:4124"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_010.jsonl"
