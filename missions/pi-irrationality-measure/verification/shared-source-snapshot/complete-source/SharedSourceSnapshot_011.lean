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
      sourceName := "OAI.PiExponent.FormalBranchOrder.rational_weight_le_of_contact",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalBranchOrderRational",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c9acb93be431d32351b340fe88e38bd5d68e07fdfdd151e8fee87542b2eb2230",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalBranchOrderRational:292",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalBranchOrderRational:292"
    },
    {
      sourceName := "OAI.PiExponent.FormalJetDerivatives.jetFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalJetDerivatives",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "69d22f80d0373ed91875fd9062279eb13aceab9353cc5f492ebf3081d03cce78",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalJetDerivatives:1003",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalJetDerivatives:1003"
    },
    {
      sourceName := "OAI.PiExponent.FormalJetDerivatives.jetFrameWord",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalJetDerivatives",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2bf100fb2298682e249db7e647067b8668cf7effcca018cd1e6a769c85021fac",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalJetDerivatives:2119",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalJetDerivatives:2119"
    },
    {
      sourceName := "OAI.PiExponent.FormalJetDerivatives.jetFrameWord_mem_rationalWeightedIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalJetDerivatives",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "823564cdb69dd60ff7b8ec52b710ea4141254e1fa8dc2baa15e9595fc3ebd8a2",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalJetDerivatives:2297",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalJetDerivatives:2297"
    },
    {
      sourceName := "OAI.PiExponent.FormalJetDerivatives.jetFrame_mem_rationalWeightedIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalJetDerivatives",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ffd27c0b9cb7f1c68978fa7c59c94467e167de7ea5b7852abc740aef9ab6952e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalJetDerivatives:1601",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalJetDerivatives:1601"
    },
    {
      sourceName := "OAI.PiExponent.FormalJetDerivatives.jetFrame_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalJetDerivatives",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "731315b3ca5c0dbfa8e5f54a664690ac4eda613abcb508b2ad97d2b4c05ab185",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalJetDerivatives:1425",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalJetDerivatives:1425"
    },
    {
      sourceName := "OAI.PiExponent.FormalJetDerivatives.jetFrame_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalJetDerivatives",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "37efea7636f9153a10df72d903747b2a9fd70d18e03e2e1fbf089acf5f40f282",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalJetDerivatives:1237",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalJetDerivatives:1237"
    },
    {
      sourceName := "OAI.PiExponent.FormalJetDerivatives.mul_pderiv_mem_rationalWeightedIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalJetDerivatives",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4ff34906b09772bc150a7339e0da5626fc13bb73584c3bc3ab7bef16830b0c16",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalJetDerivatives:638",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalJetDerivatives:638"
    },
    {
      sourceName := "OAI.PiExponent.FormalJetDerivatives.pderiv_mem_rationalWeightedIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalJetDerivatives",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6bbc08cb3b07ef810e780ea3526c5498617bfccf8ba6c2b1cb81620451714aff",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalJetDerivatives:280",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalJetDerivatives:280"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogJet.coeff_liftSeries",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5560967cec68f7f9c092c7e4ed7087899f373d4825682acff8398b22372c7dfe",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:510",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:510"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogJet.derivation_map_of_X",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7f997864ee5ad1d8bd66e3df918209e6abba85b46fae9c1652262ff9161e3d95",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:3339",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:3339"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogJet.formalJet",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "171b0c4d75d407c80819c4737daad61a712e62bd5bf260ac9e7b941171b54fb9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:2786",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:2786"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogJet.formalJet_X",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "847ff6491bd29f9061cfa764c38ee17dcc639c7f72d47d23142cef3f44d36a98",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:3162",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:3162"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogJet.formalJet_Y",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "921a3d169bc527cc431cf0eed2574d0759406fc8764c43c864cefc954aca4dde",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:3013",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:3013"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogJet.formalJet_frame_X",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2b8289dafd550b8f14c9cc2175976a572649fa28a31fabe360e2cd9ba4e5dabe",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:3894",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:3894"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogJet.formalJet_polynomialFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "535696d25e9fdad13ffe5c000c4177679bfdf1795b37f7e12b068071fb9f3583",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:4977",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:4977"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogJet.formalJet_polynomialFrameWord",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9f1a66d2fc09c7f77f9dae45614a2fcfae773360e129d08b4830b03ac5610e30",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:5329",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:5329"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogJet.formalJet_polynomialFrameWord_vanishing",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e885f333eef10afdaf77f96ad4ee3e446b5ba71001bbf6a8c555553de3be6df9",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:5744",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:5744"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogJet.formalLog",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "63502c455521d85d296e3e9e61cfd7decd76e44f78e2d20f99cc1048af622a7b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:1982",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:1982"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogJet.liftSeries",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f29ece8d37a43165610bdfd424af8f4c2f667a36b3035f9fd25dd2b41d0414c8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:351",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:351"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogJet.liftSeries_C",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5532c15f572e4e5aa6efde29940601a0e38868f153a9d37b554a318dc51d7710",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:1031",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:1031"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogJet.liftSeries_X",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "429172ec6e26020e5e4e3f3ac1013fd520ce54b7cc7c8eb5743bd13d76865d95",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:880",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:880"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogJet.one_add_X_mul_pderiv_formalLog",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5488ad05555580ffdb60b6fa267317dcd17b335d26337968dac541656552f71e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:2499",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:2499"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogJet.pderiv_succ_formalLog",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2eec663d5f94541862b6cd4704d1c8ebb0a0efe1d8aea90be0763315a960c435",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:2082",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:2082"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogJet.pderiv_succ_liftSeries",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "98fef6431b54775d79f403292e793eae9036416c6ef3073c552de246acbd5fb0",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:1635",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:1635"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogJet.pderiv_zero_liftSeries",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6055ad9d84089e2920c6035faffefe59e8537728eadf672a299ed8596a785862",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:1190",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalLogJet:1190"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.X_mem_rationalWeightedIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ab939267d023965bb36e7cd46023573b53f8fe31d471f942e24afd72ff915e73",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:7566",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:7566"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.coeff_logTail_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f7ff2343de0159bbe6f7c9ce66c06cf7e3d930a1233a4f353754eb006f06a802",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:12577",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:12577"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.formalLog_packets_surjective_iff_truncated",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "765a99a77fd142aaeb3df1bcc101b03f3293b01e0ffa931f7cb80e52a4d8fd40",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:17060",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:17060"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.liftSeries_eq_toMvPowerSeries",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f704e41dcf8eb20cf097719347c61a77410f7a334993d806c46186f0ffe28ddb",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:356",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:356"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.logTail",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7059cab353e93dad43da92d68b12ca3340ad8cdd10ff085bf7f7cb6fd63896a2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:12228",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:12228"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.logTail_constantCoeff",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6a2bec2a33cdf922bc0d9b4cd39d652b5078be38d988829848c1e38d318233c0",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:12375",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:12375"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.logTail_mem_rationalWeightedIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c79d445b1cd21881baff3970f2e78b670a8e5a26f64a9804ed1287b08967e0d3",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:12753",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:12753"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.packets_surjective_comp_equiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dd9ef97c4ffa017d6ccf4fa47bd4f6b556bc91ba986df88d24acae3484d513bb",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:15374",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:15374"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.packets_surjective_comp_equiv_iff",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "97f67c343af74a25134e3bbc24ce7b16a4bbc8e35b5887d75acd5528780756f5",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:16279",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:16279"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.rationalCoefficientPacket_eq_iff",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ca72225d9e769499eb473f5b1d87137d10704a15162224da79bd2ddafe35b19a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:8700",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:8700"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.rationalCoefficientPacket_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b8ce4fc72aab0455935ba18c33dbbe8f521ae2946c0e7dce27662ce7c9eb02ef",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:9129",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:9129"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.rationalWeightedIdeal_prod",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f33b3cab9cc487d18eade93b242ccbb9a27f685ca1af3c659db52c244d47eb10",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:5661",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:5661"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.shiftEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8cb02284393971870cf7f485d61e89645f85e1c3985fc20701eaa3f6d04e665e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:4823",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:4823"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.shiftEquiv_mem_iff",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7bc4fc2566a782b28c27eb6a43c1ab59486d0b70d66bbcd33deb73fed25c24e7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:11263",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:11263"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.shiftMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2d67a334735de0ce0cbd5ed424e3ab1712706a26c4f53aed8d8b814d651a4780",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:2212",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:2212"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.shiftMap_X_succ",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8794b72880dfe300220df557d61ea2c43e35837f6a08fc634ceae06c9edcecef",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:2680",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:2680"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.shiftMap_X_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c77127ce9c1356f570e6db1fed914bff084236e58727dac2d3128c25409bed3b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:2463",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:2463"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.shiftMap_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2af74c3d76107dbed36459dde797b8e5de723b838f089697160be4dcfe8239f8",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:3738",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:3738"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.shiftMap_inverse",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c00a365b065dc7b70a52037b49a0b2c46ec40e5c40edd78d97890cd122885cf2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:3955",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:3955"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.shiftMap_liftSeries",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f686ca0310c9dd295041cc4698d74212a592f7bf0aa0f9e3217ca9753c897f55",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:3424",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:3424"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.shiftMap_mem_rationalWeightedIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "09b3ae79cd663ff613fba39d696d837f7ebfdc2235baa115eb917706a55ec6e2",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:7928",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:7928"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.shiftMap_toMvPowerSeries",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "94254c5f5ca9b475c60da1226d1e961ebe8e37c57b3ddb143359a4909edf78d0",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:2948",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:2948"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.shiftMap_truncatedFormalJet",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c1454eab1a53cd667dd8876a0cdf7b3a495045845b7191ab04eb6462a76b764d",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:14165",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:14165"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.shiftVars",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b3ef70191454e1517227942e8a21eb5ef62eb87a92b55433d62b15511677feaa",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:1560",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:1560"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.shiftVars_hasSubst",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ad59535979bf669ba282d2622e0a8aa8eb1a059831af188918af89bedbe6278f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:1754",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:1754"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.subst_mem_rationalWeightedIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1bf053ca81251ec2cbf33428c957a43265d3deb25aac9046cadcf4ee2f5de964",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:6447",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:6447"
    },
    {
      sourceName := "OAI.PiExponent.FormalLogTruncation.truncatedFormalJet",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "db33108348d20b5b45e87b9d8562e28fba263be2e4a9e3cd5457a3b411dcb6f9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:13808",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:13808"
    },
    {
      sourceName := "OAI.PiExponent.FormalMatrixBridge.cast_finsupp_weight",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalJetIndices",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b27af738b4aa65ce0c0383fa1101769a6c3e578dd6154e162f25f171d31cefc7",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalJetIndices:310",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalJetIndices:310"
    },
    {
      sourceName := "OAI.PiExponent.FormalMatrixBridge.coeff_commAlgEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.NestedPolynomialSwap",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a118803808da3c5c14d6ae6a0dc4b473a239e6af161b781640cb1bda2b12ef40",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.NestedPolynomialSwap:522",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.NestedPolynomialSwap:522"
    },
    {
      sourceName := "OAI.PiExponent.FormalMatrixBridge.coeff_flatten",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FormalMatrixBridge",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "631b0bdf778591b4715c2555587cfd4d9e119664d9a12c7f3cf4c8b53c45b176",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FormalMatrixBridge:599",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FormalMatrixBridge:599"
    },
    {
      sourceName := "OAI.PiExponent.FormalMatrixBridge.coeff_nestedPolynomialSwap",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.NestedPolynomialSwap",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "14ef706bb4af6f6e05a6d6fbb1dd07dc85443f5e29b3a128d5ab00b788ddd7b6",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.NestedPolynomialSwap:1466",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.NestedPolynomialSwap:1466"
    },
    {
      sourceName := "OAI.PiExponent.FormalMatrixBridge.coeff_truncatedFormalJet",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FormalMatrixBridge",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8c2df832da92169b664259581abe2b74ab280d23e29507bab8c5327c673132ec",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FormalMatrixBridge:2942",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FormalMatrixBridge:2942"
    },
    {
      sourceName := "OAI.PiExponent.FormalMatrixBridge.exponentVector_coe",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalJetIndices",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2e0a7660da497b560e68d7c962a838bc85a52b47d2126a8b27086b1ae7810da8",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalJetIndices:155",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalJetIndices:155"
    },
    {
      sourceName := "OAI.PiExponent.FormalMatrixBridge.exponentVector_tail",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FormalMatrixBridge",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2bd9339a6e7ee3faf48c546f1a8c511d0dc6011db371855bf7588420384c5f56",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FormalMatrixBridge:3400",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FormalMatrixBridge:3400"
    },
    {
      sourceName := "OAI.PiExponent.FormalMatrixBridge.flatten",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FormalMatrixBridge",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "859de1334990532b2025cf57e370e53c5162a8237d72f60fdddd9a9c712e4cb8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FormalMatrixBridge:326",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FormalMatrixBridge:326"
    },
    {
      sourceName := "OAI.PiExponent.FormalMatrixBridge.flatten_C",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FormalMatrixBridge",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2161786480a6a77ff6e483e9a9e1d0e9f193c3728ee1dec78881a5c6f1c9404a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FormalMatrixBridge:1036",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FormalMatrixBridge:1036"
    },
    {
      sourceName := "OAI.PiExponent.FormalMatrixBridge.flatten_X",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FormalMatrixBridge",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c4a92b2b9d6466b1aef02a5de73f3f806b52b2addd9a39d13f08ed4676c8a091",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FormalMatrixBridge:1347",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FormalMatrixBridge:1347"
    },
    {
      sourceName := "OAI.PiExponent.FormalMatrixBridge.flatten_literalJetSubstitution",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FormalMatrixBridge",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6bda6b0bf13dcfa4cc4f7093f05b5a378fc9e9e7e7151ddd31a45d3e5fe60b45",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FormalMatrixBridge:2055",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FormalMatrixBridge:2055"
    },
    {
      sourceName := "OAI.PiExponent.FormalMatrixBridge.nestedPolynomialSwap",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.NestedPolynomialSwap",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1c5cd881bcf1741d8f6a5a5b2145b4fc2c87b85d22285cc5877d8839092c092d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.NestedPolynomialSwap:138",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.NestedPolynomialSwap:138"
    },
    {
      sourceName := "OAI.PiExponent.FormalMatrixBridge.polynomialOfCoefficients_of_weighted",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalJetIndices",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6dbc636ab6eca6ec3a5fa4122e22f5c3b2ba640289d8629643d0be8bdac1f661",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalJetIndices:2052",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalJetIndices:2052"
    },
    {
      sourceName := "OAI.PiExponent.FormalMatrixBridge.rationalJetIndexEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FormalJetIndices",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "08aa31f4252d6d7ae29580bf78ccb5c398f64889ce9eef1201963f9bb2bada70",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FormalJetIndices:581",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FormalJetIndices:581"
    },
    {
      sourceName := "OAI.PiExponent.FormalMatrixBridge.truncatedLogMatrix_mulVec_eq_coeff",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FormalMatrixBridge",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "02135cbb9981a5c273630814e74442a5f7e0d6c9d2fe0039aeb83bbf39b2fe11",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FormalMatrixBridge:4236",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FormalMatrixBridge:4236"
    },
    {
      sourceName := "OAI.PiExponent.FormalMatrixBridge.truncatedLogMatrix_surjective_of_formalLog_packets",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FormalMatrixSurjectivity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "564c4d495305461cf46c9a70d6385922fb6f386c0a0a8ee9efda1bbdb7188cac",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FormalMatrixSurjectivity:2629",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FormalMatrixSurjectivity:2629"
    },
    {
      sourceName := "OAI.PiExponent.FormalMatrixBridge.truncatedLogMatrix_surjective_of_rational_packets",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FormalMatrixSurjectivity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2b0e4850d1c015d8622c43e3182e2c3ea4bf0e262fc44e771efc0d6f344e1d10",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FormalMatrixSurjectivity:236",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FormalMatrixSurjectivity:236"
    },
    {
      sourceName := "OAI.PiExponent.FrameEquationFamily.BoundedWords",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameEquationFamily",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7bc7d1b2dc716bbe4b9a0cf8ac00238bb17963e86436e298b994f0ffdb852d60",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameEquationFamily:242",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameEquationFamily:242"
    },
    {
      sourceName := "OAI.PiExponent.FrameEquationFamily.equation_hasWeightedDegreeLE",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameEquationFamily",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a4308c62485b40d18aa1057d2866787f3cfe626270eb7eaf814b7bb2572463ce",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameEquationFamily:1821",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameEquationFamily:1821"
    },
    {
      sourceName := "OAI.PiExponent.FrameEquationFamily.equation_supportBound",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameEquationFamily",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bdc5fcd2292d3109d3bf3a56d6a93bf8453972b2290c6c5a1bc809c51f266436",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameEquationFamily:2147",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameEquationFamily:2147"
    },
    {
      sourceName := "OAI.PiExponent.FrameEquationFamily.equations",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameEquationFamily",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c7b3705f21b8156d8e6a048ab7c057518b09a405c12023e7762739e178925006",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameEquationFamily:389",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameEquationFamily:389"
    },
    {
      sourceName := "OAI.PiExponent.FrameEquationFamily.hasWeightedDegreeLE_iff_supportBound",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameEquationFamily",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4138bc7414bbc27c58eb2fa8fafc428fdc8ed2a14c9b09e44807bc1241e83531",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameEquationFamily:1521",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameEquationFamily:1521"
    },
    {
      sourceName := "OAI.PiExponent.FrameEquationFamily.monomialWeight_eq_weight",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameEquationFamily",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "45b619a4e9321fcaff2c8be4e80e3f4affe1067e79a920b7f0912d95c9b87da7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameEquationFamily:1295",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameEquationFamily:1295"
    },
    {
      sourceName := "OAI.PiExponent.FrameEquationFamily.span_equations",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.FrameEquationFamily",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "05966b87af30889a78046beda124feb2f86899c1bd214ec2bde34e5e6929664d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.FrameEquationFamily:875",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.FrameEquationFamily:875"
    },
    {
      sourceName := "OAI.PiExponent.FrameTransverseMultiplicity.frameRectangularHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FrameTransverseMultiplicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c622b72198506011476c82a1bd855afe78d1009a52df6c67091c61ceb50166e2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FrameTransverseMultiplicity:3399",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FrameTransverseMultiplicity:3399"
    },
    {
      sourceName := "OAI.PiExponent.FrameTransverseMultiplicity.frameRectangularHom_maps_residueIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FrameTransverseMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "20d9c9b58e364a816df79e41a582da4f3569201bd6a952d62bebb1f599fd4511",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FrameTransverseMultiplicity:3770",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FrameTransverseMultiplicity:3770"
    },
    {
      sourceName := "OAI.PiExponent.FrameTransverseMultiplicity.frameTaylor",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FrameTransverseMultiplicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "497588e3291e7b20aa13aeeeb017c834c674e7c6cc068d97879cb11a5648bc10",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FrameTransverseMultiplicity:322",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FrameTransverseMultiplicity:322"
    },
    {
      sourceName := "OAI.PiExponent.FrameTransverseMultiplicity.frameTaylor_constant",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FrameTransverseMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "599b740f22bb4cc3a06e8ebf9ebf4f2dc1153168585e5af58927738e5cfda81a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FrameTransverseMultiplicity:600",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FrameTransverseMultiplicity:600"
    },
    {
      sourceName := "OAI.PiExponent.FrameTransverseMultiplicity.frameTaylor_firstCoefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FrameTransverseMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7cafbf878a952b3243ec37ce222d3e5f49dd49bfe30fffffe92a2c98be548db0",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FrameTransverseMultiplicity:2057",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FrameTransverseMultiplicity:2057"
    },
    {
      sourceName := "OAI.PiExponent.FrameTransverseMultiplicity.frame_rectangular_length_lower",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FrameTransverseMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6b5d3945c68355f261dcd1027353fd20ea14894c8983e83ad1db4aa2ca8460f8",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FrameTransverseMultiplicity:4316",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FrameTransverseMultiplicity:4316"
    },
    {
      sourceName := "OAI.PiExponent.FrameTransverseMultiplicity.localizedFrameTaylor",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FrameTransverseMultiplicity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bed7d38db7eaa80c4718bae9cba2a245c17b506d38a3c3f1637ee2f0e879de9e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FrameTransverseMultiplicity:924",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FrameTransverseMultiplicity:924"
    },
    {
      sourceName := "OAI.PiExponent.FrameTransverseMultiplicity.localizedFrameTaylor_constant",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FrameTransverseMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0e0062d23f9f6bb63f9638f71dec7aa1598159b32835e57fa87ec9c8812aca7e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FrameTransverseMultiplicity:1630",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FrameTransverseMultiplicity:1630"
    },
    {
      sourceName := "OAI.PiExponent.FrameTransverseMultiplicity.localizedFrameTaylor_ideal_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FrameTransverseMultiplicity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "06e36201196e36c99473549ea160a7f19f8ac7234ad3c2cfb0e8451935d8b20d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FrameTransverseMultiplicity:2469",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FrameTransverseMultiplicity:2469"
    },
    {
      sourceName := "OAI.PiExponent.GeneralCartierDegreeLength.cartier_euler_difference_eq_sum_local_lengths",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.GeneralCartierDegreeLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1a0ccecba00843d29ff7cc1fa2febcda05ccfe998597cbb014a22b8f89847e17",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.GeneralCartierDegreeLength:773",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.GeneralCartierDegreeLength:773"
    },
    {
      sourceName := "OAI.PiExponent.GeneralCartierDegreeLength.finite_zeroIdeal_of_mono",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.GeneralCartierDegreeLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fe25973745d66eb0870adc3b25eca4a4c0a2cd2417ea034af995757af99fa10a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.GeneralCartierDegreeLength:2792",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.GeneralCartierDegreeLength:2792"
    },
    {
      sourceName := "OAI.PiExponent.GeneralCartierDegreeLength.regular_section_tensor_euler_eq_sum_local_lengths",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.GeneralCartierDegreeLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bcec1225c19f2c20353a0f7afa58e912e6469c082de3fce86396298ab1b30514",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.GeneralCartierDegreeLength:3529",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.GeneralCartierDegreeLength:3529"
    },
    {
      sourceName := "OAI.PiExponent.GeneratorsSectionCover.ample_eventual_fin_section_cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8fe3d2300dc879fdef107b6b1f58bce4f7338c9dd047a56b1e87316a60fa5b8c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover:7479",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover:7479"
    },
    {
      sourceName := "OAI.PiExponent.GeneratorsSectionCover.exists_fin_section_cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a12a245957b1f975911fa7464310769b8fae75b46871cf35f4d4467766ecc61d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover:6917",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover:6917"
    },
    {
      sourceName := "OAI.PiExponent.GeneratorsSectionCover.freeProjection",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b9010849a80580c35d98519914ad014da375ff1ec79cd7865a7168910008ae54",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover:903",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover:903"
    },
    {
      sourceName := "OAI.PiExponent.GeneratorsSectionCover.free_inclusion_projection",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a5e9b765f94a6124ba90c3f51eced2defb679329b25e4897f80fe894fd61097d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover:1092",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover:1092"
    },
    {
      sourceName := "OAI.PiExponent.GeneratorsSectionCover.free_sum_projection_inclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3789ac2efdead605b0453580fbe348b666aa98b5c3142da7dfe8d8ddd9615991",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover:1336",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover:1336"
    },
    {
      sourceName := "OAI.PiExponent.GeneratorsSectionCover.generatorSection",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "822b2e54ec78e4599cf2bfa13a0e01b3c3bd5191d9e9deb077cea9f384096c89",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover:5197",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover:5197"
    },
    {
      sourceName := "OAI.PiExponent.GeneratorsSectionCover.generators_sectionOpen_cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eb386ccf25fa2b680d654b92165f03f58125dd0170e931fdbb0d182cc5e6e877",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover:5345",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover:5345"
    },
    {
      sourceName := "OAI.PiExponent.GeneratorsSectionCover.hom_sum_app",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d1b4b65fea22272f9beb22c8499c5604e44417f368bcf1e587ee0df1d979c954",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover:1833",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover:1833"
    },
    {
      sourceName := "OAI.PiExponent.GeneratorsSectionCover.unit_epimorphism_cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b568a398ca2d27dba5b14ce3d225e6663cad8e6dd45387825754b5beb6c21ae5",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover:2266",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover:2266"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ActualLaurentExtFinite.actualExt_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LaurentExtFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "74ebb476d0096b84e25a93cbf5774e084f6f7a5e920cddcf0222b330aee4f0a2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LaurentExtFinite:2357",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LaurentExtFinite:2357"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ActualLaurentExtFinite.actualExt_succ_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LaurentExtFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "21df4d63b250a27dea728d4e5b8f0b309ef2af548d1b4504dc67d76b351c8a64",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LaurentExtFinite:1870",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LaurentExtFinite:1870"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ActualLaurentExtFinite.actualExt_zero_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LaurentExtFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b54f751d0e0da32926a95a20e0db09d2bc7a4dadca0473619ff73ff8c12d45f6",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LaurentExtFinite:1248",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LaurentExtFinite:1248"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ActualLaurentExtFinite.cohomology_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LaurentExtFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2a848adf9e3948b55efecfb6b7a5f806d82a7cceb24efbc8dd4da874144740a3",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LaurentExtFinite:2803",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LaurentExtFinite:2803"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.ActualLaurentExtFinite.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomSheafOfModulesRingCatSheafFreeOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LaurentExtFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a65a1df60912217a8cde7bbbcc736c558ca60d25a29c079d44c244343b8b1ffa",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LaurentExtFinite:958",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LaurentExtFinite:958"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.AffineIdealSections.equiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e19aed88d56dcc0c9f05d148f1522088016ea71b37e369d6afdcfad964cd02ae",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections:2869",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections:2869"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.AffineIdealSections.equiv_inclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "744d522234bf5e231d4279a6e0b5e61cd43eb5c9b7a4c15d80200df929a6a52d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections:3014",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections:3014"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.AffineIdealSections.equiv_symm_inclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "09173e94d22facfb83d51e64366b1a001db17b8231c31cbf134972ed06f29bda",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections:3216",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections:3216"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.AffineIdealSections.toIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b465e1e419f8d8129e7b8de71037651753f6421fc86e75201157f4ff11bdfc52",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections:1105",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections:1105"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.AffineIdealSections.toIdeal_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ffaa72404f2876d565040e2131bb685d9bdc6591c3b52ce4a34eb0d5c47b9b13",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections:1550",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections:1550"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.AffineIdealSections.toIdeal_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "db528d4e9d1c25f16b32d04f08c4d51ae442611153d3471e4878bcbee098a2c2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections:2208",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections:2208"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.AffineIdealSections.value",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e448e49be1023ed9c606d446581e019ab9744e3a461a17ec3ee0f70ea7a9c6b4",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections:371",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections:371"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.AffineIdealSections.value_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d6f22ebe7e064c1a7e4ec1e4c0bffa3bd01d28eff95bbf7170a4657ce8111e86",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections:527",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections:527"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.AssociatedPrimeAvoidance.exists_regular_combination",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AssociatedPrimeAvoidance",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "761f76d41be1033201160e18746bbdf77c11eb6e73ca54d4b266885d95cd216b",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AssociatedPrimeAvoidance:184",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AssociatedPrimeAvoidance:184"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechExtFinite.ActualExt",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "31848440eaf0f2fca8b46a1e6f3df0b0991d4f11d5e28b86e90b69b8644d37ca",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:782",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:782"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechExtFinite.LocallyAcyclic",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8ac30a755ad33bfc9b0430e86359c3a1aa5243f654bd9797661807519526be9c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:2053",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:2053"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechExtFinite.affine_exists_comparison",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "270823cf1faf9ed5a365cc7b93f2913b46122083004e6ff7cfd8f6aeb88b443a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:12005",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:12005"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechExtFinite.comparisonStep",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eb7dd37953cab71c7f74142cc1f59a4eb4a90841bf5605ac743a61ac32cf2651",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:4381",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:4381"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechExtFinite.comparisonStep_boundary",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "145c029cf9836d0d036483ef30773c7c2ec25547c3ce73e136a979bac5374b05",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:5902",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:5902"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechExtFinite.comparisonStep_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5da0c55f815b91fcc9a440ee09c6bcb03ebd785861627f2a5a3a9f07fc0dd2d1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:4702",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:4702"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechExtFinite.connecting",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fa3d6c0e9aa22dd93ff632d60976f50e4ad1b6ff3ca6b9cfa432f910202da18f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:1274",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:1274"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechExtFinite.connecting_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "559731b7b1dd8afc881afd19bb6678536f27d1a159c2a91a08eff3f375566e5c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:1773",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:1773"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechExtFinite.descent",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4b53ca1c539e4a0960c0cca7f3156165ccbfd057db2f5cf2265df019255e2630",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:2671",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:2671"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechExtFinite.descent_lift",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "db76c2438f2e6a4d1abe84433bdf430c18fc49ed732dbcd4dc357ebaff3ec027",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:3494",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:3494"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechExtFinite.exists_comparison",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eb70c7541d5a2f553261f788dec0a09c2d4033b611db9f4dc7326632bddef676",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:9223",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:9223"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechExtFinite.globalModule",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "709c4bc48e10d077a8930c9dbb1883912a3a011cea0a0e1c31020ae2416970ab",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:1008",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:1008"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechExtFinite.instAddCommGroupActualExt",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "72e5836d68a89d1c0fe9b93241a08daa2429e660bb65e628970c253e809ccac5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:879",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:879"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechExtFinite.locallyAcyclic_quotient",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e6931140438ef8bb8658692a97c2a71d07f4fc281fa1553d089b496ec64f8788",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:2231",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:2231"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechExtFinite.mkZeroLinear",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "20c44386b3516e4e3389f8acd24da34a53f35162ce3bf13f96529d21c4b202cb",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:6985",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:6985"
    },
    {
      sourceName := "OAI.PiExponent.GeometrySupport.CechExtFinite.scalarModule",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d71516cf76b204d5c1a13207d87793dfe6a267989e999a4dd2895a431d13f7f0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:1163",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.CechExtFinite:1163"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_011.jsonl"
