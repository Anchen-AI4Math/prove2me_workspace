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
      sourceName := "OAI.PiExponent.ReesSheafCechBase.opens",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "efbb2cdfca246f5d0b9cd0b05a09ebdba4c3cb583c380c5be227e9143d5aa86a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:2125"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechBase.tupleHomEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "17cf15b6528101873dea1c1d50cad9338ae5400e260be923480505e81b32952a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:6886"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechBase.tupleOpen_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "82d2e2515b119817f5c5e6e92a7673ef61e3de51885b90ca2a781ada205da86d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:3723"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechBase.tuple_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "67bc0aca488bcafb23344f346795a7173916a1c26affe4c7ece0fec1740fb13f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:2210"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechBase.tuple_nonempty",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bd9d2dc146c45c14b25569598f98569d801820e34f711dc9a529bb01b8867e02",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechBase:2384"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechNaturality.chartHomEquiv_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechNaturality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2a00d0373a51cad950c0eda694cd7b5fa18afeb99a437c475e264fe0212d0779",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechNaturality",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechNaturality:2384"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechNaturality.cochainEquiv_differential",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechNaturality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "32f8bab70edcaf216fc448c695628c2d7ac5f7bfac6d6ee980fa4e9c8ed8a8b9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechNaturality",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechNaturality:5426"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechNaturality.tupleHomEquiv_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechNaturality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4a36a90bbfd13b1c61213aa222ea3b0228e9da52d0732b6f08201d76dc339f6f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechNaturality",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechNaturality:3747"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechRecovery.cyclesEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f4eea99d95a1f399fdc940f988f41fbe960e700d1464d42621a08cd10e68cb1e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:3027"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechRecovery.eventually_recovery_and_cohomology",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "927884fb7bee8763ac87003605a8f118f1fc8d54184116d3cf2eb96c50b1d536",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:9554",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:9554"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechRecovery.globalCyclesEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d6f3e7d74258a4da190f5364cd4879613f8165bb8feb85f57af7ce61b015d4c0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:4089"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechRecovery.gradedCycles",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "780a8a42c2798847ca67eb513b95e5eb0b79d2a873297bdf047e6aa70687886e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:1920"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechRecovery.gradedCyclesAddZero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f3c274838929d4881576ae1de31cc036601caccd7d02fd6f5f749c25959651c7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:2721"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechRecovery.gradedCyclesAddZeroClass",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a2ad91367aa1e39c656ceed938ea9cfaf0b93a2c07cd83fdd4ea6d9c1192daf0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:2864"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechRecovery.gradedCyclesGroup",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f533b169c4e9b55282807b633f9e6a1784b1a741a3e69119536fef8290445fff",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:2348"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechRecovery.groupAddZero",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "23d65aa26fd71eaed01751581bac9c34058c1cd37c925322f4f99211dc217daf",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:2463"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechRecovery.groupAddZeroClass",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bc91ce8645c4232bfa9be9d4c6dec293bee91cc2e8640e541a401b80bd78ee19",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:2587"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechRecovery.ordinaryAugmentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1a63459642d13a1d10328946c40429a1397675875321701a44d2aa2e18f53a34",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:3648"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechRecovery.ordinaryGlobalSection",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "78ae4d3c2ce32d9011c0a3e705bd652ce5146dae0527b6d32af511977335db85",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:4913"
    },
    {
      sourceName := "OAI.PiExponent.ReesSheafCechRecovery.ordinarySectionHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "46030eb04e9a2f2c4197e268981b23f621a1853cf49dc37453fa9f1b43bc600d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery:4641"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.RowChoices",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "98def1acefd799e100d4889e9d9f1fa635991d2726dd3f4bfa52ea6ce4936bfb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:10668"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.multiIndex",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b3aac1c3795f11100810fae4a6d0bfd4e6c7efc3cbbe706511f311ab771405c9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:2296"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.rowScalar",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "25e6fd5a6123637169e5cbf6ce748019c0a0e5bae583742016ef7ce609548f84",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:7272"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.shift",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f7078d28ae849daef40dc4a03ab4592117179dd459496aa8eeb2dbd42b4cd106",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:222"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.shiftCoefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c3966b6cd9032c86c56f70ab19acc6bf3d3c0c8a08f1a44f609b7caccc3bb5f2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:1019"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.shiftCoefficient_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3cd7188363c947a1ed33d6f8e58710b3e7481b4de0fd7e7e9cb6e64df316c17b",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:3766",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:3766"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.tail",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "864a826c6d1078095926e1c88bdca809500d27fb0702b18adfd18fc633157061",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:12851"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.tail_weight_budget",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ea64ea8276585ae8a4d58da51e0a26bbd5b8a78d150f4f32588bcd28406a3107",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:14353",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:14353"
    },
    {
      sourceName := "OAI.PiExponent.SectionImageIdeal.affine_map_imageIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "383099ae8d3cb6d84c04c14dd7ad17a5b6054db58884c782d8d60758760ffd73",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal:831"
    },
    {
      sourceName := "OAI.PiExponent.SectionImageIdeal.imageIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ce47c3772147018bc7d8fe3211cee6fab85b3cefa00cd30f77d75196d408747e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal:362"
    },
    {
      sourceName := "OAI.PiExponent.SectionImageIdeal.imageIdealSheaf",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e66461d353e21057008478068e6ec163c0b7d0614e144f70ddc25e96a9b9c82b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal:4891"
    },
    {
      sourceName := "OAI.PiExponent.SectionImageIdeal.imageIdealSheaf_on_frame",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6be849641ae52d679efbc86c9be19c55b5f801d79efbe3e43d247d41660180fb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal:6431"
    },
    {
      sourceName := "OAI.PiExponent.SectionImageIdeal.imageIdeal_map_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "195712e53abd127d8a70e567ed5dfe6a3f872f88f3c0df9fc679c136d6d2fae8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal:6106"
    },
    {
      sourceName := "OAI.PiExponent.SectionImageIdeal.imageIdeal_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a296eaae4b8d38f01710e54f9392d5ffdaffb1f9c54b6128108a21a03bf438eb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal:2040"
    },
    {
      sourceName := "OAI.PiExponent.SectionImageIdeal.imageIdeal_top_of_frame",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f5540f2d165bef6d3ee226e92ea249d86f078c793ac1c68d864b6d4d4fd84ee8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal:5262"
    },
    {
      sourceName := "OAI.PiExponent.SectionImageIdeal.map_imageIdeal_affine_image",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dc824d3ec0c972128e24f282d198965d93f0081784f900cc73b6eecf128a4747",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal:3157"
    },
    {
      sourceName := "OAI.PiExponent.SectionImageIdeal.map_imageIdeal_basicOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e9e4b57ba9a9db19e2a4bd7898bee4cff10c737fb2f58e30caa6640c440f5b5d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal:4134"
    },
    {
      sourceName := "OAI.PiExponent.SectionImageIdeal.map_imageIdeal_le",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7ed12fa8cdf788b7dcfb647dcf680a8872ddd13106a60a61931b50a8074f559a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal:476"
    },
    {
      sourceName := "OAI.PiExponent.SectionImageSupport.imageIdealSheaf_support",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionImageSupport",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "89fc8576697e5eea8358a502f1efa3b6c78a4a10a5082e599566095b23a4a60b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionImageSupport",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionImageSupport:1861"
    },
    {
      sourceName := "OAI.PiExponent.SectionImageSupport.isoOpen_preimage_on_frame",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionImageSupport",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cd8eb6130faa90411b5efa57ddac95bcf0221b7571c10a47ddc573ecd2a89f28",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionImageSupport",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionImageSupport:568"
    },
    {
      sourceName := "OAI.PiExponent.SectionImageSupport.preimage_basicOpen_topIso_hom",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionImageSupport",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dc3e47e5329993d1f586029b654bef012b5243106df1bb653e45096e315fd958",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionImageSupport",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionImageSupport:1588"
    },
    {
      sourceName := "OAI.PiExponent.SectionOrderDivisor.CurvePoint",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ed2ddc2240a4dbcdba02e31327eece24780f9da4a0b08fbdb8a62653dafa1fff",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor:350"
    },
    {
      sourceName := "OAI.PiExponent.SectionOrderDivisor.divisor",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e47f1a9b419a06a9e38ded61141fa70c55d8b3e98c44a3054776e9b640a1d5ae",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor:3102"
    },
    {
      sourceName := "OAI.PiExponent.SectionOrderDivisor.divisor_degree_eq_euler_difference",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "50a403bc1c216d4d639b0389e8abef2558f59236ade71d91bc5f0f051a86151d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor:3860"
    },
    {
      sourceName := "OAI.PiExponent.SectionOrderDivisor.mem_zero_support_iff_not_isUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d2644e696db874b962400851e880e49555003b06d9b4585b161942b3490614c3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor:438"
    },
    {
      sourceName := "OAI.PiExponent.SectionOrderDivisor.orderAt",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5f51c566c4c82a4811e9d3a452a3cc60d5a5ab5edcc59ab94177ecd29e7e10ad",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor:947"
    },
    {
      sourceName := "OAI.PiExponent.SectionOrderDivisor.orderAt_eq_zero_of_not_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "61a25bd687aff8a6d66765a258f52547d2d3af7b1dc8275529cab4060c112245",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor:1252"
    },
    {
      sourceName := "OAI.PiExponent.SectionOrderDivisor.orderAt_finite_support",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6ea9ec3a7c8228c598ae0502eac1698cf25759d18d2675eb62efa4d39a2cac8e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor:2178"
    },
    {
      sourceName := "OAI.PiExponent.SectionOrderDivisor.zeroPointEmbedding",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e32864c8f018ed6b4bb65f216fd3032c9ddad7c7dbf86b341a6ae8f81add76a2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor:1778"
    },
    {
      sourceName := "OAI.PiExponent.SectionZeroIdeal.dualSection_isoOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionZeroSupport",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e8257f12aad24ba723de9816c050a672c116f80863912f6ddece77ce9d5a530f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionZeroSupport",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionZeroSupport:424"
    },
    {
      sourceName := "OAI.PiExponent.SectionZeroIdeal.zeroIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionZeroIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f0c9501a66bac9b887d8a340a2f35a5e6d18d332ab7d1822e84f9121eb2e94b9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionZeroIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionZeroIdeal:634"
    },
    {
      sourceName := "OAI.PiExponent.SectionZeroIdeal.zeroIdeal_ne_bot",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionZeroIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "180e15dd0238fcdfcc619976fb6d9a7261b41796f500356dffd696b4e00c7405",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionZeroIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionZeroIdeal:1753"
    },
    {
      sourceName := "OAI.PiExponent.SectionZeroIdeal.zeroIdeal_on_frame",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionZeroIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cc9a5ecac9930c53a6313436dce123e5455468afa02854e394886104fe128ef5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionZeroIdeal",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SectionZeroIdeal:1020"
    },
    {
      sourceName := "OAI.PiExponent.SectionZeroIdeal.zeroIdeal_support",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionZeroSupport",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5643c4f39d1c4021f219faa0265640e9821ac24fc004a7306c14dbd174ad18b0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionZeroSupport",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionZeroSupport:1035"
    },
    {
      sourceName := "OAI.PiExponent.SectionZeroStalk.intrinsic_length_eq_of_ringEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "47e0d21d403f7ba77a6f750b4c5670845f8d81755b6e931464768c365be149c9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk:3564"
    },
    {
      sourceName := "OAI.PiExponent.SectionZeroStalk.sectionGerm",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2efde06912223d65aff4688a9b1a2116b3236a89a8b90ce636d37b1e9d3905bf",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk:2613"
    },
    {
      sourceName := "OAI.PiExponent.SectionZeroStalk.sectionGerm_ne_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f751f74913a245a9231400e8af5f7f703b5d464f786a7e58934224a4e60528a8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk:3856"
    },
    {
      sourceName := "OAI.PiExponent.SectionZeroStalk.stalkMap_ker_eq_map_affine_ker",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6f9798fd6b1432db2e6547beca78b45fe61ec8ba6971a42a17a8c3a0bddac6c3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk:330"
    },
    {
      sourceName := "OAI.PiExponent.SectionZeroStalk.zeroStalkQuotientEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "62d58532b9aff8d48f315684556368c4e3a1098e2f06a0998bc9e985991f9271",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk:2900"
    },
    {
      sourceName := "OAI.PiExponent.SectionZeroStalk.zero_stalk_kernel",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b8f7fd5caac7806319336db73e11a9d22aa93d986d8b88491faa900e13344f02",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk:1927"
    },
    {
      sourceName := "OAI.PiExponent.SectionZeroStalk.zero_stalk_length_eq_order",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4bd58f1c5372b6b1670cdb864a8de892b66f4e37afd08aae222354056064d9b5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk:4672"
    },
    {
      sourceName := "OAI.PiExponent.SeparablePointLength.coefficientBaseChangeEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dbbaa02a6be944e93706a3f909306a46c1600a3be3bb731cff01fdfe7367e446",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:381"
    },
    {
      sourceName := "OAI.PiExponent.SeparablePointLength.contractedPoint",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "990d5ef9af63a512915c624990e33f52c9e3cbdc830296d323ebd2d69ffa9d10",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:2070"
    },
    {
      sourceName := "OAI.PiExponent.SeparablePointLength.contractedPoint_isPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "facf7b03c8634dfcbc34d25c7a34919ba2704acccfb62999c8341db0b1545baf",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:2245"
    },
    {
      sourceName := "OAI.PiExponent.SeparablePointLength.pointLocalAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ddc9fb12c07cf10513a537eab4bb98dbf640a364e5a33c6d7c6e3a8a5626dd13",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:3126"
    },
    {
      sourceName := "OAI.PiExponent.SeparablePointLength.pointLocalMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c340fe7bec3f2fc18dfdf5a4fc47062cb32b917d16aec287c100c2cbe983cb73",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:2802"
    },
    {
      sourceName := "OAI.PiExponent.SeparablePointLength.pointLocalMap_isLocalHom",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f73053a60d53d40bb3d2a144cbb06afd4fd6d9099f8a021bba27fd7f7d00c505",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength:5116"
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
      sourceName := "OAI.PiExponent.SeparablePointLength.point_liesOver",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f6a1e26c574a56c441c7f19c2bc631d15beece0e4475249bb35450fe7b0a474a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SeparablePointLength",
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
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.SerreVanishing",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.SerreVanishing:522"
    },
    {
      sourceName := "OAI.PiExponent.SheafSectionGluing.glue_after_map",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SheafSectionGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "35c0e8be865b5e1b2ad3edc2599f3fd4d677ad7657c419a1177c4e6cf0313e12",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SheafSectionGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SheafSectionGluing:1248"
    },
    {
      sourceName := "OAI.PiExponent.SheafSectionGluing.mapSection",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SheafSectionGluing",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c3cf52b1aa39e5806f8ac773dbc6283e72fd57405f410b83835080c831c55111",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SheafSectionGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SheafSectionGluing:340"
    },
    {
      sourceName := "OAI.PiExponent.SheafSectionGluing.mapSection_congr",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SheafSectionGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6b576c39c6ceac49927bae9f9b650268b76774ebf1f61bbff89075d6f25bba76",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SheafSectionGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SheafSectionGluing:1037"
    },
    {
      sourceName := "OAI.PiExponent.SheafSectionGluing.mapSection_naturality",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SheafSectionGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "05a566696bee347336f92bcfb1fce56f070e6a0a97fc25cc91d01d9c25034261",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SheafSectionGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SheafSectionGluing:578"
    },
    {
      sourceName := "OAI.PiExponent.SheafSectionGluing.overlap_difference_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SheafSectionGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "11c5a4b30804e1357fbd59988bdbb0887fe38c94c6fc0766cb9f2c713f919d14",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SheafSectionGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SheafSectionGluing:3282"
    },
    {
      sourceName := "OAI.PiExponent.SheafSectionGluing.restriction_of_glued_map",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.SheafSectionGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4313720570105bc36d8000646314f950c16d37170e18485b74fe30382aa312a8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.SheafSectionGluing",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.SheafSectionGluing:2235"
    },
    {
      sourceName := "OAI.PiExponent.ShiftedFreeGrading.component",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3b34faba30e3f50c1d3916242624e1973d4b299427b372c61985185023af20cb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading:584"
    },
    {
      sourceName := "OAI.PiExponent.ShiftedFreeGrading.component_eq_zero_of_not_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f493e59c9ecf548e83f5c5d640b49ef7aa12ad362f25eaf4bde8a4a4d8341ac3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading:947"
    },
    {
      sourceName := "OAI.PiExponent.ShiftedFreeGrading.decomposition",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9a265e935fd43c90412106638661c83883b55b27d8778a3bb027d907118ac780",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading:3324"
    },
    {
      sourceName := "OAI.PiExponent.ShiftedFreeGrading.decompositionMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5a830ea936f7ea41075228d2749aec6741b6f882289ef304500159bb0de4e619",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading:1461"
    },
    {
      sourceName := "OAI.PiExponent.ShiftedFreeGrading.decompositionMap_homogeneous",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "14b5341143cb0e63eeb42d21c1e859da7a3739b187598e8152b1b823529528d9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading:2819"
    },
    {
      sourceName := "OAI.PiExponent.ShiftedFreeGrading.decompositionMap_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6d0144167ed1a1937575f63d2f259995e695fc26a4b46b1f0e5f77137a0b8e49",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading:2373"
    },
    {
      sourceName := "OAI.PiExponent.ShiftedFreeGrading.piece",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f65b38eef5b5eaf51c61eae14a414d61df58e961d3ad3ef986ce51bd90af0e87",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading:350"
    },
    {
      sourceName := "OAI.PiExponent.ShiftedFreeGrading.support",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0204c2345b1ac1a4a2cf7fc56a7f103c140c569ef161d66056b32a6da2dd5c4e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.ShiftedFreeGrading:777"
    },
    {
      sourceName := "OAI.PiExponent.TaylorRectangular.derivativeWord",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TaylorRectangular",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c6630fbee861d5798d833c8e0d93793e72fac6201dbeca875ef2013e85039bf0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TaylorRectangular",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TaylorRectangular:1818"
    },
    {
      sourceName := "OAI.PiExponent.TaylorRectangular.rationalFrame",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.TaylorRectangular",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d5f6e4679b7734bfe1c3e44d5a29b39d4b16114856153f81c864e7b46aa47bd3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.TaylorRectangular",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.TaylorRectangular:1287"
    },
    {
      sourceName := "OAI.PiExponent.TranslatedPowerCover.Ring",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.TranslatedPowerCover",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "06d660ad4d12d5f5bb9e45a8e5a56a8b98dce160ec18c94edac0293e09550e55",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.TranslatedPowerCover",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.TranslatedPowerCover:316"
    },
    {
      sourceName := "OAI.PiExponent.TranslatedPowerCover.basis",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.TranslatedPowerCover",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d8d604fbbf73085735f7bff0bcbd383d2953c209c75d12a63858fb3dae5c2e6d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.TranslatedPowerCover",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.TranslatedPowerCover:1688"
    },
    {
      sourceName := "OAI.PiExponent.TranslatedPowerCover.decomposition",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.TranslatedPowerCover",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c0828b2bc584a27737b7cd7553b698f7540d9fd9c580cdcf2362204634886d12",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.TranslatedPowerCover",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.TranslatedPowerCover:814"
    },
    {
      sourceName := "OAI.PiExponent.TranslatedPowerCover.instAlgebraMvPolynomialRing",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.TranslatedPowerCover",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fc5677e3bfe75e20b9c995114861c299e414091bc81f7fd5709be2e7222b6049",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.TranslatedPowerCover",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.TranslatedPowerCover:623"
    },
    {
      sourceName := "OAI.PiExponent.TranslatedPowerCover.instCommRingRing",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.TranslatedPowerCover",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "738b489b2ef4af208ac75d3833586355c9a0f8af3e9f389494599fb1cab3f664",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.TranslatedPowerCover",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.TranslatedPowerCover:394"
    },
    {
      sourceName := "OAI.PiExponent.TranslatedPowerCover.toPolynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.TranslatedPowerCover",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "358fd55f816a7253686322e30575ef9914ffee02c13245e82b7812a45c9dc164",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.TranslatedPowerCover",
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
      sourceName := "OAI.PiExponent.TupleCechBound.FullSupport",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e5c80a58aff98bc279b8dfdb8e09543e3013d1644958ad0e53a2406f0d35e1bf",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound:273"
    },
    {
      sourceName := "OAI.PiExponent.TupleCechBound.extend",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "391d52c60d61f83726e23fb3c94198602c3c9fa5dd658f7a80c4f1eca84a703e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound:924"
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
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.TupleCechBound:375"
    },
    {
      sourceName := "OAI.PiExponent.TwistGlobalExtension.exists_global_twist_extension",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f1ff3de90bf8914f10f29dcc68276b9e40515b474e4ec1fbe8c0ca1b4b3b4a0c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension:7157"
    },
    {
      sourceName := "OAI.PiExponent.TwistGlobalExtension.finite_cover_twist_gluing",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "473455565e299756281bf2bcf6fcd78e6850b731c9113f500820195805540fc6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension:4588"
    },
    {
      sourceName := "OAI.PiExponent.TwistGlobalExtension.finite_local_twist_extensions",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8a642a7abd7102863643f1f96bf7d70e10ba53719364e0b438e9ba49d2d5fab5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension:3131"
    },
    {
      sourceName := "OAI.PiExponent.TwistGlobalExtension.global_twist_extension",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "28e9b5133ab5eda407b3ea70d885d091e4575d0714aa158a3c179b957117339e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension:8374"
    },
    {
      sourceName := "OAI.PiExponent.TwistGlobalExtension.global_twist_extension_native",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6124c7ec233b50314710dbecf759c680d316b418a70d44ead919a2d3a957073f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension:9166"
    },
    {
      sourceName := "OAI.PiExponent.TwistGlobalExtension.local_twist_extension_ambient",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9168d226a405fbfa549c4da395e46f7bb477b18a0036ed1d3f87d2935c49af28",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension:1115"
    },
    {
      sourceName := "OAI.PiExponent.TwistGlobalExtension.mapSection_twistSection_add",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "03550ac5010c482d337676bb0d8860454a9d5111759ea0570e90e54acf141f57",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension:4152"
    },
    {
      sourceName := "OAI.PiExponent.TwistGlobalExtension.section_open_image",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "da88390d1aee233131c692d0e89997ba93f3a13bf8f032d4e3fe25e826f8ce5b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension:593"
    },
    {
      sourceName := "OAI.PiExponent.TwistSectionClearing.frame_local_input_zero_on",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5b62e06f7d76f5ee58204400456361aa13f689c81cd584bb197a8a31e43b79c2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionClearing:3032"
    },
    {
      sourceName := "OAI.PiExponent.TwistSectionClearing.frame_twistForward_ambient_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0681bcfc0ac4ae01bc9f75f2068584b538b79d124d7b7f967fd5d4e45b4616a6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionClearing:6153"
    },
    {
      sourceName := "OAI.PiExponent.TwistSectionClearing.frame_twistForward_zero_on",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1f85c7b06530e257c136aba2a14dd08b0a88b5c42fbfccc592321c98cfa1504d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionClearing:4414"
    },
    {
      sourceName := "OAI.PiExponent.TwistSectionClearing.hom_section_restriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f138f5c85b099a73a3963e4615de2d5d0118ece1deaa54a78588738a87f96cbe",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionClearing:5827"
    },
    {
      sourceName := "OAI.PiExponent.TwistSectionClearing.iso_section_restrict_zero_on",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9f6cae21463becacef9ff7d4d0c36653e87f70228540d0ff86416228e1dacfa0",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionClearing:2548"
    },
    {
      sourceName := "OAI.PiExponent.TwistSectionClearing.twistForward_section_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionClearing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "525ce551803589dc128293c719a7272dd18695b2156782dccf1745ff6217603e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionClearing",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TwistSectionClearing:7673"
    },
    {
      sourceName := "OAI.PiExponent.WeightedBezout.mem_pointIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3891fd6576d60c89ef72438c82fe21919c4da01cb59bf4ce35ef445f6798dc52",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout",
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
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:3425"
    },
    {
      sourceName := "OAI.PiExponent.WeightedBezout.pointIdeal_eq_span",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5a6b3f3612ef44c7008e9d22c20c2b87b03420dd407fb355d6037730040fd657",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:3870"
    },
    {
      sourceName := "OAI.PiExponent.WeightedBezout.pointIdeal_isMaximal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "46a79363a8f432af8ed95159f1ff8d4851f6ed1d0c5534bc507c75091a4682ef",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:3551"
    },
    {
      sourceName := "OAI.PiExponent.WeightedBezout.pointLength",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezoutBound",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9728588d4bd1a7a3d7cf7341ab0f01c065c471868029b321fc98a1d932f25c56",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezoutBound",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezoutBound:421"
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
      sourceName := "OAI.PiExponent.WeightedBezout.translatedPowerSubstitution",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "262f91de09f22b338433e7370e24fc8cdfa4f15630ca7e6f84be6d63acc06b8f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:391"
    },
    {
      sourceName := "OAI.PiExponent.WeightedBezout.translatedPowerSubstitution_C",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "51c8ff60c2cee362ebc0cf6f46a91b8cf44ee397b3220211c7fb3dd64c2705fd",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:854"
    },
    {
      sourceName := "OAI.PiExponent.WeightedBezout.translatedPowerSubstitution_X",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c037fc67336b81f2dc9fb17d30dec795424a978bdce0e239ae6d0b17e04fbab1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:607"
    },
    {
      sourceName := "OAI.PiExponent.WeightedBezout.translatedPowerSubstitution_comap_origin",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "04b0180b4b7060b6c49c0b2064c1d7ac5781daa18d49a9e5fdbd0b042e8146e8",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:5259"
    },
    {
      sourceName := "OAI.PiExponent.WeightedBezout.translatedPowerSubstitution_eval_origin",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b44a699d0ff0dc646981d0c43d4aa63185ac5e54610a0ae81b7c3a50ce4ff806",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:4963"
    },
    {
      sourceName := "OAI.PiExponent.WeightedBezout.translatedPowerSubstitution_factor",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "902db32018898b4c9544c0722212deb81c793a5a749f8e99d0526bcfa07b3225",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:2925"
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
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout:2753"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_018.jsonl"
