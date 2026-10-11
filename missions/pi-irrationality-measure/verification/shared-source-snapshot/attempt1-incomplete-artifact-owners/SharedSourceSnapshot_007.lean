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
      sourceName := "OAI.PiExponent.DVRBranchExpansion.expansionHom",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "284e85ce7a53d1b4de4a41faad8a895375971648da57b01bbc74d6e6a37d1e78",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:6452"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.expansionHom_uniformizer",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f8cfcc816502bb3ad3159c47c4c4e044943c71b5e7a79747b47b3118581cbbf1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:7105"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.expansion_add",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6e88bc7aee9bdc54d3722b5ba327bf4069735fa0fa06472058d59d66c40b0428",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:3342"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.expansion_algebraMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "972ba9e3f8a69604630859e22d620dc8745c18c70d306fd95c958443df31f9a7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:3773"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.expansion_mul",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bfee91b93f8f68adcb2a811949ef99b47e7c7283bff876b593d9c00a41b38b12",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:4760"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.expansion_rec",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3e3e2e7fb47887029a53f84030338bfcb5d05e3e19285e199af3aa59262df101",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:4065"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.mul_remainder",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "194d26207cce27e561254b641ef582de149da09d1f0bda8fa4cdba1dad48122a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:618"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.remainder",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2e7e21bdb71f340eacafce1f49ab86a08221fee3e364bc6b211f9f52c763fc0c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:538"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.remainderLinear",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c04419f3309caa5756194a7ba93be1a686942380ec1070dc7b0ebf0b66ae463c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:2065"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.remainder_add",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "19c3c485fa23e5cfe782b461013f0b649d38bde4e2fbcd978d553daf0e3d6576",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:800"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.remainder_algebraMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5a1c93e35ccca159ab8f7928e2a332c5ad35b3d5dd9fb408e0e55543c6f93e5b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:1436"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.remainder_mul",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "44cf80951288de98c0dd99d42e7cda1c382fc79ee28ab4457856df735aa856c1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:4425"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.remainder_smul",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a50781fc8bbfb2fb2f87ae41433a13bc5c173e5404d3a0dfe3e7c6e9a29d4fb6",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:1068"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.remainder_uniformizer_mul",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7d00b23d3ed92f0e694a8915ade369dffe901eea35a230a646e07a966dd5d1cc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:1826"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.residue_sub_dvd",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "15dcbdda23565c49f28083eec736ef623fd682ed66d0109688a0bb87cb5a1a1b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:336"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchExpansion.residue_uniformizer",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "818ffac987e6a6bd9ecd3cdb31f2e1bfae2c45f6dc3357932f54d8b34796d629",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion:1646"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchJet.contact",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchJet",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ea4e6aeb6ec7f7ccb8fbce97faf93e3150b2fb0e1dc1b49a7ee2b2563215cdc1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchJet",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchJet:3436"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchJet.coordinates",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchJet",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7fc6dda40b70b3536d5144ed3c170428f91bbf8775f86b94cb6e15a48a25a5be",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchJet",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchJet:952"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchJet.coordinates_centered",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchJet",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "17a07a1122c16e852cd0d2f9395e45be47c168e45dfb1fa03a7322c244d03d91",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchJet:1168",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchJet:1168"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchJet.coordinates_nonzero",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchJet",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "466459e401d3371c39b7f61b90f71349f241880a0dce43233b8e08fce4b5f514",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchJet",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchJet:2441"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchOrder.algHom_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "11fd756077779b6fd1aeef9218b37b4633c858dc8b7ae0750078e24ab5b56bc4",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchOrder",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchOrder:3825"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchOrder.algHom_order_eq_addVal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bcb70163fc179c9f993c8eb3563041ddaf773c329992600a8d7c8ad89849011f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchOrder",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchOrder:3562"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchOrder.injective",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "97e3b4d198399943b3831bc06feba5f859b1844119d3c3c4f71bfb1aaeb49194",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchOrder",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchOrder:846"
    },
    {
      sourceName := "OAI.PiExponent.DVRBranchOrder.order_eq_addVal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DVRBranchOrder",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "785089981b85c2e51c0ca8bc97c6a702cb82f2897b325c7f64188f2502c00aa2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DVRBranchOrder",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DVRBranchOrder:232"
    },
    {
      sourceName := "OAI.PiExponent.DVRValuationUnique.eq_fractionAddValuation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4d37f703eee9162ac77a759c7011b8d4030e8b4295c4ed67ea5bffe94ba3bda1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique:3159"
    },
    {
      sourceName := "OAI.PiExponent.DVRValuationUnique.exists_order_eq_uniformizer_multiple",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d57957a552a50d22c043ad2099f2ae3605e09c30a5d08ea0e4fb4ead45c1845a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique:1380"
    },
    {
      sourceName := "OAI.PiExponent.DVRValuationUnique.fractionAddValuation_normalized",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7c1e9ad4ea52b3678834e47da594888307e2e0f723b744042e5cead402468729",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique:4684"
    },
    {
      sourceName := "OAI.PiExponent.DVRValuationUnique.integerOrder_unit_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2834e426d834446b75b531054bf94b23179f12eb0dee5f0f344542c0e92e9679",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique:753"
    },
    {
      sourceName := "OAI.PiExponent.DVRValuationUnique.localFieldUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e91392c80c776612e50ec7e95dfc251eea119355b76cbca53d034c4e5c9965dc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique:420"
    },
    {
      sourceName := "OAI.PiExponent.DVRValuationUnique.localFieldUnit_val",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ef8117c3d43bbf8ee548ccb793d5caae5af33365b1e97ec0e69456b57e5b7331",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique:566"
    },
    {
      sourceName := "OAI.PiExponent.DVRValuationUnique.uniformizer_order_dvd",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4e3fee31cac9731445068f0aabfaa172aeb66ee22ff8bfe5bb79296779de8ee1",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique:2233"
    },
    {
      sourceName := "OAI.PiExponent.DerivativeIdeals.derivativeCore",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1b54af6773e21ea739d03d1c672eaf3be47e48a13b68f36bffe2ce4ee327a69b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:2280"
    },
    {
      sourceName := "OAI.PiExponent.DerivativeIdeals.derivativeIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0f498135f40e28c319f397b3a322c6a2dca0ed51618fc1343c23e637ac7f7e4a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:1290"
    },
    {
      sourceName := "OAI.PiExponent.DerivativeIdeals.exists_persistent_derivative_component",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aa414a3ef0cd2087f72226eb4d0d46c962b3e1c4c5c63ae586e2c55f43fc6eb5",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:5334",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:5334"
    },
    {
      sourceName := "OAI.PiExponent.DerivativeIdeals.wordCost",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dc4355c9d45cdf02187fd4bd7b042cd5d3eb94ac29e27dcafcaab0a13d8621b7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:743"
    },
    {
      sourceName := "OAI.PiExponent.DerivativeIdeals.wordDerivative",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1140a3db04690e9d57c37850c3d7719286b78d0d31e94f5c72a1bfe75b6d8bfb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:328"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantAnalyticBound.log_norm_sum_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.DeterminantAnalyticBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4f78a2336e845707f3bb1710d89946c4c325aec273b4337b82649f02b0c3d382",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.DeterminantAnalyticBound:5774",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.DeterminantAnalyticBound:5774"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantAnalyticBound.two_alternative_exponent",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.DeterminantAnalyticBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "790d81aa4b88b601cf932eb074f6062554a268cd91ff9874a5e655182b97604c",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.DeterminantAnalyticBound:215",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.DeterminantAnalyticBound:215"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantContradiction.AnalyticAggregateStatement",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7ff3637cf679513fca377c20a6da7b76705a89d07054edb7118e964250f295c2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:4587"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantContradiction.Column",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d254537eeec190a12d8ff0ce95e052da1f9a345a68563291203cd32d1183cf36",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:1487"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantContradiction.FixedData",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "121224e4a278e93b89f07eebcde883b9f77b943b3aceef201dd82c735f11504b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:677"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantContradiction.GlobalInterpolationStatement",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e631ecae0b10fd1511cd84cc1be084d3af8290c040ecfcfe3c84c4e65b48f642",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:4399"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantContradiction.Row",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bd10ee494ae0d521d267cc74ad5168ac0bcde905a98dffe617198da4ffb4cee7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:1321"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantContradiction.actualMatrix",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c596b19a391f6687196e929f09f6f23874aaee52b5c16552ba7a24037956af5c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:1637"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantContradiction.actualMean",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a6f2fbaca54c085fa54fb9973ba9b8a2eeb74448de555ce17d611b4a24cbe42f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:2320"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantContradiction.actualMinor",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a28bf2bbe2b0e0f95c74f5a963edb00130a88fb224af1797083b0bf5a059a47f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:2042"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantContradiction.actualRowCount",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fc4e13f893e5ea9a1732519e8ea9cdce538421d7c2144c95b981b41f3b0f3329",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:2482"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantContradiction.collisionConstant",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dd1f0febdc04faccd4b5e374f91928f327ce4a31bbeeebe0c7fb60c41e15115e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:463"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantContradiction.collisionLimit",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fbf7d66e807b98c2e715deb8230c9208758198cc7902864abce81c926c009172",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:2978"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantContradiction.collisionRate",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1f70e5d4eb8de11f7c1960a315425afb988ce51775deb690dc5c0918c57cac46",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:2788"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantContradiction.finiteDenominators",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "07144205a73259ce61ef5436ceafade674483476fe4e75c2f61202ce36998ade",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:887"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantContradiction.finiteNumerators",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "881d847e91466f3a5e9d02b59051247374f1ba923f2b2a731d861488931a6110",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:776"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantContradiction.lowIndexCount",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eb03d7e80ca2a1823b7b96c2950a8bd2f905759f858124a87c92c25c762e329b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:2593"
    },
    {
      sourceName := "OAI.PiExponent.DeterminantContradiction.piEventualLowerBound_of_interpolation_and_analytic_aggregate",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "071b2762d25f6606437267981abc9ee7f506c7669b0d545066abff460371606b",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:8308",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction:8308"
    },
    {
      sourceName := "OAI.PiExponent.EventualLowerBound",
      expectedModule := "OAI.NumberTheory.PiExponent.Statement",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b829022a3b694653fd6c8327a850dca3a59721e08cff08304aec78466feb5af2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Statement",
      commandUnit := "OAI.NumberTheory.PiExponent.Statement:451"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.affineGammaEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7210b221d25c7c17fa41a5e3652cd6e467975d8ad8dc2e7f27aa462959b26f5c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart:695"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.chartFunctionsEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0d0b80d4a29572d725d6697285a9142583de307c808858cca4d0dd0757a6f97c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart:881"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.chartFunctions_naturality",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "568fbb536fa6ecdb78691e2f0c65ae828109bb48526714ed7c0a652077e8e677",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction:1504"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.chartOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "25880177313b2d0153e29d41c25fb3ab0f77b29455ffdc920bb2b311790e2f41",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart:610"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.chartPowerIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eccd8d4995b1143d4c6e387c971dbceefc8439e21ba2e6552f0a00463a225111",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart:998"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.chartPowerIdeal_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d537c3cd87ad32c4d0a2d560aff065818af46b57bc1d9abf3b74b43765e71615",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart:1174"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.chart_square",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "561aa495e82976a1ac4e974710e4740c45f69a497d5585431d45c0d63df5360f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction:1072"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.exists_representedSectionsOpaque",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedOpaque",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "078305cfda3324326d6bea63aef832f57cffe881ff48750977b4a982b48bc351",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedOpaque",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedOpaque:862"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.functionsOnOpenEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a193ec4ac67ba6e81dd4a1728f6807f6311e7a07c4d4a40fff81b8972a74e525",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction:1360"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.functionsOnOpenEquiv_naturality",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e87145881472e9de6d2bc3acc2e8aabbc0a3a0e54946a64831214e026dd8109b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction",
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
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart:5297"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.idealMapAddEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c595556f99bcc4b74a2aa29c607f9fdb856bc14876d9335d745322942deacf3c",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart:3522"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.map_chartPowerIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6232bfcdc9481715ca8cfbedd2a684f4676337dd1959164fda323b3cd6734295",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart:1987"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.opensRange_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e1d40e62f43a6bb3554fadf44d49d169c67dc3ce48527f7b25f1906bb9584382",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction:856"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.representedSectionsEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ce1c94169db2d9cd81f44d5bd223280ada3c9d8ed94e912720d24d8c861cfe89",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction:5345"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.representedSectionsEquiv_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f8dba668df3d06aea03db02084b17047553a3cffb58a6e574be0716fed60162d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction:6893"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.representedSectionsOpaque",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedOpaque",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c6e72cb4a0bce32873a9f14f80130b5e7c7ec62301fbaaeeec5229df51252e2b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedOpaque",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedOpaque:1086"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.representedSectionsOpaque_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedOpaque",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "92e855a5a51ac51e77c7d872939a18cfde3b2d65afd604c93486927b33ed107a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedOpaque",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedOpaque:1525"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.representedSectionsOpaque_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedOpaque",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c76d32fc07209138084b1d3885ea2f01e4fda44ee36634be849a3b14d082024a",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedOpaque",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedOpaque:1283"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.restrictedInclusion_value",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3f58d108f1344dee839f32ccdb3737bec8174bdeabfa4bb4ae5e3a5d159b3589",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction:3497"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.sectionsEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0ef45270f0a574af2b57af6b21332d5a3f3d89a9ba7eee179ca0460528ba2219",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart:4154"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.sectionsEquiv_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fe016cde209fd183d3342fed09cda0b7b64ff1627f0a13cd84fc539417c5f198",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart:4758"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.sectionsOnOpenEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0733b9670f425c187456c7531119d94bcf53912f09ff987bed7a4f8fc12ed607",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction:4539"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.sectionsOnOpenEquiv_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ab5c9d3057fec81f9062154c17255e141374da9648644c9dd77ffbbb642aa256",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction:4785"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.sectionsOnOpenEquiv_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "005434052a5e26b2aa386d2d6ed6d31de5bb1ef0440879b15d21170205607f82",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction:6062"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalAffineChart.topIso_restriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4cecc5be85552e55681485b1b6989c0fa389d958fb8a90e724a4b15c342fbc4f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction:2417"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.admissible_degree_eq_neg_contactSum",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7cd4ae10667f6865a1693d6601fefd64277239dbc127018c692adfafdd523d2d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:24124"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.centerMorphism_eq_centeredLift",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "16830e3e098b671afc382f8ee7cef0fca4bbf3a3002343cac6c5e0c56e1f3f72",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:12536"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.compactIdeal_comap_ne_bot_of_generic",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6045a3c59af28e73488d29c441b2ae7c14fec218fbeb177809e5090c04f73ed2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:11032"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.compactIdeal_degree_eq_neg_contact_sum",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fbac95d070a2a0ed56c96f1a4ca38560c2c69b331384048e6f721df105a786b9",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:19103"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.degree_eq_neg_idealDivisor_sum",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4ef6a75b8dedc4f11b8656ee1a80f8e1b27528d2442082187f203bdb1d8bea49",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:17974"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.divisor_eq_localIdeal_length",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b25001590537fe6b93a7b07ea7274e48b978639bd269bbea841f6475cc1a9446",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:15490"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.idealDivisor",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "40756300b124a5894f21841ffecba8e837bb19845cead01c07bcbdd8f6b9c6ca",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:17095"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.idealDivisor_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7ab4c33ca3d19cfc342a76fc739fbb51470aa45e64ca0f3fed8b9a5928832fc5",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:17321"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.inverseSection",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "05af169dc32b99b6b70d70624da2960d49e51271f929e7023c06d9ca7e28efd3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:1167"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.inverseSection_zeroIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5a265193299a2713e7544a75c9570182f3e003d91e274ccec282a0a5f20ce2cb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:1341"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.inverseSection_zeroIdeal_eq_comap",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "623d8d903cf6bb8d47c4281280897a38971750b7708383460b48f25f2860cc5f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:2723"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.localIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d83be64c645d4863ab481c51d11a2c448e2833e30e433f7af6ee6059b9916364",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:6885"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.localIdeal_compactIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ca24c4f4691d974daf691836c87cf2c52fb5a08b0352f7fde531b8ef7991de09",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:7730"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.localIdeal_eq_top_of_not_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "32aa732cb12bada5bbc831d097487b774c92af8fe2e295367d1b3fb0f7a4af38",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:8358"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.localIdeal_length_eq_logContact",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9a184eb26a92d5fa3534d8224385e47223e9386f644b0a734b8885de55a52f23",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:13401"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.localIdeal_specIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f59f061194ab780604021d33a406bfa3970c8312989087eb12e46faeb0fa5b8f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:7112"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.map_powerIdeal_eq_top_of_transcendental",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5f14f3fdf495207589ba9b4a1ce2f47ce3a77cc3e240633f04cb52ab430725a3",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:9165"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.pullback_inverseSection_ne_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "44c12ac3108a631c77624099b191a85a3bd594daa55c3f6e67081fccbc97105b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:5648"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.pullback_inverseSection_zeroIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d2b0aec9d933f832d9ee811ff9cb62e0e76d1da6a18ff84300a83b6418a32dae",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:5203"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.zeroIdeal_pullback",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e4239e607b3246e7822b69320efed54304f0cf312381bb7dbc563682cec95645",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:3139"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.zeroIdeal_spec_top",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4de3636247a6930a8f9d6b81ac2dd3a4fdb4cd23ac35a1079c44c5ce05fa5f3e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:6090"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalCurveDegree.zeroIdeal_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4f78693c0ad88da01df82d94d0ffb81b12350e531ba3d97991285973cf1b510d",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree:4735"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalRepresentedTypes.Frame",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedTypes",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "75180fd31196c1810ca116026a7dedbcd97734a7b8f167c2e6bf6a03838e8c60",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedTypes",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedTypes:402"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalRepresentedTypes.Sections",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedTypes",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "05fc6fa8abec24fe7fb3933c20eb5bc0266983277c39522c0f0df24db0729ddb",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedTypes",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedTypes:626"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalRepresentedTypes.frame_nonempty_of_open",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedTransport",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4f100ef035603b3d6a289dc5c74ceed3738ad460a4172d5ac5f52c15e313fedf",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedTransport",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedTransport:545"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedTypes",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7c0320ab0b347a1a8848129f1249ef003d4a5e49bc60ad6393592d25fd157463",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedTypes",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedTypes:802"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalRepresentedTypes.representedSectionsTyped",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedTypes",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aa6a80b68efc6097b4acb336103ebe9f7179bf5c9f0beb13bd4e55558086b20f",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedTypes",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedTypes:1347"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalRepresentedTypes.representedSectionsTyped_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedTypes",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1c681922f04e570edb0e2a2b3a43e2b4c7110dd9839abfbf8168417202427fee",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedTypes",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedTypes:1508"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalRepresentedTypes.representedSectionsTyped_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedRestriction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d175d3c001aa4c86a8913ac85962d9bc96094a586ffb30004413e1ccb144dfec",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedRestriction:1531"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalRepresentedTypes.restrictSections",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedRestriction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "07d4b725c586c9cf55d8137d49747495dc638ca178c3a44d37a30a4ba60fc0ec",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedRestriction",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedRestriction:612"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalRepresentedTypes.transportSections",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedTransport",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "03c2f603594d9fb8bee1ccd1459a5629fa16c98be41a42f2d533502443287409",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedTransport",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedTransport:735"
    },
    {
      sourceName := "OAI.PiExponent.ExceptionalRepresentedTypes.transportSections_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedTransportNaturality",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0e21df20969cb3e393cedeb638ed4ed737ef5c444b12d0dfee9c862a5838bcfe",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedTransportNaturality",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedTransportNaturality:609"
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
      sourceName := "OAI.PiExponent.FiniteGlobalPresentation.affine_kernel_exists_finitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "139598ea3ec42b92ea76d83e50e063bf6c18a5acca0f39ed1433f21f9c9948cc",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:7720"
    },
    {
      sourceName := "OAI.PiExponent.FiniteGlobalPresentation.exists_local_finitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d01a24a9a520936bdc146df489132dc59b3b4ac276b03447142ec8ace56985ff",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:11248"
    },
    {
      sourceName := "OAI.PiExponent.FiniteGlobalPresentation.finitePresentation_of_le",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "542f61824804bbdb4b9643d71d11a318c28ccf88a393a9e5c274c287724fa87b",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:13231"
    },
    {
      sourceName := "OAI.PiExponent.FiniteGlobalPresentation.free_isFinitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "453d5dd30dfae445c9177ab69ef2f4d8525ab3e12929301f682e152d6752cba2",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:9434"
    },
    {
      sourceName := "OAI.PiExponent.FiniteGlobalPresentation.isFinitePresentation_of_affine_presentations",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a8b0873a32e667ecea68290ac11324b67cdf5d71789b70f90f2973b668ddd703",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:6737"
    },
    {
      sourceName := "OAI.PiExponent.FiniteGlobalPresentation.isFinitePresentation_of_localPresentations",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a8a567948a56d9d5c467ff9d91292f8977e5040b33b6fdb2d45915356735f442",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:12428"
    },
    {
      sourceName := "OAI.PiExponent.FiniteGlobalPresentation.isFinitePresentation_of_locally_iso",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9ed99b63d5bbcde40ff690730d8db2ab2dc83f8e73857532a694b37a7ce4f6f7",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:14541"
    },
    {
      sourceName := "OAI.PiExponent.FiniteGlobalPresentation.isFinitePresentation_of_presentation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8772411ccfaeacc4c9c14a084b3beedb6d4f6cdbdc22fd1e89445c7f29534184",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:1581"
    },
    {
      sourceName := "OAI.PiExponent.FiniteGlobalPresentation.kernel_generators_isFinitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a4049c2a8b662d2f90cbcace2a2a2c17a196abfc897b10c1726eb11ada44c41e",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:10901"
    },
    {
      sourceName := "OAI.PiExponent.FiniteGlobalPresentation.kernel_isFinitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4a442ae403a4621d0959c2b16479b6e364d6b43c3cbc617ef654aa579d861097",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:10063"
    },
    {
      sourceName := "OAI.PiExponent.FiniteGlobalPresentation.moduleTwist_isFinitePresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "15c878a8ab8bcee039192a6ac9d546508c5ee0e0fb5ca74f80cf9b3362165c49",
      ownerKind := "definition_bundle",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation:15289"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_007.jsonl"
