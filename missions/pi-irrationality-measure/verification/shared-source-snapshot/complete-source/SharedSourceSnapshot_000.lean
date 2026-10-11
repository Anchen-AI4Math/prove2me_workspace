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
      sourceName := "OAI.PiExponent.AddEquivSignedSum.map_signed_sum",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AddEquivSignedSum",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bbb52dc38dae71d31398deb616028975b845aa72d210278ee3431b82d339ca5f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AddEquivSignedSum:138",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AddEquivSignedSum:138"
    },
    {
      sourceName := "OAI.PiExponent.AddEquivSignedSum.map_signed_sum_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AddEquivSignedSum",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "76727c4c551985cbd01d52520cc9e98216726f6860b73ab5c98e86c2216bdeac",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AddEquivSignedSum:385",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AddEquivSignedSum:385"
    },
    {
      sourceName := "OAI.PiExponent.AdditiveKernelTransport.kernelEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdditiveKernelTransport",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2d585def3eeb34858262b88574327ccee968b852d96ce3a31e4568eed02e55e2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdditiveKernelTransport:284",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdditiveKernelTransport:284"
    },
    {
      sourceName := "OAI.PiExponent.AdditiveKernelTransport.transport_primitives",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.AdditiveKernelTransport",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f99c0400fa98992eebb13c13b1d0e0f6b7ec6749f62d0846b31ecf6eb99fa77c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.AdditiveKernelTransport:1056",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.AdditiveKernelTransport:1056"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.A",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fa91f693d18e4b1f80974b94186c63bd8f8dfb0dcad90be5dc89b4f5120f5028",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:7425",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:7425"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.H",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupPolarization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "79a6ca1c44f03bd0dfd70185cbdbacaef83f0ee654457d8ba5363b1253b568dc",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupPolarization:792",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupPolarization:792"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.H_ample",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupPolarization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c3114ba283b7bb189d5d1d1f09d515cc4e6dc927983c87f1d892c88b46d741e1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupPolarization:871",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupPolarization:871"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.Index",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5a8a2fc62e98180f3526e9b6a2b7677446ce93dee02853dadce2c28985d7be33",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:841",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:841"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.J",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8dda7cbd8287bfd52c497df70946509c0003a00b5fe7221fb1a8c5cc7bf849e8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:7498",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:7498"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.affineChart",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e01230898ac255e1e38e137ff731f643dc3f72c0896c15a4cc60ad417a7147aa",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:1708",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:1708"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.affineChart_isOpenImmersion",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9620d1e1ba4878a6c4ab1ce758919a855c1bb6a2fb4a2aadc194702b1a4727f8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:2009",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:2009"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.affineChart_over",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c2948deff44b43cc3aef5331c675da355178cb6f5599786ef74aac8dfb23c88f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:2946",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:2946"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.affineChart_quasiCompact",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c2b47fb8289abfc5348cca11c5222786aa91d05a77198f204c25f140addb3bca",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:2857",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:2857"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.ampleExponent",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupPolarization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e20af87b2c095ea9485581b63bdcd64dba0c31d9037bbc792ccfe014862270c0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupPolarization:634",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupPolarization:634"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.ampleExponent_gt_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupPolarization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bb8f60c6c117802bdf74624612542c62cbbc52ab4a5c032d452fbb543dcc93da",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupPolarization:696",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupPolarization:696"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.blowup",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4b5fb006f00c3a2d1a63f9e5d3799547cace68a0be1fd713e2989255bffaa1ae",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:6475",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:6475"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.blowup_compact",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "afe83f9e528ce52b71f5b585f732075a35c4800651cf63b21413d09066e279be",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:7245",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:7245"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.blowup_isIntegral",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0a9470c9c359299ea5065353989a10bb6dd61cb075d1fa9d77e762e674788baf",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:6957",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:6957"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.blowup_isLocallyNoetherian",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "abcc6de1935fb53596f1a8e3322b6d7eff1879e3969c61d1bb6f582239368db7",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:7112",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:7112"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.blowup_isNoetherian",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aeeb888787c5454393532e9e77d223905aedc003c68c68bebe7ecfa262df5006",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:7361",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:7361"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.centerIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6d0ec24ecfb778e122c23d8992749618660385c85c643a1230dd60d7bc39c97f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:3827",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:3827"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.centerIdeal_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6ca5272dc8ec597b9b470e91d611013b65b14f768925b6e9b62218cc38ffdf1f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:3987",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:3987"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.centerIdeal_support",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7c58e7e417e2cdaf2e0e737e0ffe8428e89643023db3436b5b0c7e25781519ed",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:4201",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:4201"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.centerIdeal_support_ne_top",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "40b6a5a1dc93b1ef02be546d244f114a72711fad9300ac383229b3f602495f51",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:6333",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:6333"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.centerIdeal_support_subset_chart",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b311160cbd47f571ab4669225fd6a1ed44ea58b52d459ad0731433b32a9af5fe",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:4718",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:4718"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.compactification",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f4149ffca67a5befee20842c25742dd12150155aefc7a34df863d22f0a1bfcdd",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:1313",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:1313"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.compactificationStructureMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c5ade5053b0370afc73371bd39e9c7a3b6b01534e045c2f44e436a0be4a431a9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:1420",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:1420"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.compactificationStructureMap_proper",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b200651786032b3cfe1ed8f91651c64d2da91ce97cb3a832d17e10631c62f3d3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:1552",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:1552"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.compactification_compact",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "306c1a4a9bc63c6864df2871ebd90ef65dbc9ce54dd2b78f1391d502cddee680",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:2623",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:2623"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.compactification_isIntegral",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a7beb8af12819ca0d6d354da01558413fcb31f87f654885b07c34533d13fa365",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:2361",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:2361"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.compactification_isLocallyNoetherian",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1a34a4ddc2cfd0c31ddbc5dc162781cb28b2a54d1ccefaf657bdb4fb184bb3ce",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:2454",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:2454"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.compactification_isNoetherian",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9fd8978b9f0ea92545f753e1c419f70ca2dec5cce2dd686a2753921cbfb83801",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:2775",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:2775"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.compactification_nonempty",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e82fc90c38ed042432dd96b86ecb4cc787bf3e6a2dbdc325c5def82219e6e281",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:2259",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:2259"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.constantIndex",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "61d7d45e86b115391ee88887902d5186291e3e8b8ab9e86eb716536116769153",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:952",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:952"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.coordinateIndex",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "204f7248499e99ab545735854e8bfa73b2473d4b6e57171e1636bd5bb2c00ad5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:1036",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:1036"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.exceptionalInclusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4de865df0e6948db813e33ef39b116e57bd8c2afe0dc0445f8085cd1ae2b8bc5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:7608",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:7608"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.exceptional_presents",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d39e165db64eddf1925c8babd33ed453e60cfd6843a36dc32aa59cfaa8243fa2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:7758",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:7758"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.exists_ampleExponent",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupPolarization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5e6344dce746fd014eacd6dd0e7cfaef94891d187c54e15f15abc6de73261f79",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupPolarization:376",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupPolarization:376"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.exponents",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b98bc1003071afc82f4c6d9362605c5177fe4a31055a4a9ed503c3702425fef7",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:874",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:874"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.hyperplane",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "116e798bcc37be9c17cc01268dcccf392f6201de7c0ca1c4cafda6310d95fb9e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:3293",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:3293"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.hyperplane_ample",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "73faeed36fec136d18e346939122ff5edc415f2752c67b43ca1c224584116cfd",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:3396",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:3396"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.index_nonempty",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "df05a07155d19d69feb3b31e39f7b9c006e3e10a1c20b2a11672644067ba2b60",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:1240",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:1240"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.interpolationBundle",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupPolarization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "686389eb23ccfaadfeef5e5b626e84d7a6714b34be8fbfe3058fd83293af9b3e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupPolarization:948",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupPolarization:948"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.interpolationBundle_ample",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupAmple",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b8c262cd5a8b6efe8e36063b38a93d57f9b1deab6cfc7237e085aebd85536e1f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupAmple:295",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupAmple:295"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.isBlowup",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "df310b977359f4217961c2ffa9c8f694312b8a6a3069f3d475bbd6152b966a7e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:7956",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:7956"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.logCutoff",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fe4069a05830aa3dae46b7262f63d6ebde3a052434c025304847ca713b4a671a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:3511",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:3511"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.logCutoff_strict",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "16fe01e8628d898960a06ceb02cb7cf6b51d53e3be40754292c5f95e1765cdcc",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:3623",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:3623"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.origin",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "746fa24bfec46d80435c55e62623798a708b285ed08d57cd329978f172ba9657",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:2130",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:2130"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.origin_avoids_center",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bf6363c5ac063998feac2b21457ced446cf387ae7287d5e5dacb1aa2babb4fe2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:5635",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:5635"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.origin_ne_center",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d787c38391a78b01db0aa8856a9e2ff3ca19c82e542e2ad7574f1bacb5af26d8",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:5203",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:5203"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.projection",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ae2c874b0aaae256fd1ebe2f4762fa28a9ba48c9c01694f00cf046f5c73d5a7e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:6557",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:6557"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.projection_proper",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1c4200a026719a487d527cfd25f57f69444dc1e09b68d10fc96711989942ee33",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:6776",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:6776"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.pureIndex",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7f04adca34d18c4b6efec2c1aedace4937c95a2ed4a74292c3b1ddaf60e22c7d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:1143",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:1143"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.scale",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cd675a2ab915fa1181cc8215974be182d65f2fa9278172847045452f520e7a01",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:672",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:672"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.structureMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "88e01fae89f9cd4f5b70735edae6d381caa117bddeb51f8022ca85125e65ed9f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:6675",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:6675"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.structureMap_proper",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "660e7aece3870e163bf1570b9b2223cfc3874d104e80f2247dbf08ebbaf06ef7",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:6851",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry:6851"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.uniformMargin",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupPolarization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3e82b568e22344bc80052add90a714df0fcbc96d2d116c92d6b316b96d0e3e8f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupPolarization:1021",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupPolarization:1021"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.uniformMargin_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupPolarization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "500b27c2521d76a575b4c15897ddda0914a03e581f4adfd8906a5d8950c35092",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupPolarization:1113",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupPolarization:1113"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.uniform_curve_margin",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveDegreeData",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6b3cac90cfff98b8f7d4d0a01d176c8f28b87f23ba09c2c92cf20b606da84f2c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveDegreeData:950",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveDegreeData:950"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupGeometry.uniform_curve_margin_of_affine_curve_data",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupPolarization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0587f6709b43bdb796e7e723388864a4cfb9b05cc83c756ef9d40f82fe9cd0a7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupPolarization:1247",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupPolarization:1247"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupMargin.AffineCurveDegreeData",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin",
      graphKind := "inductive",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "52e80b9dee7de10e4dbd498d17f99007b516d00344eaab477388dfc555cd4282",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin:501",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin:501"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupMargin.AffineCurveDegreeData.E",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cbeeb1144066d260d70fdf6847643273e4acfd6a43d40a7b9bf6790933e7f2cd",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin:501",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin:501"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupMargin.AffineCurveDegreeData.algebra",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0bc56565ce965c51c66dd4f47757de362d1a8a9f5c5d2e8fc149271dd967f02c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin:501",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin:501"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupMargin.AffineCurveDegreeData.casesOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c76eff74a21f099f3023539ae76930867634b55df4164c5e1b0e3dfc348191de",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin:501",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin:501"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupMargin.AffineCurveDegreeData.coordinates_generate",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "214ded90d2f1e3a20370716a093802da50d61bead0d461f5591a452cc2b594fb",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin:501",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin:501"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupMargin.AffineCurveDegreeData.essFiniteType",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "164756e83deded0fc84c265ef65d86daf7300b6f1ce377eb458c793872d9dfa4",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin:501",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin:501"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupMargin.AffineCurveDegreeData.exceptional_degree",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3ee3a662274a4c417e8caa701eac2a06f1b63aee6bb1114397c8026258b0cfd5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin:501",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin:501"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupMargin.AffineCurveDegreeData.field",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "19489fc6df7ec15c9ae1b9e80e6c173c527cff6bc9a9009b6337865f85d4722e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin:501",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin:501"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupMargin.AffineCurveDegreeData.hyperplane_degree",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c85d2759def136b2e003c495d05cfc8b04352726b0c07969d38842198fd76bb0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin:501",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin:501"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupMargin.AffineCurveDegreeData.mk",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin",
      graphKind := "ctor",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b0b7e8562bfac8bd5fbc57ecac8c3663b02d5dccb62e685e8a8f028e41970762",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin:501",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin:501"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupMargin.AffineCurveDegreeData.mk.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3bcf48e39029c87d58c975a6bc328146f42c9f40e875b38b4a9f23f70e09d31f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin:501",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin:501"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupMargin.AffineCurveDegreeData.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7c4cbcf25112036aac8c5d25d8e770739fd2b42161ec04519517153569322550",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin:501",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin:501"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupMargin.AffineCurveDegreeData.rec",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin",
      graphKind := "rec",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "77a19587e1444ce1035b4a3b50901cfa8bb259101ce09fb24d6cc3bf6b7f7dff",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin:501",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin:501"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupMargin.AffineCurveDegreeData.recOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fa2cbe0384af1e157303a5bc65b09288ad4fd28278ee1a710e207afa0030902f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin:501",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin:501"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupMargin.AffineCurveDegreeData.trdeg_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8a94907bcd9821022a379603e6c0a7f1805200f2d2136093c52ba68851ae1c4b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin:501",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin:501"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupMargin.AffineCurveDegreeData.x",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "820fda234dac287600a817e0268eda68f979390b81f79712f21f30eeff41df90",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin:501",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin:501"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupMargin.AffineCurveDegreeData.y",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ce2f0991fb6c366af4b57c915c9ceb095df6d3b682e325b781b199a5377348c1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin:501",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin:501"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupMargin.affineCurveDegreeData",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveDegreeData",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "639e74a7de85596571b5bc1faa3530bc88741b1faf7abef0827829a6bcdc9a82",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveDegreeData:335",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveDegreeData:335"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleBlowupMargin.uniform_margin_of_affine_curve_data",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c712c2db062ae306f25e6db484cbc144dae4c17bf8f7a36a65e153d7409859ef",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin:1148",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin:1148"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveCoordinates.chart",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b91ef4e9e27da4bb604d716bec4dfa0e615a3a88aa8e6a2f030ebc259f19587d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveCoordinates:1619",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveCoordinates:1619"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveCoordinates.chartPresentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "16f8d79c9e788134167c84821c06a319c3fd9d5b6b36dbb179f4eab481c2e1ef",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveCoordinates:1693",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveCoordinates:1693"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveCoordinates.chart_nonempty",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aa8a3201b0245c6bdee421c5308854993c6a6afe2884910828f62b6adb38c9d6",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveCoordinates:1890",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveCoordinates:1890"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveCoordinates.coordinates",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "583ed7eca2235fa0c7df35b5de67961f3588e93a8c12fd3869a3ec6f836c3932",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveCoordinates:2247",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveCoordinates:2247"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveCoordinates.coordinates_generic_map",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "97f866a4a2533406fac31373baf9e0e64f5380ac3ea9bed18d8efe9a443c1f83",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveCoordinates:3519",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveCoordinates:3519"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveCoordinates.fieldEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "96cfc2972685850490183140320e1f9713079265da1e4ec344ae5d97ff6c43d1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveCoordinates:1111",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveCoordinates:1111"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveCoordinates.field_properties",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveCoordinates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "afcacfd2ce3a13cdcfadb59b9b81c3fbed13963006d4518ebd604f21f1023969",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveCoordinates:2790",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveCoordinates:2790"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveCoordinates.imageAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d86034d1e6805d2f03e7dc4ace42867e67b90ffc5a255c575c6f84dbcdea92df",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveCoordinates:930",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveCoordinates:930"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveCoordinates.imageCoordinates",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e02ac218a6d9bad79501e249e6df769ded12702f79cb9e8fddca65fe636e35d6",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveCoordinates:2040",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveCoordinates:2040"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveCoordinates.imageCurve",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8a1eec07e91b3cb5b579d4ce07b1fd4aa4f4d2629bd87425a078c459b078acb5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveCoordinates:565",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveCoordinates:565"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveCoordinates.imageStructure",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "57cbc4e1df8216fd31f8454b38c49d0fabfcefbc8702cc97611636a5cef79058",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveCoordinates:684",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveCoordinates:684"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveCoordinates.sourceAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b0bfc3834a571a1adfd1f3db9bb9ef4aadf7db7902df65cdc9abced246ca3a65",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveCoordinates:775",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveCoordinates:775"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveCoordinates.sourceStructure",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveCoordinates",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9067c47da15ef2f127f1c3b42935fee4f390632c70196e751d03f6a840fe8524",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveCoordinates:626",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveCoordinates:626"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveImage.center_point_isClosed",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveImage",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "84dbfa33b81bb1a32e55ed2de8c1945d31f98f1896eceda4386fb71de23c092a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveImage:388",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveImage:388"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveImage.functionFieldIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveImage",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f31902827a56e54332f51e5e94048698d2b3e7f052ec6ca6eec5f41546049608",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveImage:1993",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveImage:1993"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveImage.functionFieldIso_generic",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveImage",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e668dc568fc64bb3ed76ddaaba756ba86215b6e28d79bee16f03762cea1f852c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveImage:2350",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveImage:2350"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveImage.imageCurve",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveImage",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fff0b0122c4b5ee76b3edeab71d4f01cbac318ff0005349c0f7b35aa6730e084",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveImage:1776",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveImage:1776"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveImage.image_meets_chart",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveImage",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "591c6db3c159fd7e12b7802b484916633da4abf1c00107f0d75df55c2794b811",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveImage:2920",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveImage:2920"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveImage.meets_center_complement",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveImage",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "99975c543862d4472b3337919808e4fe51a94b44d3e2ec47508fa2721b673816",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveImage:1235",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveImage:1235"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveImage.projection_restrict_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveImage",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1ab6df7497ebe984592999fdf0f712d274d5a809d3d95a012bd10747859814c9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveImage:1634",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveImage:1634"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveModel.ModelData",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel",
      graphKind := "inductive",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1a4769ef7f48c842548a93bc060a9a20e67e091306ce41cfaa07b63b60d1ffe8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveModel.ModelData.E",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "71a60cd6766148887611685c67c4f0d8e6c9d122573ba690559bdaa8b2369b57",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveModel.ModelData.algebra",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "19e3f058c0dc6b1111f469c97a5dec9cd75093b76815bc5dddc89d50b4c44de8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveModel.ModelData.casesOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "51fbb84a3ac1935c53806b30961ecf1460a5ddac94414ddc50dc7405dc3245ed",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveModel.ModelData.chart",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "594be1a5ad3b8c6f5cdc288a4d9af3e8d9c8dd77662ee29978b7bc7059057558",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveModel.ModelData.chartIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a1f7ddd499d35d04578f30a46acec8f4bb0e8c455fd48707511048fe11c21fc3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveModel.ModelData.chart_nonempty",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "38fded7fbf29af767de0b610f6d577e65fd67aae1bc534f17835485dd2a76cf5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveModel.ModelData.coordinates",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0da420a26a8e9648b6aeb2c85205b71e546dd9b45bf13572b5b26dfa8e36b6c0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveModel.ModelData.coordinates_generate",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9ae63dfddee5c6c4dca4d69e668d3dc85457f38cdf9b0781f9cb92d9ed06ffc6",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveModel.ModelData.essFiniteType",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1c8709db18e08d20468bb5c2ad55eaa517e9e1fc4e4b209659616475096842e9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveModel.ModelData.field",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d074c9d9ff3d5ffb8b3ca18847f0eae4ae7a1dd25b534fa8cc5b363d7c584c06",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveModel.ModelData.generic_coordinates",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3685f9ff842229feec98da851902cf58feadc7c92cb4e3370899628bb67c150a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveModel.ModelData.mk",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel",
      graphKind := "ctor",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "995c2968a7d341b7628c6a6814c9ce574fba9a2080eaa8fb4a790a16f3a0bee9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveModel.ModelData.mk.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "623d1074cc4b98075811e6a5466d6cd76f4489474004d844b3823733cefeb939",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveModel.ModelData.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d8fa4a48d7faf7afe17bd9d8d62f9dfc6b2eef81ea0fba2a99cfcbbf89a295b7",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveModel.ModelData.normalization",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ead0759092ccc5635aed3dbcd1a24cdc19230964aea492a5bd625cfa339db756",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveModel.ModelData.normalizationFinite",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3ea759f8f591d2a62cd8c3a54227f6c6d3734a33a573b38d6ae02a43bcff99a8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveModel.ModelData.normalization_over",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "051110d2bae0f0c60dd40880a27dd03c70151adfc2c11d1cdea890610022c863",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveModel.ModelData.parameter",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8a5de351ae0d455fec03b941b74c7b207c254b650820443fa269acf5e1e2f6e9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveModel.ModelData.parameterFinite",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bcd73b73388e28737eb6e93e3857e2082482408106897111a75f28ee3e5f6dc9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveModel.ModelData.parameter_transcendental",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b1895ffa7f8911b738c22ab09461d6fcbfdcf881c24682228a6e1be6962a6863",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveModel.ModelData.rec",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel",
      graphKind := "rec",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6099a64c51cab65b043e865730ae69c8b8561ab145c5049622b1683315c1e483",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveModel.ModelData.recOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6a52791b90c737d5d48495a6bac5675bbfbc90ea038195c8e66e661cfe28507a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveModel.ModelData.trdeg_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e7077f29781b885abd472a5ea2a7b4162dcc3b6ea6abc0a566659afb1269e002",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:406"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveModel.degreeData",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleCurveModelDegrees",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1fe6c7a401cc0799aacd99e6594b8b88416b750dbe9bd903172e76d7b64f2b35",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleCurveModelDegrees:411",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleCurveModelDegrees:411"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleCurveModel.existsModelData",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a73624b280928836ec208fbe2268deaea895c374b200a6e39825ff6527d3eed9",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:1682",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveModel:1682"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleJetPackets.formalPackets_surjective_of_jetRestriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AdmissibleJetPackets",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "924bd4ae7e55b51984735572de5029bcb2c5e3e3647d84ac97b3ebd9a6ae7e92",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AdmissibleJetPackets:1105",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AdmissibleJetPackets:1105"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleJetPackets.sectionPolynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AdmissibleJetPackets",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4fdf6eccccb547fdb190cfe46ffa744aa00ef338f34cb567b756afd31055fcf0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AdmissibleJetPackets:805",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AdmissibleJetPackets:805"
    },
    {
      sourceName := "OAI.PiExponent.AdmissibleJetSurjectivity.blowupBundle_ample",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleJetAmpleness",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b10dd84c3a923be044b055616cb2d68b2e1afd1fd541a817bcbe8e7a419448f9",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleJetAmpleness:567",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AdmissibleJetAmpleness:567"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_000.jsonl"
