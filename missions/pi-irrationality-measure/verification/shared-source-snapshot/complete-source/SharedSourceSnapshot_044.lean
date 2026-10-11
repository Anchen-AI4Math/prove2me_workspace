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
      sourceName := "OAI.PiExponentSeshadri.RestrictionCohomology.restrictionGenerator_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "63fa0350b7a5dc4d2179636e24eef59ae66584d44c07e07855c4bfb5035c3b38",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:49049",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:49049"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.RestrictionCohomology.restrictionHomEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b05ecaf5468a84f451feea7cc9c001574091aa03ac1c4820bb64b76c591531af",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:47449",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:47449"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.RestrictionCohomology.restrictionHomEquiv_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a74099c87d653e29070d87a8bd01d662f161ea6934b09f02edb9608726e4f6ff",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:47780",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:47780"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.RestrictionCohomology.restrictionSectionsIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "90e7f19c32793b7803082ea2d510659291b87631a71229f1620bd3d8861b2953",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:47275",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:47275"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.RestrictionCohomology.restriction_ext_bijective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c21606ad1d9b55e117609bd3720d7455ca61a9ef7b69c8e1043c3bae14417849",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:49366",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:49366"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.RestrictionExact.restriction_additive",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "06ef4bb608fae9b10dd6770c7d5a01f7cbf70ed6dba94353c3c95ba7a792e611",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:40348",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:40348"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5e8e7cee6b6d44bfeaba8d761bb5849c23bdb83fcd9c36f39bd0b714f05e83f4",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:40854",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:40854"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.RestrictionExact.restriction_mono",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "06011a83eacc1673418194f69453db2f64ce609aead1191a8a3a1b93ef7c4ccb",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:39771",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:39771"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ca852020688804db4747ef9ace9e164a9bb6bfee48e76dbd4e35824b7bcdde9f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:40660",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:40660"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesHomology",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5855aebaeaf4de2c10a6c1219e0283f7bfe7345682e6ea8d92060482c4b49565",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:40467",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:40467"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6dc89d9c807511f9b411e67fd2b0a5c467deb0bcaad0d088b8c5b2c4ad55a09e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:40189",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:40189"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SchematicExt.basicOpen_ker_eq_bot",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cb537175018abf3da4b1907cf2b8615689bc03e99b14ed45edcea3b158b641c6",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt:3852",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt:3852"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SchematicExt.ext_of_ker_eq_bot_of_isSeparated",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "713452cc90e4111ff231a051c0a9affe41fa9112e11dfc99868c397f194958a7",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt:2722",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt:2722"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SectionOpens.isIso_of_locally_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "304009d759e2a2d88c0d7e335f5cbb6898255f6d1e64d81d7d65540dbf628865",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens:1672",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens:1672"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SectionOpens.isIso_of_stalks",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "49762c9baaa9ebdc609ea0fcb553867584535eda9c49ec9957caf5693991ebac",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens:325",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens:325"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SectionOpens.isIso_restrict_isoOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bc28ecc904486a31f7525400dcc8add63a49ae0a1480dceb558556543ff70f96",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens:2318",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens:2318"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SectionOpens.isoOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0cba39bdaca8741dc586d9e4f258be03117c134dd68de04b4b1cacc3f89eafed",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens:1978",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens:1978"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SectionOpens.isoOpen_postcomp",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9772b51125070d715dd79f5e22d48d1d66db0c576b37c302839e76f254d02675",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens:2769",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens:2769"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SectionOpens.isoOpen_precomp",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fa423a21edc78572e5ad495f04cbfba9fcf0a701ce838216872f681164a43b25",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens:3429",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens:3429"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SectionOpens.isoOpen_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "20bdf0324c41c48eb69bf9dd1ba60272d727825b0ab2620f4d83f7dec8856d70",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens:4087",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens:4087"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SectionOpens.mem_isoOpen_iff",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ccbb6819fc27d23f37a9735e1fbb3a405396c59a67e7839baba00c6c01ff27ac",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens:2102",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens:2102"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SectionOpens.restrict_isIso_of_stalks",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7385aa7ce76f7b5eed69fc74cc7427055bc5cf5b05863447ab2215d5327130b8",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens:1314",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens:1314"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SectionOpens.stalk_isIso_of_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a12b1e372674c0479f0dfaa1e6306ae76ff47198ea461cfaaf2f8907757a1e2c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens:846",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.SectionOpens:846"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SpecMaps.coordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4301a2b8abbfea12a0961aa80cdfe710cbb7a3f17acc1498bea85aade67a9908",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt:253",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt:253"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SpecMaps.coordinate_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "25137f31eb39bfdb6e5fd295cf2167789e74cad146fcf3166fbc4a930014bd5b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt:541",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt:541"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SpecMaps.coordinate_comp_spec",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fe20e29d16fc046ce61971b25fec9d4177ce94be958daaf2976ce6450d1e724f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt:823",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt:823"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SpecMaps.coordinate_ext",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6b487202e08daf9e32755458babb2a49f99e8db858ebe9071d9177be1a58a872",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt:353",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt:353"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SpecMaps.factor",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7aeded39c6a0d04cdd6d32294678bfb84a3e421e6ff1fa4d2b6f0da10417e02b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt:979",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt:979"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SpecMaps.ideal_unit_generator",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d8378c6dbfa45bda551f57df11ac42aa96a54e2c04513ca12a8d624174d08e8b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt:1971",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt:1971"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SpecMaps.isUnit_coordinate_of_preimage_top",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c7a49b2bbba1debfe3c29d8d365e9758910edeadace5f7f7af7a0dece7b468af",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt:1746",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt:1746"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SpecMaps.isUnit_of_basicOpen_eq_top",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e92702a01a567419279b6439803bdf895f54cb8b918cbbc34a28de2a932c7328",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt:1485",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt:1485"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.SpecMaps.preimage_basicOpen",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a731ea68c486d4d14ba3ba729b85462df909460e44b2db4b8b56505a4998356e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt:1206",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupSchemeExt:1206"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorLocalization.map_tensor_right_unit",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1f5a5cc4ebe7a9a99961ae662c7c48c72eb44a5b414b5ded684eb2595391d7ab",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws:1017",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws:1017"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.adj",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7b0d039cc3ee836277ae561ef200991582e8d4d8ab4ba6a04fb09d42009728f2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:620",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:620"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.assoc_inv_pure",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "679d55587d10805e37f54e0d6c5ff30bc0671cc48535dc39c11e7f3579be76ff",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection:3459",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection:3459"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.assoc_pure",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "481fcb7b12c26fb9d2affe614f35892e20ac657283ddf88967999bfc223a2e7e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection:427",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection:427"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.framed_pure",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9e12c895dd32a0599894f425ed076f59464d5d3008721b1f8095b1d891a6a09a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen:2230",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen:2230"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.hom_ext",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1bad842f6d93d0fef92a536d9e00eb15956b6f6b6fab2470057dc28bc922f0c6",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:2758",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:2758"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.local_framed_pure",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "de3f66e7da0c34084bba764bf148abe6e17e5a0ac59f4d623e1d26c46faeab5c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen:2767",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen:2767"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.local_section_coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "01e79eca76f1101c419cc02b29c6ae3cebb609c47f2cd9357358985c76d5bb43",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen:3587",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen:3587"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.map_pure",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4da92ab649df8f36e3718002abe29438531c8343e0383777a3cf6015f7848bb2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:2339",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:2339"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.mixed_value_open",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0eec806367de26472b0bb3054149b932889edfc882c18fc333461f00555c9b8c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection:7196",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection:7196"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.mixed_value_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "84d90e5e06d9efca71e3ad456a8f3060a7611ebb0d1ac0ee4da79f8dd8769585",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection:6677",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection:6677"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.openSection_tensor",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8f3309c94122acb0c7e50bdc10649e7fc645496a6581135d20831e84ddf00d91",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection:5599",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection:5599"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.power_succ_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a010c15309b9e00c2fed23f0ad26f0935622ec134a48310a9509c1f09f6f1cc2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection:5062",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection:5062"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.presheaf",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "98bc8c4b3783048c4f860eb342fc13905015f8d9db7134a81ba0959e94c22a47",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:510",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:510"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.presheaf_restrict_pure",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "28c03c9e48217900becd3d19271f8b1608f9a5eed6969dfbfd92c5fc624183fb",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:4201",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:4201"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.pure",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9178a87ba60fc9315f8bf74024424da610870c441e03c42e835b8139843da7b6",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:748",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:748"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.pure_add_left",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1df9292956a7dce32eba05e15cf4f6094b19f1fd5df8498099b3ab659a4bdac5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:960",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:960"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.pure_add_right",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3eba1798ff872ad3e5672eba53416d0081d7d1cd1e84ab5b23deeb24719b9bd4",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:1209",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:1209"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.pure_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0e8f8650081cec725eaed136d76930a1f90e5f11e4b87acf836f6e22d0d800d2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:1978",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:1978"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.pure_smul_left",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d66274dd13e35c842c1475876f0879c8f80a97a8ae85c1fd36d4588741c48a29",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:1459",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:1459"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.pure_smul_right",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4f4da444665e5f0d2cbc699423c865264a32c9da14e9630ca46fdf3608f776fe",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:1718",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:1718"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.restrict_hom_ext",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "74e2e256d04ef88f464f62f5ca8cd67b08b64df02569b850ebc25c4c937284ab",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:6713",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:6713"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.restrict_map",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7f10c4351494261ae2338ec9ec946efa5bdb0358b99ba09b10fe875b6b2e00e1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:7523",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:7523"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.restrict_pure",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "587e32e6db376726fd683e9c4c7422ef146f5bddc1cc40370b1f5edc2b0f59fc",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:4664",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:4664"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.restrict_pure_inv",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9cf87121c9cefcb5b10f73d04f8e218a709b32b3c2920db6b5e59367e4b0edac",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:6171",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:6171"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.right_unit_pure",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cd8b3926370225c31258869c58bc89eb80021ad3168fe2ee2424f7c4c3dace3a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:9246",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:9246"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.section_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0b76ed148e94f800cb058555eb17cd0df48220b9b789faaa44517a48794c04e1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen:1189",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen:1189"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.section_open",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5d67150719e49d22829093c896abab98ed4df94de9295de93ce081fe1295c5eb",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen:4536",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen:4536"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.sheafify_restrict_unit",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "adffebf5906c6112c58a8e6417ab895b5f223b34b1697073173497c76eefe7de",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:3066",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:3066"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.tensorSection",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "724e277b14f9a8e0e9055d5f2e5eb662b9d31812baa984ade8e2457ca9b9e171",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen:1025",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen:1025"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "97e3277c3e507b069beef6b711352fafa099675aa208f3504f76fc6a8ee5395f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection:6403",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection:6403"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.unit_inv_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7be4c7808c11b05ab659036f06f9acfcc1eb64edc25d0e6fc952a60fc7ae6810",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection:4448",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection:4448"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TensorPure.unit_pure",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.TensorPure",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ac6e16f57c5bdbb8b10b9738072f6fbb19794a3bd82a6493cc826f41475c7273",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:8732",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.TensorPure:8732"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TildeExact.map_mono",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c202b834415e6608fafe6471c64defef21d7009483cec9ce1c0af258411b53c7",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:24417",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:24417"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4835d47897caa93be4ece012a3a02a73f8a074ad9596dd7133acc9c968d6ac4c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:25105",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:25105"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TildeExact.preservesHomology",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "01bf5fa811905a8431365d0ad3656846cb3de462f7638277e62ddd22d8c3bf99",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:24963",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:24963"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "422a3044ab1d12fea549fe6afa523ffc48103a767f70b07ce2fb503584d1283d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:24848",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:24848"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TildeFlasque.flasque_of_injective_global",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bd887964da3e9e26c302e62b57d91c3c9b8fd3774eced6e7a5ad22f12336500b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:23298",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:23298"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "332db7c12b8574e7380029e942f2a66c17beba5ea658dad97feb25d67a2c4b14",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:23812",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:23812"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.TildeFlasque.top_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d1529d42354b6406faba88914a7b9e8d83447437ea5b65a4e96720eb72fd0419",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:22225",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology:22225"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.UnitEndomorphism.app_eq_mul",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "12bb5390c471f2e23d670414f664f0771659ef68b38f57e257e5149eab934c61",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:500",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:500"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.UnitEndomorphism.equation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "679e95b7170c465bfab5e2cdfcc0f2ed97c30b50a897abc6bfe51d99f5375a87",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:424",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:424"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.UnitEndomorphism.equation_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a43323f49e0782e276a7a87b544926a80a5226ce3f98f15f894a30a3ad5e2c55",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:1171",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:1171"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.UnitEndomorphism.image_principal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a601e8df45c44ff6345a5d6bc07a72742d6fb18e51379e19ad9a73bf4a297956",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:793",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:793"
    },
    {
      sourceName := "OAI.PiExponentSeshadri.UnitEndomorphism.unit",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "68c73dbdd1892420d1ddf474c6036ddd684b85a9fd9850c4c18f8d1dc19b444b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:308",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal:308"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coefficientAdjoinRootQuotientEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1a6b31e891dfe492bd37fe139fd829e6106c76d777347168523f0eb69446a1ee",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient:2498",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient:2498"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateCoefficientSplit",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "25da8da8f12eb53bfc17eafdd30b8a586e515043ea85034a7d301e136ccbe7ea",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient:409",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient:409"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateCoefficientSplit_X_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e4b98c4493fd19a58490e5ffc3f46302b62b7cf65965288391b5364a6684b930",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient:651",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient:651"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateCoefficientSplit_aeval",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8847ae4d9f71eb9d07740804366550c7db5866f4acc4c482fcdf0d8aed3938e3",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient:1255",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient:1255"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateEval",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ac4414a563cf7a3b1d25b04daaa4435c3c5844f0c5a3e0bc06accd6e6fac4fba",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:354",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:354"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateEval_X_none",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a6c580f6f64d6398df4d9640f0bd57db70e2ea0595ad82222a7b9ddcb0a04d46",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:648",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:648"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateEval_X_some",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "74130ba22f02bc45fc077a225b5704aaa4d2e537fffc5862dd28c7d7eb989d89",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:772",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:772"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateEval_homogeneous",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a6b83b163d16bbd36b96ae93d98a32d5ba80c193b91e761a335f8e1be581c77e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:1353",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:1353"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateEval_include",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2d4322c18232d94bad2428a06fe459c27eabf64e72e9319d2aa7d165cf9b3188",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:900",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:900"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateEval_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "995d811dab5e56b3bb406786758e01993dfcc6b0e4fe5950156b202fc4458561",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:1185",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:1185"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateImageIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "476d7073256559e1b1a947832bb48c4f07d897d4560e51360135f05471a17d67",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:2070",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:2070"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateImageIdeal_homogeneous",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a7b61e8cc581a6f2534d4de2835a174cd8cc657ebb06813b994bc0c2275377fb",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:2885",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:2885"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateInclude",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2006c87f9824bdb2f78f8c92e862b68989f7baa173b5fac97f04234b7da9cd76",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:514",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:514"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateInclude_eval_mod",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "31db06db28e98de00db09becad8caf93d606004b83d6a0fc34a878a3781b2231",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:3255",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:3255"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateInclude_homogeneous",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8c19bf82abf0997721759868dcd644b698d2b518617685a0fc38db66f75ad164",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:1895",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:1895"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateInclude_image_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "989b8b60d27440e65f7329324894a10c62433ad37aedaa231ef744e8054f2fdb",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:4081",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:4081"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateMinpolyIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6959d27b98cf1257ddbd51cdd53692529c8bc0f5049ed97a61a98eba1a0bf2c4",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient:1917",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient:1917"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateMinpolyIdeal_le_of_mem_contraction",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "25b6d95d8ffe78ccf4571e3c2ec2bf0c35e0db49bcbc5952f1f787ca82100f53",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient:4902",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient:4902"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateMinpolyIdeal_map",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2f31269663c30ad8f7be6b1e1ee19ddf8a6927455ae75b5e172aa7608cf4f6aa",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient:2097",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient:2097"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateMinpolyQuotientEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d008c4987893d7e9a50db2448f80dfca2a17083efdacbcf0a2736e67901df729",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient:3170",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoordinateMinpolyQuotient:3170"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateQuotientEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "da111812f0d010fec852e6c028629bde5bcd0268cbd2d6e3708c015fd73147c8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:4930",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:4930"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateQuotientEquiv_section_map",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "35246904d26e6ca59bd23498e336fbcfdd4e109fefcde5f77028a11436fe081c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:5867",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:5867"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateQuotientInverse",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "36090d6697b96a83e0f72e0d7619ca0786aeba77c530e17115519230ec1a6781",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:4614",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:4614"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateQuotientMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "24d6c637508c7559e58a82cd561dde8f8eb480ab56d7a6ffb2937e654dfe4e92",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:3805",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:3805"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateQuotientSectionEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2f739afd052d93cc5b9cc75980d36bfcb790153a0cb4dcf4daec034978b40dc5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:6824",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:6824"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.coordinateQuotientSection_finrank",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "57bbeee8513df40d63b4f9482109dbf042f03ed548225b184b34ced465f26064",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:7195",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:7195"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.homogeneous_ideal_map_of_degree_preserving",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6649777ddd74fe3bfb252b57c9d643a8d27ccea25f695f639e5ed70c3ff9edf3",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:2220",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:2220"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.renameImageIdeal_homogeneous",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9b5303545f53984c6ae273336a2988cb855333e0151cba12b578ef048bac0c9d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:9572",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:9572"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.renameQuotientEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d00d629a16329419695660f5e27522f9d4b7e2e779e15dd6e4392fc1294772aa",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:7575",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:7575"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.renameQuotientEquiv_section_map",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9de7f02400a11adb0bb41cf349f6768f0bca9d4a1b4810dc22e683855c4eacb3",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:7846",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:7846"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.renameQuotientSectionEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b41198106807ef82d296f2f7a5072fcc9aabefdf2e527df502414f80438fa997",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:8874",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:8874"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W08.renameQuotientSection_finrank",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c83d9869f9fe0cf3d86443fe167eca8a8ec222b825af0db6490ce6e10bf4a2d6",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:9235",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading:9235"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W10.TriangularLocalParameters.firstCoordinateContraction",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "deeda6e6bbc00c8967fe27142d2155993fd33f1ffcffdf170d9f32df790609df",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters:8251",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters:8251"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W10.TriangularLocalParameters.firstCoordinateContraction_isMaximal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "78de7aa2b9642f542caf398db831213083c0ea53a4c45844fc3451d775d52acc",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters:8386",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters:8386"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W10.TriangularLocalParameters.firstCoordinateIdeal_le",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7325ccd217814395f1d49418bc4b2dff0f31ef15b8808142371389ef1120d1be",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters:9902",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters:9902"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W10.TriangularLocalParameters.firstCoordinatePolynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6ac13fdef2c80b52d49d1f211c7cbeecb56420b2246308788edc98f1f7edeefc",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters:9200",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters:9200"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W10.TriangularLocalParameters.firstCoordinatePolynomial_irreducible",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9c23f73a71b5728fc5e75f713290900fb13b6f320475eeb39d18796a69c73aa3",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters:9321",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters:9321"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W10.TriangularLocalParameters.firstCoordinatePolynomial_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c4115f29973eed7afff9a76fc01ae6a50951da4819ad3961ac3391c03771c8e5",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters:9718",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters:9718"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W10.TriangularLocalParameters.firstCoordinateRelation_ne_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4c8f5b1b55ce11af76ca797711289711516a475fe0c034b43d6daa0acec51b70",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters:10206",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters:10206"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W10.TriangularLocalParameters.lift_parameters",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9c0cbe132078f113dc918ee9e09c77c22239b5e55118a28afcacadb3114b17a5",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters:3083",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters:3083"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W10.TriangularLocalParameters.maximal_coefficient_contraction",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a1240e7bd8b3ef1a232cbb90f69c9fead3ff407ab980f282519914fa47d48719",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters:7723",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters:7723"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W10.TriangularLocalParameters.ofList_cons_eq_comap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "300136552a385d600838a42f006e1b76fd8325a9cf8fd1c47216b839d2f10a7e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters:2664",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters:2664"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W10.TriangularLocalParameters.polynomialMaximal_regularParameters",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParametersAssembly",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7f4eb0e95cfa372377de51dc6eb18c94ec3cb50f5b146ecdf24d7bb93b3c5cc8",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParametersAssembly:297",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParametersAssembly:297"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W10.TriangularLocalParameters.polynomialMaximal_regularParameters_of_ringEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParametersTransport",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2197c578ce6bf8d049b4f1002f681261e692e4e0fdc4fb17a0d5f3b04e324855",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParametersTransport:1158",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParametersTransport:1158"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W10.TriangularLocalParameters.principalModuleQuotientEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ab5acfae941991c13e943c91e81f5829dab1e049ba4023eb10b1ba017e2fb871",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters:900",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters:900"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W10.TriangularLocalParameters.principalModuleQuotientEquiv_mk",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "256a5919115c26c86a643b0e7ef7671398b37bb63495d7b73799af7b64f7c46c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters:1192",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters:1192"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W10.TriangularLocalParameters.regularParameters_transport",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParametersTransport",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "333066407874e4e94cc5447fd5b31e48f84b071df43b75791faad677d7cfa2d3",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParametersTransport:560",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParametersTransport:560"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W10.TriangularLocalParameters.regular_cons_of_principal_kernel",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7f45cc2426fc5f81e1c29dbf0ea1eb34fffdad1309c7520c334c8167ad199764",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters:1708",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters:1708"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W10.TriangularLocalParameters.regular_element_of_ne_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0ef5ddd5a8ece2ee2e4a5338a167e0f9f6c7391215a1e6f6891752ebf517764b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters:3931",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters:3931"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W10.TriangularLocalParameters.regular_map_ringEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParametersTransport",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "27dc9508818af22f6034604fbe4602642d307e51a1fbd080603339a4a85f8644",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParametersTransport:265",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParametersTransport:265"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W10.TriangularLocalParameters.scalar_top_eq_principal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "99fa6a3935e9c27a35f1d80dfed0e20b789c94e43ac705932a1e639b40c23c65",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters:723",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters:723"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_044.jsonl"
