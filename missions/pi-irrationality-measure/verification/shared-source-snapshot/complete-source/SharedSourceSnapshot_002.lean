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
      sourceName := "OAI.PiExponent.AffineJetSupport.sectionsIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AffineJetSupport",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bcc1a023bc0221ab3642124e94aa8bd64dda187f5816c3f2c8733d2a7d3ed0fb",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AffineJetSupport:2922",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AffineJetSupport:2922"
    },
    {
      sourceName := "OAI.PiExponent.AffineJetSupport.subscheme_preimage_eq_top",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AffineJetSupport",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6a8d44a66016ded21882b50c2c751131d489300e4359b91ed7b0074f63da5a4e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AffineJetSupport:1920",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AffineJetSupport:1920"
    },
    {
      sourceName := "OAI.PiExponent.AffineJetSupport.twistedQuotient_restriction_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AffineJetSupport",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "852e70d70cbb54265ce3320738f152f098d88b5c1e5f4ff2db64c63e1fd50fae",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AffineJetSupport:2171",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AffineJetSupport:2171"
    },
    {
      sourceName := "OAI.PiExponent.AffineReesCanonicalRecovery.eventually_comap_bijective",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AffineReesCanonicalRecovery",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5ac6d8bf78f7610ae6d1a4540658a2256ed304f9201216fdf8304ac2b260fab8",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AffineReesCanonicalRecovery:625",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AffineReesCanonicalRecovery:625"
    },
    {
      sourceName := "OAI.PiExponent.AlgebraicJetPackets.formalJet_packet_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7d2ec6e5c833f9aaeb636a5914927ece435fdbdc40d318e98599f7381e8efba7",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets:9151",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets:9151"
    },
    {
      sourceName := "OAI.PiExponent.AlgebraicJetPackets.inverseTriangularMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9aa041f17fde21235504435aa273124e297a5b819617f0c825506acb0489c593",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets:531",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets:531"
    },
    {
      sourceName := "OAI.PiExponent.AlgebraicJetPackets.inverseTriangularMap_X_succ",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c758b31a7cc5d495b1b31e2be279db36e0bb2fa0f795dbbe17d51c5248901fa5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets:1347",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets:1347"
    },
    {
      sourceName := "OAI.PiExponent.AlgebraicJetPackets.inverseTriangularMap_X_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a6d6f293462146b89b0b2e86528f1ef186973fccfbaa590262c75544f9f74ef5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets:1171",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets:1171"
    },
    {
      sourceName := "OAI.PiExponent.AlgebraicJetPackets.inverseTriangularMap_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "27328542db41111b1f30e20c3abe08b6e5c3e1524b0fe6cf3c8587511ffdf6c5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets:2215",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets:2215"
    },
    {
      sourceName := "OAI.PiExponent.AlgebraicJetPackets.liftSeries_polynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8cf4553b7a4abff1507249468dc639bfec8a05f5d48916ac6d872b010457b229",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets:3022",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets:3022"
    },
    {
      sourceName := "OAI.PiExponent.AlgebraicJetPackets.triangularEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7b6926cb7c2bae6a36390cfa2795694a9273fb2f90004aa1a159d9d267eaf1c2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets:2740",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets:2740"
    },
    {
      sourceName := "OAI.PiExponent.AlgebraicJetPackets.triangularMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9a07243cc83ea42d03465da75e5890937397cdf8206a2ea457296666a9f3f797",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets:279",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets:279"
    },
    {
      sourceName := "OAI.PiExponent.AlgebraicJetPackets.triangularMap_X_succ",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2191c19c131fe5561c9c3e1108ff5acc2d29cd0f39e117b24fcc477a48898050",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets:949",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets:949"
    },
    {
      sourceName := "OAI.PiExponent.AlgebraicJetPackets.triangularMap_X_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f682b57f6a3b7213024fbcba270e6668c951f0a834ea662b0e974dcafc113b6d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets:794",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets:794"
    },
    {
      sourceName := "OAI.PiExponent.AlgebraicJetPackets.triangularMap_comp_inverse",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0a503375a6762a627a9afa519026c32e0a9be18675a6050acdfa24c0339c3e74",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets:1601",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets:1601"
    },
    {
      sourceName := "OAI.PiExponent.AlgebraicJetPackets.truncatedFormalJet_eq_polynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "190771aebaa8565ed9592a422be7a1b3cb821199b33ee824619c152f93cae9be",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets:3502",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets:3502"
    },
    {
      sourceName := "OAI.PiExponent.AlgebraicJetPackets.truncatedFormalJet_inverse",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d6518beb72cf584ca59ecb3dd2f9d889fa83f4daf4f9b4e737f6df27f4ec5bd4",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets:4495",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets:4495"
    },
    {
      sourceName := "OAI.PiExponent.AlgebraicJetPackets.truncatedFormalJet_packet_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7ee8314165a7169e7fc70064f59257afffbc7fa99de2a39e3562cc6fdec05a62",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets:6883",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets:6883"
    },
    {
      sourceName := "OAI.PiExponent.AmpleCohomologyFinite.cohomology_finite_of_ample",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.AmpleCohomologyFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7123d8197e83245130322ef93f2eda19dcf88362b72fe30ba89e7190ab572997",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.AmpleCohomologyFinite:628",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.AmpleCohomologyFinite:628"
    },
    {
      sourceName := "OAI.PiExponent.AmpleCohomologyFinite.projectiveBase_eq_polynomialProjectiveProjection",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.AmpleCohomologyFinite",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "50a5825504eba50002b01c16d54635393ad5eab92836bfba361c56a61fd9a437",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.AmpleCohomologyFinite:443",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.AmpleCohomologyFinite:443"
    },
    {
      sourceName := "OAI.PiExponent.AmpleGlobalGeneration.affine_local_generators",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleGlobalGeneration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "81b72af544cf736f81101e37fdc37e20c823adffa161cadf70d2f82ef179ac14",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleGlobalGeneration:3210",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleGlobalGeneration:3210"
    },
    {
      sourceName := "OAI.PiExponent.AmpleGlobalGeneration.ample_eventual_global_generators",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleAllPowersGeneration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0013bd5322ca568248c0b50580171752971d99e593ad2b6515dbf8e902b33bc0",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleAllPowersGeneration:407",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleAllPowersGeneration:407"
    },
    {
      sourceName := "OAI.PiExponent.AmpleGlobalGeneration.ample_eventual_power_global_generators",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleAllPowersGeneration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6d91abeac2db6c75371a80cd525200cb19bc10f860249ce5753b45518649bdba",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleAllPowersGeneration:2079",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleAllPowersGeneration:2079"
    },
    {
      sourceName := "OAI.PiExponent.AmpleGlobalGeneration.eventual_global_generators_of_section_cover",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleGlobalGeneration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5197b64f395387cf3c4abadb08cf863a6f49fd2d1564b603fb576b730e9b085b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleGlobalGeneration:3764",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleGlobalGeneration:3764"
    },
    {
      sourceName := "OAI.PiExponent.AmpleGlobalGeneration.openSectionEquiv_postcomp",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleGlobalGeneration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7052ffa9291c578a1680549c782e68157a8fad2976b08e5e9bc38a539707ab62",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleGlobalGeneration:2584",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleGlobalGeneration:2584"
    },
    {
      sourceName := "OAI.PiExponent.AmpleGlobalGeneration.openSectionEquiv_restrict_from_top",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleGlobalGeneration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "df7b00182122a5cf21c9486d6b40e6ac9127f673987804f8c2df9bb01177f8f8",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleGlobalGeneration:2105",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleGlobalGeneration:2105"
    },
    {
      sourceName := "OAI.PiExponent.AmpleGlobalGeneration.sectionMultiply_isIso_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleGlobalGeneration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "098c58e3b2f313b217363c26a462fd538b4ce432e4962274c3d24b02300045ce",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleGlobalGeneration:580",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleGlobalGeneration:580"
    },
    {
      sourceName := "OAI.PiExponent.AmpleGlobalGeneration.twistSection_isIso_restrict",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleGlobalGeneration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6e46657b3930c7581cc71e4bc5f073bb4ced6a031673953da1fc90597efc025f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleGlobalGeneration:1227",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleGlobalGeneration:1227"
    },
    {
      sourceName := "OAI.PiExponent.AmpleIso.isAmple_of_sheaf_iso",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleIso",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5b72e43d1cdcdc6c2f07a1e4dbdf96b6a4e975f8cd6c9796bb4b93791f329cf3",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleIso:480",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleIso:480"
    },
    {
      sourceName := "OAI.PiExponent.AmpleIso.sectionOpen_postcomp_iso",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.AmpleIso",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "252c712206d03b9b7f4590b10166c262abc9e6fa2ad82ea52645174a0f7b9582",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.AmpleIso:256",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.AmpleIso:256"
    },
    {
      sourceName := "OAI.PiExponent.AnalyticCollision.differentiable_exponentialMonomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.AnalyticCollision",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1a822cba073033eafcdecaee8b4cd317fa7b0a031c5311ba199c64cc9e282709",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.AnalyticCollision:319",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.AnalyticCollision:319"
    },
    {
      sourceName := "OAI.PiExponent.AnalyticCollision.exponentialMonomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.AnalyticCollision",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bec031f893fbb515efbb6c776962e476304e03112706cf215beb90cfeae36a42",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.AnalyticCollision:202",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.AnalyticCollision:202"
    },
    {
      sourceName := "OAI.PiExponent.AnalyticCollision.hasSum_normalizedTaylorCoeff",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.AnalyticCollision",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b4eddeabd0fa0fae0fb3d6526fe236aa8ad597013799e727cd270d7c97b22d1b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.AnalyticCollision:2130",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.AnalyticCollision:2130"
    },
    {
      sourceName := "OAI.PiExponent.AnalyticCollision.hasSum_rowTest",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.AnalyticRowSeries",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c55932ab9f113ff4936b57655fe4c686e91e948699a649bd07ed129ffb84c952",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.AnalyticRowSeries:194",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.AnalyticRowSeries:194"
    },
    {
      sourceName := "OAI.PiExponent.AnalyticCollision.hasSum_translated_row",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.AnalyticRowSeries",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b1ee2a3502258136497bfe6c8d12ecd58d6a6754346dfeab00c9ba151686d2a7",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.AnalyticRowSeries:2757",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.AnalyticRowSeries:2757"
    },
    {
      sourceName := "OAI.PiExponent.AnalyticCollision.norm_exponentialMonomial_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.AnalyticCollision",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "876e96868e7ba22279d131b4e984895983670925ce0baa75eea797d510912bde",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.AnalyticCollision:571",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.AnalyticCollision:571"
    },
    {
      sourceName := "OAI.PiExponent.AnalyticCollision.norm_exponentialMonomial_le_exp_budget",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.AnalyticCollision",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9bad5761cf9cb12f4ef1a09be672021026bad5ba65fcf0935ba07d334e2c4291",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.AnalyticCollision:6573",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.AnalyticCollision:6573"
    },
    {
      sourceName := "OAI.PiExponent.AnalyticCollision.norm_normalizedTaylorCoeff_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.AnalyticCollision",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "30b34615b3c0950599b42c7c4d77a991d7a4416e38f191172714034269d9d003",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.AnalyticCollision:1329",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.AnalyticCollision:1329"
    },
    {
      sourceName := "OAI.PiExponent.AnalyticCollision.norm_rowTest_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.AnalyticCollision",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bf32e2465979f10ee78f047990f9874256c772a3d56e349a1fbdf7903b4aba05",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.AnalyticCollision:4161",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.AnalyticCollision:4161"
    },
    {
      sourceName := "OAI.PiExponent.AnalyticCollision.norm_rowTest_shifted_power_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.AnalyticCollision",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "258e8eb8e592ab8887088b014ca1b33ed4c6f5555bb2f1b08cebd4717e849b2b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.AnalyticCollision:5412",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.AnalyticCollision:5412"
    },
    {
      sourceName := "OAI.PiExponent.AnalyticCollision.norm_shifted_log_div_le_half",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.AnalyticCollision",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d5bf6918e6acba38e78c8b53f79f87d28e2285fb5e9f084c181c13083f8797ec",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.AnalyticCollision:4964",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.AnalyticCollision:4964"
    },
    {
      sourceName := "OAI.PiExponent.AnalyticCollision.normalizedTaylorCoeff",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.AnalyticCollision",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9e3f893e20fb72eeafca30261521e66600320ccbcca713c143ebf6e9c109c383",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.AnalyticCollision:1189",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.AnalyticCollision:1189"
    },
    {
      sourceName := "OAI.PiExponent.AnalyticCollision.period_center_radius_bound",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.AnalyticCollision",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9baa28c353a54fa35f0b9b1dcbf92935a54b83e0ce3eb155144845b73e434a3f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.AnalyticCollision:5888",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.AnalyticCollision:5888"
    },
    {
      sourceName := "OAI.PiExponent.AnalyticCollision.rowTest",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.AnalyticCollision",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f6df91c8ff9da9968b275cd3b6aca4856dccab619822d1f4d96c7fe4eabcf368",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.AnalyticCollision:4043",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.AnalyticCollision:4043"
    },
    {
      sourceName := "OAI.PiExponent.AnalyticCollision.rowTest_const_mul",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.AnalyticRowSeries",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f8b18899195b4375b7ee475cf1898e8200b14d402e961dc9ef4d545704dc8464",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.AnalyticRowSeries:2323",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.AnalyticRowSeries:2323"
    },
    {
      sourceName := "OAI.PiExponent.AnalyticCollision.translated_row_determinant_bound",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.AnalyticDeterminantCollision",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "71e2782f53412f7f39bba15f27adfb3cfd6573ddbeb53f55465a69a528c9d077",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.AnalyticDeterminantCollision:278",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.AnalyticDeterminantCollision:278"
    },
    {
      sourceName := "OAI.PiExponent.AnalyticCollision.translated_row_determinant_bound_sum_order",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.AnalyticDeterminantCollision",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0ede24a7874cac61d4f796dd18c8c258fc7f29959f88f510b426e1cb47f5a33d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.AnalyticDeterminantCollision:1826",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.AnalyticDeterminantCollision:1826"
    },
    {
      sourceName := "OAI.PiExponent.AnalyticCollision.translated_row_determinant_exp_bound",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.AnalyticDeterminantCollision",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "99e9a2bd8bb0af00920a056bdcd8c22c5b56214a1e8165c3b8cfea74cd663eb7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.AnalyticDeterminantCollision:2857",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.AnalyticDeterminantCollision:2857"
    },
    {
      sourceName := "OAI.PiExponent.Arithmetic.cleared_det_log_bound",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0f50e56738ffe293c5066b3af4b73abb255d87d04e571e25822927a6ef09f3ab",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:3136",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:3136"
    },
    {
      sourceName := "OAI.PiExponent.Arithmetic.cleared_det_log_bound_of_entries",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "96c1b9c5cd6f01471e2415bd45f826794e45751e781d742fe8e04a46c8aff359",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:11439",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:11439"
    },
    {
      sourceName := "OAI.PiExponent.Arithmetic.cleared_det_log_bound_with_denominator",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ac85c5246bed75f2b4e3103365cc058eaea7d90650123396e0d51914f05ebb83",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:11941",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:11941"
    },
    {
      sourceName := "OAI.PiExponent.Arithmetic.cleared_det_norm_bound",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5fc2e02aae97b4e81601d00fa2a45bde80bacdf67fe49b24233b548fcf51f33d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:1867",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:1867"
    },
    {
      sourceName := "OAI.PiExponent.Arithmetic.cleared_log_trunc_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cb7bb0b6752e88ee9b4fcfd1f47d124f175199fe7f10bbd8838587f84cfc3ac7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:7630",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:7630"
    },
    {
      sourceName := "OAI.PiExponent.Arithmetic.cleared_polynomial_power_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0db490600d5d5b186fe1f5dab316191d134300d7bb02cb46c1d6ad2d9da339fc",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:9085",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:9085"
    },
    {
      sourceName := "OAI.PiExponent.Arithmetic.cleared_polynomial_product_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ab56f2371cd3ac2e8d1dc91b367e5b34004476b84a05da3dc323e7d6796f5be4",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:9701",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:9701"
    },
    {
      sourceName := "OAI.PiExponent.Arithmetic.cleared_shifted_log_trunc_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4b60f8776d37f3612f7964b90e89a4bfe09dcfa81f4832acbaa5f16a087b4b65",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:8453",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:8453"
    },
    {
      sourceName := "OAI.PiExponent.Arithmetic.column_log_cost_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ee5454e1e0c94ccd2f1b1ee14926fad1e1a9cb0790db1929d1731395347d3657",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:13374",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:13374"
    },
    {
      sourceName := "OAI.PiExponent.Arithmetic.common_denominator_coeff_gaussian",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "52387c4f63b2325bed5d603d3b16066de631297e08c3c6b1e1a44e9fb023dd00",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:10368",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:10368"
    },
    {
      sourceName := "OAI.PiExponent.Arithmetic.det_row_column_scale",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2cbeb256083b713e19fac2f06902cc2579267a7f6cda0d3df7e45bff030ed548",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:1452",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:1452"
    },
    {
      sourceName := "OAI.PiExponent.Arithmetic.dvd_lcmUpto_of_pos_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3bfd79dffaaf171a4a2d0f3290ec11f0aa6ebf84501f8d5b5339bb0130c4ab13",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:6880",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:6880"
    },
    {
      sourceName := "OAI.PiExponent.Arithmetic.gaussian_C_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ca7a27193b5c97c8dda1e4d754dca2240772cb1c248df530bc7ac5f5d77904d3",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:8278",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:8278"
    },
    {
      sourceName := "OAI.PiExponent.Arithmetic.gaussian_det_norm_one_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a7e50bf391cd19bf266f0a3c7ea2c55acb0ff362096856cc6a47eca80e04d838",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:1130",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:1130"
    },
    {
      sourceName := "OAI.PiExponent.Arithmetic.gaussian_norm_one_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "900b2373d783bc4e72c43d97e32cf19e26bca63feae1596a6273c1582fb78e21",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:761",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:761"
    },
    {
      sourceName := "OAI.PiExponent.Arithmetic.lcmConstant",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "31cc4f14cbc40464a9583c80c042821d3aa246550eff9a7f4033fd8276f3fd17",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:355",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:355"
    },
    {
      sourceName := "OAI.PiExponent.Arithmetic.lcmConstant_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3c773e94e4ff1b1d9a6c90203a0a3ee029623a432c2c2611aeae4cd5b099ed69",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:412",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:412"
    },
    {
      sourceName := "OAI.PiExponent.Arithmetic.lcm_mul_log_coeff_gaussian",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cba1e72c9a2d89d289ea4851fbd1a0ade1b13dca6d38dbdd416924aab9fb59f5",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:7056",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:7056"
    },
    {
      sourceName := "OAI.PiExponent.Arithmetic.log_lcmUpto_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8b38252819561da87b87a948e635067ee15c1a2f3aee87629a3c161b08bb2b38",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:563",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:563"
    },
    {
      sourceName := "OAI.PiExponent.Arithmetic.log_lcm_floor_product_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c007d2dd963d132ab8b22c8f466f2a532baa93943c73b58893cf714bbc7f843a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:4554",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:4554"
    },
    {
      sourceName := "OAI.PiExponent.Arithmetic.log_lcm_power_product_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "26bb80c2dbc35423a5ed02db389ff88c89e6ce9b1c4a8f3be3c0ca86b63c6ef1",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:4022",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:4022"
    },
    {
      sourceName := "OAI.PiExponent.Arithmetic.normalized_arithmetic_bound",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "23cc7ffef56148643195942ce298ac654f9cfa8a51c8529e39ee6ab08a88ffd4",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:15170",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:15170"
    },
    {
      sourceName := "OAI.PiExponent.Arithmetic.row_log_cost_lower",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5e0991837b4d676e7b577ba55d62b526a92628f4ae7acf1fa1c00562475ecafa",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:14105",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:14105"
    },
    {
      sourceName := "OAI.PiExponent.Arithmetic.shifted_truncation_product_coeff_gaussian",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a6d57f20cde0dbbc11a57ae3f724ea0a092289aa5b6729f3cffb0fb473c8c429",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:12720",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:12720"
    },
    {
      sourceName := "OAI.PiExponent.Arithmetic.sum_ceil_truncation_div_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3bbd6f1431bf8f7de866186a86212242a958f4944923fe809306733718e605be",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:5385",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:5385"
    },
    {
      sourceName := "OAI.PiExponent.Arithmetic.sum_exponents_le_weight_div",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ce6f6fe879f5792f2cfbf4b57704f7735d0455473a666e092af5fe8427478f20",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:13691",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:13691"
    },
    {
      sourceName := "OAI.PiExponent.Arithmetic.truncation_denominator_log_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "988197ff2275567913a1167a43c2e9a2d288761d58ef5706e840f236c14eba18",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:6121",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Arithmetic:6121"
    },
    {
      sourceName := "OAI.PiExponent.BirationalOpenIso.exists_open_iso_of_generic_inverse",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.BirationalOpenIso",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0f8328dbf81ba5ac0db16cb5e4c48a131523cdcb5509c7f27b809c1eeeb6428b",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.BirationalOpenIso:273",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.BirationalOpenIso:273"
    },
    {
      sourceName := "OAI.PiExponent.BirationalValuationStalk.stalkClosedPointTo_bijective",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.BirationalValuationStalk",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f1a05fb00d454ca6a121f084ee0c7e96d14674d8272488a35fade1ce027fbe65",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.BirationalValuationStalk:2559",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.BirationalValuationStalk:2559"
    },
    {
      sourceName := "OAI.PiExponent.BirationalValuationStalk.stalkClosedPointTo_field_compatibility",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.BirationalValuationStalk",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c24d249077953df276ed75966c3d61d52700f4a2fc5410ae07e288541dc555ff",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.BirationalValuationStalk:848",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.BirationalValuationStalk:848"
    },
    {
      sourceName := "OAI.PiExponent.BirationalValuationStalk.stalkMap_isIso",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.BirationalValuationStalk",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "af63e36d3a20ee3905f34c0688ea207e131fe0e329a6fd158e62ac8610d4caf2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.BirationalValuationStalk:3653",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.BirationalValuationStalk:3653"
    },
    {
      sourceName := "OAI.PiExponent.BlowupCurveMargin.actual_contact_bound",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "566e97977bd1a2e7f3e7db4e78a9229b53a27941c482e7eee789442191f816c9",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin:7453",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin:7453"
    },
    {
      sourceName := "OAI.PiExponent.BlowupCurveMargin.contactSum",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f49f6de645ac736d5d2ab1a3a25e6796ab8ec78c40776a49a64fe351724ce3a6",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin:6588",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin:6588"
    },
    {
      sourceName := "OAI.PiExponent.BlowupCurveMargin.curveDegree_zero_of_frame",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "63313472034990408e0e3f6e55d5f2eec464ecc18b152e866141fb74cdd6798e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin:2721",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin:2721"
    },
    {
      sourceName := "OAI.PiExponent.BlowupCurveMargin.curve_degree_laws",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a79c06f8aded370c5648e8c3563b05554e4f5a9b1d90f8b589599b54eff68477",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin:550",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin:550"
    },
    {
      sourceName := "OAI.PiExponent.BlowupCurveMargin.marginCoefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fdda1a073774c1d1f2dba239ab8d229697b772bac454f5e7438ab0ef299e4263",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin:1609",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin:1609"
    },
    {
      sourceName := "OAI.PiExponent.BlowupCurveMargin.marginCoefficient_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "76b9974cd02dc815035079a2a54c074f97a5c38d46c482049a46fad1ecc8e3fc",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin:1696",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin:1696"
    },
    {
      sourceName := "OAI.PiExponent.BlowupCurveMargin.margin_of_actual_contact_degrees",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "46f67d0a1939c6cd9d24a7bb3d6ac28e6c680deb2f999b8d004764e10766d40b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin:7801",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin:7801"
    },
    {
      sourceName := "OAI.PiExponent.BlowupCurveMargin.margin_of_avoids_center",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e9d0f14657946a1065a747c103deef1191a74c1d83197e4b44eb785f65f0525a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin:4071",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin:4071"
    },
    {
      sourceName := "OAI.PiExponent.BlowupCurveMargin.margin_of_contracted",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "05145cd31ffc4860729847c334932086073d18fde7d2557fac567f6535a93e89",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin:5457",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin:5457"
    },
    {
      sourceName := "OAI.PiExponent.BlowupCurveMargin.margin_of_exceptional_frame",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9484c98672337fbc7a23eb54fe5247fa7df4b04c82253c6ec56d6a026e9ff92c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin:3125",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin:3125"
    },
    {
      sourceName := "OAI.PiExponent.BlowupCurveMargin.margin_of_image_outside_chart",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5a926bc3bbca5b1fb051e970407f3f6c4fd35719279090ba69bd0b40297f8d78",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin:4752",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin:4752"
    },
    {
      sourceName := "OAI.PiExponent.BlowupCurveMargin.margin_of_nonnegative_degree",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aaa471882a04ff6256727c344dd6e241ae72a65bc787b105e51a5da84427f060",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin:1912",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin:1912"
    },
    {
      sourceName := "OAI.PiExponent.BlowupCurveMargin.poleDegree",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "de499d4677a54c61ab2591c5c6c506904e3c29a28029485963f0e8ee18f26713",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin:7198",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin:7198"
    },
    {
      sourceName := "OAI.PiExponent.BlowupJetSurjectivity.blowupBundle",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupJetSurjectivity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0d8d99f7966e92cd78a5e827686ac549e4289de8b8da725ef2eb7fe8484ca377",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupJetSurjectivity:481",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupJetSurjectivity:481"
    },
    {
      sourceName := "OAI.PiExponent.BlowupJetSurjectivity.eventual_blowup_jetRestriction_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupJetSurjectivityComplete",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "837f35277b84e7149307a43326c3c53447549b79c61d0de3d00b3655b1727563",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupJetSurjectivityComplete:393",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupJetSurjectivityComplete:393"
    },
    {
      sourceName := "OAI.PiExponent.BlowupJetSurjectivity.eventual_blowup_jetRestriction_surjective_of_affine_recovery",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupJetReesReduction",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d37adedda6af44f03165bc10d57f69a307763e980d5a587422da96ee5d260359",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupJetReesReduction:446",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupJetReesReduction:446"
    },
    {
      sourceName := "OAI.PiExponent.BlowupJetSurjectivity.eventual_blowup_jetRestriction_surjective_of_section_comparison",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupJetSurjectivity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3e0260d6252d195589121347201ee1f7fe1e7e05bdbad430718b9841a6d824b7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupJetSurjectivity:740",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupJetSurjectivity:740"
    },
    {
      sourceName := "OAI.PiExponent.BlowupJetSurjectivity.eventual_jetRestriction_surjective_of_ample_comparison",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupJetSurjectivity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a0029e40d7e8450609af65b63984664a2da94a21143ff0814a40250e9f423f66",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupJetSurjectivity:2225",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupJetSurjectivity:2225"
    },
    {
      sourceName := "OAI.PiExponent.BlowupJetSurjectivity.jetQuotient",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupJetSurjectivity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "326bc1b7e964563dff8d886b1887c087f23d53b83bd62ead2b26a2062d9105ad",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupJetSurjectivity:506",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupJetSurjectivity:506"
    },
    {
      sourceName := "OAI.PiExponent.BlowupJetSurjectivity.jetRestriction",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupJetSurjectivity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "54675b80d2b20e109759d35d0cd05d9a985b1f9175105f23191e1cb0357b9623",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupJetSurjectivity:836",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupJetSurjectivity:836"
    },
    {
      sourceName := "OAI.PiExponent.BlowupJetSurjectivity.jetRestriction_surjective_of_h1_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupJetSurjectivity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f01a3f668da7dd2dc71017fd7f1800a5b7696d9bf664d0deb4cf151dcd7d1b49",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupJetSurjectivity:1184",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupJetSurjectivity:1184"
    },
    {
      sourceName := "OAI.PiExponent.BlowupJetSurjectivity.twistedIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.BlowupJetSurjectivity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2b53fd6d8d1446cd5f9a4a97a4662cb56b80bc7c5820bb6b224d4475412a7e6d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.BlowupJetSurjectivity:663",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.BlowupJetSurjectivity:663"
    },
    {
      sourceName := "OAI.PiExponent.BranchContact.active",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.BranchContact",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "93151b80ac3111481271d883605c58e02a1e26c4ba2b6d0663d0899611be4ae9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.BranchContact:185",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.BranchContact:185"
    },
    {
      sourceName := "OAI.PiExponent.BranchContact.active_nonempty",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.BranchContact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c666079ab49a6779b7bafab66540b3bc4cceacb7dce3c9e38430dbdafb0419b3",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.BranchContact:448",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.BranchContact:448"
    },
    {
      sourceName := "OAI.PiExponent.BranchContact.add_not_all_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.BranchContact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "771eada4252684714edcf94f56a3097c9e885e44408be4a82f831a20d51d23bd",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.BranchContact:5056",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.BranchContact:5056"
    },
    {
      sourceName := "OAI.PiExponent.BranchContact.contact",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.BranchContact",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1916138d8569b829fea0d332886d438f7aee7a2666bf28f31d2f894f8d621bb8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.BranchContact:631",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.BranchContact:631"
    },
    {
      sourceName := "OAI.PiExponent.BranchContact.contact_add_high_tail",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.BranchContact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e548a7d3324b5985d1a59e018fbb9b5db1a8e2101a8c1fb3d5365c76dd2e8344",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.BranchContact:5397",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.BranchContact:5397"
    },
    {
      sourceName := "OAI.PiExponent.BranchContact.contact_bound",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.BranchContact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5360950695ef44e8b60daa0975f539259b7ff31e7f1f4ae62a50930a2c4da16d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.BranchContact:1937",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.BranchContact:1937"
    },
    {
      sourceName := "OAI.PiExponent.BranchContact.contact_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.BranchContact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4e3a3c792d978e49bab824758b1e53ca36b748f2878c1dc4e69b970e82af6e0b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.BranchContact:812",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.BranchContact:812"
    },
    {
      sourceName := "OAI.PiExponent.BranchContact.contact_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.BranchContact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7811208f0c3deda4f40eaec306c1690f7f4d415d15c9332101162291ddcf9622",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.BranchContact:1393",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.BranchContact:1393"
    },
    {
      sourceName := "OAI.PiExponent.BranchContact.exists_attaining_add",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.BranchContact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c517c29d0a54bc1345df75408c3ffbd70b4f51f9d04c64ff73af9c0ed03f4b7a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.BranchContact:3741",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.BranchContact:3741"
    },
    {
      sourceName := "OAI.PiExponent.BranchContact.exists_attains",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.BranchContact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b4a3948d5abfec209d2ed8c4cc4516753b79ca4b9d5074fa7cf14beaf4829c9d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.BranchContact:1044",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.BranchContact:1044"
    },
    {
      sourceName := "OAI.PiExponent.BranchContact.le_contact",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.BranchContact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6d9c2e2d650af40c91453697f570eb86e9c81b38a2b9590e903e12bb52553d95",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.BranchContact:2374",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.BranchContact:2374"
    },
    {
      sourceName := "OAI.PiExponent.BranchContact.mem_active",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.BranchContact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d602b9f9602f3fbf11c6767b2edec2125e4301f357160ae37b67b5ab3079b8d2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.BranchContact:308",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.BranchContact:308"
    },
    {
      sourceName := "OAI.PiExponent.BranchContact.order_add_lower",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.BranchContact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e793cf0c95c94ac54c2b4170de1d31a96c7fb74ac7beee5d7ac4cdcef41c9425",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.BranchContact:2776",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.BranchContact:2776"
    },
    {
      sourceName := "OAI.PiExponent.BranchContactIdeal.addVal_pow_toNat",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.BranchContactIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c3e16366405f06afb2b545eb79757e757cb6c9fb97a859585b0c331d570691fc",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.BranchContactIdeal:945",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.BranchContactIdeal:945"
    },
    {
      sourceName := "OAI.PiExponent.BranchContactIdeal.colength_eq_contact",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.BranchContactIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "975d395818b72c5e79030198e4af1e05e1bc900799d372e486d6b1013ea189df",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.BranchContactIdeal:4207",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.BranchContactIdeal:4207"
    },
    {
      sourceName := "OAI.PiExponent.BranchContactIdeal.contact",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.BranchContactIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "97e133726d5483bd62b203f7c773504dec2fee93e061e05066541676d467b7fd",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.BranchContactIdeal:1310",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.BranchContactIdeal:1310"
    },
    {
      sourceName := "OAI.PiExponent.BranchContactIdeal.exists_generator_colength_eq_contact",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.BranchContactIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3d0766307d948524906f01b9f83b44b184b1bd59bfff464f3e41d22a0bfdbe98",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.BranchContactIdeal:1580",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.BranchContactIdeal:1580"
    },
    {
      sourceName := "OAI.PiExponent.BranchContactIdeal.powerIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.BranchContactIdeal",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9ee1f24bb67929abbda4c316aae092e62c979e8b2edad92ee08188b6071fb936",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.BranchContactIdeal:350",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.BranchContactIdeal:350"
    },
    {
      sourceName := "OAI.PiExponent.BranchContactIdeal.powerIdeal_eq_singleton",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.BranchContactIdeal",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "99bf19abbcd6c88588197a81df30172c62a030dc411ddea2ba34eefe2d374afd",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.BranchContactIdeal:460",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.BranchContactIdeal:460"
    },
    {
      sourceName := "OAI.PiExponent.CanonicalAffineRecovery.bijective_iff_comap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CanonicalAffineRecovery",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "00b1aea23c1a61997bfccbe319f5abdca05b3e7b0c5082e3143711f21184040c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CanonicalAffineRecovery:952",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CanonicalAffineRecovery:952"
    },
    {
      sourceName := "OAI.PiExponent.CanonicalAffineRecovery.power_bijective_iff_comap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.CanonicalAffineRecovery",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1aee781c3cbf38bce3c5d2ff9549ab26a744cc691c2eb3bc9c5f5920dc6e2407",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.CanonicalAffineRecovery:2747",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.CanonicalAffineRecovery:2747"
    },
    {
      sourceName := "OAI.PiExponent.CanonicalRecoveryProperties.ComapBijective",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CanonicalRecoveryProperties",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f8cb5f707b7913bef5abcff8e88fe98208035c3a888a2f62cc8669052500ed89",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CanonicalRecoveryProperties:348",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CanonicalRecoveryProperties:348"
    },
    {
      sourceName := "OAI.PiExponent.CanonicalRecoveryProperties.OrdinaryBijective",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CanonicalRecoveryProperties",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c9a5c0bb5f84798a1a2b08d018275ee23f39f355845ae17ea3594fde961f9a58",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CanonicalRecoveryProperties:531",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CanonicalRecoveryProperties:531"
    },
    {
      sourceName := "OAI.PiExponent.CanonicalRecoveryProperties.comap_open_square",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CanonicalRecoveryProperties",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bcbc9b491984a5574c74a25e29926cbc732ea1d8da941e69e5bc68ae2b2ef15f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CanonicalRecoveryProperties:1475",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CanonicalRecoveryProperties:1475"
    },
    {
      sourceName := "OAI.PiExponent.CanonicalRecoveryProperties.ordinary_iff_comap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CanonicalRecoveryProperties",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4354e5cfd6f4168cbbcb90ba11126512096e0518ca12799afcc15a4b56c51acb",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CanonicalRecoveryProperties:852",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CanonicalRecoveryProperties:852"
    },
    {
      sourceName := "OAI.PiExponent.CartierDegreeLength.cartier_euler_difference_eq_sum_local_lengths",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CartierDegreeLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "97d05dfab8a477397666daff25d60307f63c11fcc394747907576f7475080a0a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CartierDegreeLength:502",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CartierDegreeLength:502"
    },
    {
      sourceName := "OAI.PiExponent.CartierPowerFrames.cartierPowerMultiply_ideal",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CartierPowerFrames",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6ac0fdb891632f6b923d1cb4e5edf54e76f1f554739af1b4787f01cc0dacb26f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CartierPowerFrames:5151",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CartierPowerFrames:5151"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_002.jsonl"
