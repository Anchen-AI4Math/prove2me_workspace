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
      sourceName := "OAI.PiExponentSiegel.W10.TriangularLocalParameters.zeroVariable_maximal_eq_bot",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e8d86ec77cf677fc8d17d648a74e605c9a04fcd102bdb2a89931ab84775fb744",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters:6627",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters:6627"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W10.TriangularLocalParameters.zeroVariable_parameters",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f357fdcb31a78a4937b4c1929424fa7d038883d4a14eb898a1ec56bc17829163",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters:7068",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters:7068"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.AffineRing",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bfe0dc060975c1be7f2b56d4369e754e815b7a885d45952348aeba66be8a1773",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:6568",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:6568"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.ConeAway",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9a3b59d4ffd7109fe42c13968f2244ca495fc30282b8fb2abee267f18be4224d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:6655",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:6655"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.ConeRing",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4160e00f2c21d5b8fb41f99a295bc70afeb4be80909ac2b47c3792a6fe5271f5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:6608",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:6608"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.LaurentChart",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7e992e1d35b840779d65e88e03b37deeb62f113633253e233cb0f8d029dcc13d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:6731",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:6731"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.affineLocalConeAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fe21d35610951cf606a973b5d16fa90a8099d1ec260c00b238e81a4c85bf3598",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization:2159",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization:2159"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.affineLocalToConeLocal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fd10110f77711067872b4f387ca178e5b1eda86d2a9df9b082cff714ab77b09f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization:1883",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization:1883"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.affineLocalToConeLocal_faithfullyFlat",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeRegularSequence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6ef4c3469f5b18912cb563f96bdc934b755b95c89b4bb388480b0569d054efae",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeRegularSequence:4516",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeRegularSequence:4516"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.affineLocalToConeLocal_flat",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a22cace3ac25dc5f4f0ded0251bbdef955d4bc669224f8df546a69074cd2761f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization:2848",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization:2848"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.affineLocalToConeLocal_map_maximalIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7716f958fe4e940b11dce94164cb7b26e5bf8eb4569bd4dafeff3c98f4fd4c0f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization:2341",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization:2341"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.affineToConeAway",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fa4b76193ade1a8e2c946d4fc59c5de9e05a3f9d1f8dffda6950bff12b81527f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:7431",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:7431"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.affineToConeAway_C",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "89cb7b926ed8372b42abf76b4ebb6546c87d58db0961f68504521c7aa867951b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:7725",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:7725"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.affineToConeAway_X",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2a17051c2071887fe234d7574410f716f67f92fb4f06cef20d1252c704a5980e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:7923",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:7923"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.affine_ideal_map_to_laurent_local",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeEquationLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "999c44072eb7331b827c8a45749ab8ec0653d7e1ecc4327bf8c487c9b5feb10e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeEquationLength:2215",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeEquationLength:2215"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.awayChartPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "df5d873daa8324124dda1ce70d406db4031e4a122d0fcff3d3381d5e295376c4",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization:447",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization:447"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.awayChartPrime_isPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4506b5fd4ecc0c802f5a6f930d106d0d4a76b63df61890b22c359c3bf9fb8545",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization:574",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization:574"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.coneAwayToLaurent",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2989ac4ce9789db3f1cfd48536b3c6413d210be1c478689993479201b93f64b6",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:8945",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:8945"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.coneAwayToLaurent_algebraMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "32dc70f0b20fe23fb9e5c45ef2245e3099f9ae618deda88c282e7f61e0a63998",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:9179",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:9179"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.coneAwayToLaurent_comp_affineToConeAway",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c11f607f82ef10791c191a2695d88b1ba5dd869ac54748b1772e05b0b4d49e17",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:10648",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:10648"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.coneAwayToLaurent_comp_laurentToConeAway",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eb7c626ef290ae0d61667d7d444e3b9b5f84b0c59af77e9bd38314fb4da6c1b6",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:11553",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:11553"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.coneHomogenizingUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "22f9e0197a3943ab31cd7186e3769db37a92b5a3b9ad3e2bee9176e3219b544c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:6793",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:6793"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.coneHomogenizingUnit_inv_mul",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "08670ef2721340ddd131f67bf0ccc47472ee9c11fc480cce2b5dc37f3a84ec0c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:7150",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:7150"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.coneHomogenizingUnit_val",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d028aedfd505849babe5549d2b85f8cecc5595689b55d23329bd1fa8ab13f48d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:6956",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:6956"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.coneLaurentEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d8f1446abfc8c49f2b1ded6cc0493a34681c2a212cc4d5d37158ea8095814a3d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:12364",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:12364"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.coneLocalCoordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeRegularSequence",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7e1496613a3893f8c30ec1a95a1974bfb04ddc71b227249f8a8aa791b1752321",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeRegularSequence:2232",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeRegularSequence:2232"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.coneLocalCoordinate_isUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeRegularSequence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "740520c3b05f32d43b90d82a2026d447ffdbfcb19d26d2b677645f9063708dc5",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeRegularSequence:2398",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeRegularSequence:2398"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.conePrime",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "61018d8f2e91030eb4293609e0bf7788de496e98c505b38b00ab0126093af80c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization:692",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization:692"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.conePrimeLocalizationEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c4437333ba9ec3898c0699888b21d29845e57a5903e0e03a5f21cb133d0617d3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization:1407",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization:1407"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.conePrimeLocalizationEquiv_algebraMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeEquationLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "40f53da5d56eb99c0540ff3f7956a62de92cfb1d80045196f2a0012bbabcad73",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeEquationLength:328",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeEquationLength:328"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.conePrimeLocalizationEquiv_map_ideal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeEquationLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5a5ad704fec2e5d25eff2b2a85a1d689b4708710ab98445eec776caea31dd8a3",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeEquationLength:1707",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeEquationLength:1707"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.conePrime_isPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6c0a5c790972fdc6fc6be453ae79c82e0feb272b40ea980d034ab3ec0d2a9a48",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization:814",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization:814"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.conePrime_minimal_over_homogenized",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ConePrimeProperties",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bb3bb9514e722abaaba3b61b43828a900e3f59756945f59bf12408204e71aa02",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ConePrimeProperties:1891",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ConePrimeProperties:1891"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.coneToLaurent",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "17697696b257654da1658c8b5a6d47fb9364e5480bb671c2d8b798dac5aec343",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:8176",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:8176"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.coneToLaurent_C",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e1dd8ffb8947e9e254ba7ad04cd1a650f44bcb73f01db3897510590a072daa0c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:8437",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:8437"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.coneToLaurent_X_none",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "345b36c198aae022f6613d0ad2f7c1a5735e0d2497967e48e30a515f3f9a08f7",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:8600",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:8600"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.coneToLaurent_X_some",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b4fa8f04eb282849d78af243021806fde9ab8be154869aa80b0ac9fcd268556c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:8742",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:8742"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.coneToLaurent_homogeneous",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.ConeHomogeneousEquations",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b7dbabb12fd4840cd404afa2dfab45b2fe81f2cb316de21f0f461a7c5a5edbb0",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.ConeHomogeneousEquations:2256",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.ConeHomogeneousEquations:2256"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.coneToLaurent_homogenize",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.ConeHomogeneousEquations",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8061e6a9e3deaaf7f973af4efac40b0400b3a644de56f25e8ade0097d7e2c6f5",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.ConeHomogeneousEquations:2618",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.ConeHomogeneousEquations:2618"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.eval\u2082_scale_of_isHomogeneous",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.ConeHomogeneousEquations",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1ffe7a1b27f45883d1513f90c5641aace27b265181e0fc520769ea06db3c3280",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.ConeHomogeneousEquations:328",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.ConeHomogeneousEquations:328"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.homogenized_cone_local_length_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeEquationLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5b1c59064ce245a265ac1e7fd62ccf58f0e22367ad2862daf20e1a10a664091d",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeEquationLength:2914",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeEquationLength:2914"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.homogenized_list_regular_at_cone",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeRegularSequence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "42d46784ee3f9894f3cae25b24663519e2444eddccbd0b43966eefc2414250ea",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeRegularSequence:5073",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeRegularSequence:5073"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.homogenized_local_eq_affine_mul_coordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeRegularSequence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fd934f94835a37655747057e1e4dfed2dc974332e998e3e2e85d748061e195e5",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeRegularSequence:2669",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeRegularSequence:2669"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.homogenizing_coordinate_not_mem_conePrime",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "00d0fdcd8f5f5560e2872c64c3b312ace02d41c6ef0028cdc7d4721db9550b17",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization:917",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization:917"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.isRegular_map_mul_units",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeRegularSequence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "16c1a77b4fb3add09ad330178dc36b70d7ce901f95dd31aa015d4cf6291a2f09",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeRegularSequence:1039",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeRegularSequence:1039"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.laurentLocal_maximalIdeal_map_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "19a2a39f9c8e84651128b510a55daebebe25a10952a77a613f99024560d18199",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:5594",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:5594"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.laurentLocal_quotient_length",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9b9828f574bbc37aef9ca35fdec729a00772ba761336b55bdf26d8dcf7a31621",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:5932",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:5932"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.laurentPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "daba7f550088f15c5edd31a5508765cae760d647cae5d19ded42adb0c674b2d6",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:2762",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:2762"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.laurentPrime_comap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8a63f2acb2a1253a60f74cbc2a2fc50f46e979a6a6505872a58ecead147c0eb1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:4306",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:4306"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.laurentPrime_eq_map_polynomialPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "448c9991a0dd010c89eecb0e035634e640a2f8e3c2a03363ba28f1d596d5d330",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:3445",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:3445"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.laurentPrime_isPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e27189414eac1d00526549906ab2a3419af76f848574f113327aee54159b21b3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:3985",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:3985"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.laurentPrime_liesOver",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "26d696e50ff9b2c7922fbb3cc110f545a2e2d58bf3a81bfbafda9d924eaa2ba8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:5032",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:5032"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.laurentToConeAway",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5b7a0321c1a896452bf2c13f909c190a442f4a28324235f27fe5918459e6a70e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:9385",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:9385"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.laurentToConeAway_C",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e640e5b9c5c1345c49e9e0098d63427dd13bf3d7d696ed8795b5f76f395adb30",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:9534",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:9534"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.laurentToConeAway_T",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "abc0c6c390a59edac6bac6190e2cb1a2c5781545f71b2f24697a34f068924cab",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:9709",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:9709"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.laurentToConeAway_comp_coneAwayToLaurent",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "07717b9d1209453ba865a660a445ff8c8bebd3a0d0078447579a85b438d311b5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:10172",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:10172"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.laurentToConeAway_comp_coneToLaurent",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bcfab8d7af828e5926b70f0799d2875067062b33ffb3692e274fb50353b8d26d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:9864",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:9864"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9fc5988ec8c7c8370ea1db8433164ef1c1e3a6095cbb537ee236beda0c69f270",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:5163",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:5163"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a52b7206a5d749d16308d251b8a4602c3b54c6176192f2e38cb5dee97e39f93d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:2844",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:2844"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.localized_maximalIdeal_map_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "742f4ffc0a73bf05fb9b0c9de6ad7c82bc200df3a6e1e00c2f209017f9b9d472",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:665",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:665"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.map_homogenized_span_eq_laurent_span",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.ConeHomogeneousEquations",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3c526e10612a9ad46e194f6ad3256e1b9bc05b9c73ae80be579d26ad09c35b8b",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.ConeHomogeneousEquations:2982",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.ConeHomogeneousEquations:2982"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.mapped_minimalPrime_of_prime_extension",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ConePrimeProperties",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b599d1ff2a9048f7e65bdb836c629e27c37d0c2decfcdcd0a557069ad74895aa",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ConePrimeProperties:549",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ConePrimeProperties:549"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.minimalPrime_isHomogeneous",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ConePrimeProperties",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9ae0c04941308becdd89d982858193228bfc866d5ff3a6569a302906041ac0d0",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ConePrimeProperties:1016",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ConePrimeProperties:1016"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.ofList_map_mul_units",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeRegularSequence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "401623d18e5a8571138522e67a4684a48ba9e24b9c751aecec0919e688c1660a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeRegularSequence:443",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeRegularSequence:443"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.polynomialPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8c85969951e04df3107306eb712d43ad3db4254e0da3bea596ad0f1f41b9dcf0",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:1544",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:1544"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.polynomialPrime_comap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ff90eb774d1e0850c8d2cc78ff50074fa6c6b47c9f6b04d92944d17f70561f0e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:1615",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:1615"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.polynomialPrime_disjoint_powers_X",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d5ecd3847ccfb1afac25742150ba28c319920f903af4dc78845e76329491ec24",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:3113",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:3113"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.ConeLocalLength.polynomialPrime_liesOver",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "db129fda609d720c176e41ffd9dc45b941643d0454d42e3072f80a273fe5b479",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:2009",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ConeLocalLength:2009"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W17.IsolatedIntersection.local_regular_avoids_retained_minimalPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.IsolatedIntersectionSteps",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "174525f6155a7188b034d7f6658d9f7b4a478f0b3a8f1e9721dd8ff60518167f",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.IsolatedIntersectionSteps:1141",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.IsolatedIntersectionSteps:1141"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W20.exists_linearCombination_avoiding_ideals",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.GenericCombination",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ea29a89a25b355aaa56bd70e12992cd844a14651075a04fa1df2cf787faf4ee0",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.GenericCombination:1208",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.GenericCombination:1208"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W20.exists_linearCombination_avoiding_primes_below_radical",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.GenericCombination",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5f62c2c324867046f2e8f61f79e6822b0c18926d11895db800eeaca48bcf559f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.GenericCombination:2051",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.GenericCombination:2051"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W20.exists_linearCombination_avoiding_submodules",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.GenericCombination",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bc0d14f1e1bba355c97213ddfc701c55e1d4516ca98a7de10061b2e8e5fd9cbf",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.GenericCombination:392",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.GenericCombination:392"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W20.prefixIdeal_homogeneous",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularPrefixes",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aba61bc7e1d03f289008f77d120013c44f3ce319e52a26fe428a749824dbafa0",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularPrefixes:1456",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularPrefixes:1456"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W20.prefixIdeal_succ",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularPrefixes",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bf912cc856321e239d372a6ce5675cb316afbcf2bbf33c142b60f9624181d724",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularPrefixes:225",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularPrefixes:225"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W20.regular_homogeneous_degrees_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularDegreePositivity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "09c5e409980f7b28b1386339659ae384112e3c12ebb9d53b317d4cfd389e87d0",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularDegreePositivity:1802",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularDegreePositivity:1802"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W20.regular_next_mod_prefix",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularPrefixes",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e5eee46f32c6ee2f5a6fd7d9d49d2770fe05eda4536d0dabdd3482a6bb4e987f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularPrefixes:535",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularPrefixes:535"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W20.regular_sequence_ideal_ne_top",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularDegreePositivity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3cb7f8f03e469e890b65233626679557ab9c917687f9bc2cac196d3eecb8ed89",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularDegreePositivity:290",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularDegreePositivity:290"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W20.regular_sequence_term_ne_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularDegreePositivity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fc6a34b8052effb524bc37cc0fbfa0886305969c95db32b3436d5417c0784e93",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularDegreePositivity:919",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularDegreePositivity:919"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W20.regular_sequence_term_not_isUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularDegreePositivity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b1d445f57b91306519db90f71597465992c186ec46884d9a77c36124cbbc906d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularDegreePositivity:596",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularDegreePositivity:596"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.affineClosedQuotientLocalEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a484d45d8c1f4d80b318ecf249a26b6678dee9ed5d7b43bbe62926ef95163635",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:6616",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:6616"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.affineCoefficientAlgHom",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c43edd3e51c57a8a3c43ca1b5e5bcf8d035b29a910c491831f42f0c8e6315c8b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:485",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:485"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.affineCoefficientAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2be63f0da4599239d9a56dbf516e9182cc6f379e1d208a431f9d0926998c1e4d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:929",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:929"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.affineCoefficientMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "db9326dd6a1edbbe297af026facb5a6b832b90943950e1ce0ad5f3cf6d4cc54a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:773",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:773"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.affineCoefficientMap_comap_closedPoint",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "63277f5ad1a40f8cf98412cd2f59083644bcf87d35c0347f92b1aaf1ad3dc3f9",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:1774",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:1774"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.affineCoefficient_isLocalization",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "540a041ff34de50bbd97c2bc0c01c4d33217b90ca4f0940d5cf764dbfa86ebab",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:1157",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:1157"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.affineDenominators_disjoint",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aea2b597405c5d54f2baef24cc469b40e0855ae86d9e5fd233203707159a8337",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:2315",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:2315"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.affineLocalQuotientEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bf47ab078d579e25db44eb9477aec2f0b3c1f6770b18ca76ced9719d08b9a97b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:6158",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:6158"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.affineMappedIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a94b58e5e52c9c0915f6890e7d03988f83b2b516671af315ce252f1df3e8e737",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:1484",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:1484"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.affineMappedIdeal_comap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c1bc7b3e95ae8c7e7ba484bb2075a7d2e421482eb91c8e348b9c8c38ba12282e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:3652",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:3652"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.affineMappedIdeal_isPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fb00bf5bfcae01a9555bd895e1fa98d102d200e926026a5e88f6d3030e7ea36c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:3003",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:3003"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.affineMappedIdeal_le_closedPoint",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8e33242bf87e7074b1cbeafab345ea74ee74e0d1accbf5184e0360feb44b420f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:3375",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:3375"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.affineQuotientAlgebra",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3cb17854d328cf63616c8addd82a89ac0af16b36397dad292e2d478509097480",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:7621",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:7621"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.affineQuotientMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "184b124db47687b98b542dc0d6229933902effab6d5b21995b55ef5d83e39273",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:7358",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:7358"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.affineQuotientMap_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "63372ca48a8cb42387f2ae2db28826359ccdff403d658bf1900aca161c1aeebe",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:9178",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:9178"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.affineQuotientMap_mk",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "335ed8a212791f98f4118d789816d31ea8ca26e2035b07d0643ff403e767e757",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:8195",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:8195"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.affineQuotient_faithfulSMul",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "34dd6f3a4d75b97beb84900c63b86cd1eb15d71cc3b8e7d1e56f5685173f7c26",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:9439",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:9439"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.affineQuotient_finiteType",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fbeb46e911edd9269ad4b2a869ca305a9e0cff3d7ab3948a350ab234599c97f5",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:10095",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:10095"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.affineQuotient_isDomain",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cc7ba63924403c04723316632a9c4977439ea16a9867a09a9474a8e823eb0434",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:9805",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:9805"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.affineQuotient_isLocalization",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3fe8365d29f80a2a326153d5e181a7c427e451a45a90c11fc674376bc44efdad",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:10476",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:10476"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.affineQuotient_scalarTower",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "88035e3be6dac486c9aded0ec39a223415551d5512e99019f13cbd7764215602",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:8436",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:8436"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.atPrimeEquivOfRingEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1884389e4a905b22b1a738ef1ddbe8022af6397e253ef14b862791a221e6181d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:9693",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:9693"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.atPrimeEquivOfRingEquiv_algebraMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "94dd29c5e70f140604a81eeee378a58edabed80eb17541e9472ce685d8f04a22",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:9945",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:9945"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.atPrimeImage_comap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c3a87fe564cb98e57e8ed79fa881b3598b184beab8f5318db0c46dbc8710aa6a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:9478",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:9478"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.closedPointLocalEquiv_algebraMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3ca3f750ac4622b60485c430876b88865a19b722a1d99989e4730080cf69feea",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:4545",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:4545"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.closedPointLocalEquiv_map_ideal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "de5393c5158a04e2f5cc865600d6a19276972ec3eb43b65af10c1c6780bf3a40",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:5672",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:5672"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.intrinsic_length_eq_of_ringEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientLocalizedLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e99f93e097c256e89dabfd0b9a7ed57eb08c4a703330572976016b43e7780076",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientLocalizedLength:265",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientLocalizedLength:265"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.localizationQuotientParametersEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "707b1503fef9477f8076fb6421d3cde3f420405626c9365973a9e255fdf48a41",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:6206",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:6206"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.localizationQuotientParametersEquivTrans",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "51fb2d8e0b87a2676ea9b06777b917f4db2d89b63a907c850f0969c230311a6b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:10358",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:10358"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.mem_quotientParameterPrime_mk",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "63ffdaeef351068d0524fb42db71f50ec48c2e758d5953be76d8ee34b99561a5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:1056",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:1056"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.originalLocalCoefficientLocalEquiv_algebraMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4d63e3b349eb6c6669205d6a01195a908d4176957f2b9391d513118d1964da8b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:4051",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineClosedPointLocalization:4051"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.parameterEquivImage_isPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "edae43c6d86b68ea4e6c1853ff57b4e4503bab2b9dda5de70f643094f21d58f2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:9320",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:9320"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.parameterLocalQuotientForward",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "510c80ce3f40b7808d03dec5e29099452d7762eaca7da314bfc10d3965eb747e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:2651",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:2651"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.parameterLocalQuotientReverse",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a8317471b7b9d5993b1ec7715cd81d8fa49e15218522d079712f7cb531e0375f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:4427",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:4427"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.parameterLocalQuotientReverse_algebraMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f5ac8aedd7fba0d2b58e51fda26a76dcacf78426ef9350841b5c86d80e00e59b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:4788",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:4788"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.parameterLocalQuotient_forward_reverse",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "35f9068a86527a16f5c6f551fa276f77ac082cf7a0f47d750fd5081762fe1020",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:5626",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:5626"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.parameterLocalQuotient_reverse_forward",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5e23cd4d8471d53fa668b8bb300004ffc6052f408389dc0e6f4280522005d07e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:5074",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:5074"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.parameterLocalizationMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a3a8c414e68d9a6b3f874dd445f205afbe515e7e82299f7e83f8abc73de087df",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:1459",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:1459"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.parameterLocalizationMap_algebraMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "90a135a65cc5bcd2335c8ddfd9578108c897b41c3144eec21e847116b2309e10",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:1963",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:1963"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.parameterLocalizedIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "63d2d7d8a53550d5155266d183b7d76eef4194813e022a215d0138e4231c8ee2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:1255",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:1255"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.parameterLocalizedIdeal_le_ker",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "71b25a471d17b846eb2d796dd0cc01882daeba43f84b4934a9dddc532dedfd52",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:2257",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:2257"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.parameterQuotientToLocalQuotient",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "765918af57a0b9d00f0688bf941ae810eadfc8a3f1bf66c273e8ebce968b90ac",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:3217",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:3217"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.parameterQuotientToLocalQuotient_mk",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "750aa06322a35b38dfadbb3f3e55d7907eae6d0588b7a45943ada9e97cbb8d42",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:3556",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:3556"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.parameterQuotientToLocalQuotient_units",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fded80f171b42788d0e511697d09b248b71aacf80e7aae7ca042751f5fde4dd8",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:3802",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:3802"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.quotientParameterPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7e4e0bddc95e979014702d1936bd9c36cc0ae69d10441f8c8d575ab09b0a537e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:352",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:352"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.quotientParameterPrime_isMaximal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1764f6cbde0995efdd77269e1fd39c44c77b981d8ff66c7d53c25aac262b1559",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:752",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:752"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.quotientParameterPrime_isPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0e424dfa48683932074860bd10204d06f57d82ae66fa88ea913e18922e61db9b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:466",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters:466"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.quotient_localized_length_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientLocalizedLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7495941e3a1f011a9fc2ea119a3448a0bf23219e1ed5cc7f1577a65d03fba18f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientLocalizedLength:1408",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientLocalizedLength:1408"
    },
    {
      sourceName := "OAI.PiExponentSiegel.W23.quotient_localized_length_eq_explicit",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientLocalizedLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b1c1c479fba860d7aa9aa6b70ac6ca66b5bc3b1b04f515f06f6ea8e6cec4ec91",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientLocalizedLength:2272",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientLocalizedLength:2272"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_045.jsonl"
