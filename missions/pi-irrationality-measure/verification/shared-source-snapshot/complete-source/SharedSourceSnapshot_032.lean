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
      sourceName := "OAI.PiExponentJets.W22.instIsPrimeValIdealAndMemSetMinimalPrimesLe_oAI",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedMinimalPrimeFamily",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cab753c49f31b472a7f3aa8ac3a012f76551dd5ced4742be90d9d0fe6ba1f376",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedMinimalPrimeFamily:624",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedMinimalPrimeFamily:624"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.length_eq_of_semilinear_bijective",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientLengthEquivalence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b1ea21db2af512eb5a95463536247a7c1c5084728241fd084df1de04f2bf5b6f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientLengthEquivalence:138",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientLengthEquivalence:138"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.linearCombination_eq_parameterCombination",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FinsuppCandidates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "34bdf2016de953bf38440465988c511c1cc1a5711ab9be7dfc2e6664e859e15e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FinsuppCandidates:221",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FinsuppCandidates:221"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.linearCombination_mem_ideal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FinsuppCandidates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e5e23e715e46933b78091c4b46b1dbed11011f4debd055a6f180d224b2999ad7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FinsuppCandidates:851",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FinsuppCandidates:851"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.linearCombination_totalDegree_le",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FinsuppCandidates",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c9d9b89f5f452977e6dbb6de088f6ef9590b8a93ef1254fa6377ab789c9dca1b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FinsuppCandidates:513",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FinsuppCandidates:513"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.localPrimeTowerEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPrimeTower",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0b93545063dd6904757a0da95e10aa55f74965b5d7f448e4c1c5e0c5eb81b33f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPrimeTower:287",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPrimeTower:287"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.localPrimeTowerEquiv_algebraMap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPrimeTower",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7de89b2f0190d0feec8c2a40f46dd012be941b3fde8d7cf186f459c12ffaa238",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPrimeTower:610",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPrimeTower:610"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.localPrimeTower_map_ideal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPrimeTower",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "50b346afaa72c977bddbacfd1195b2b6c528580407f9c92c0427c235645d27da",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPrimeTower:971",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPrimeTower:971"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.localPrimeTower_quotient_length",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPrimeTower",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "257c01fba99f04dce5e310dc04b232c84f69d25b144a8eaa1585197377e6f050",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPrimeTower:1815",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPrimeTower:1815"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.local_regular_list_avoids_parent",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousListHistory",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a969a53c1e823d002c79f08f3aeaa98a272aaffe279e1b930880a2f1bc7903e6",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousListHistory:1393",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousListHistory:1393"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.localization_map_cut",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedOneCutPropagation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4e69b7be44f32415a852fbeca6115dfbe9416854187901c57e89b03f1fd50152",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedOneCutPropagation:765",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedOneCutPropagation:765"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.localizedCyclicFactorEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedCyclicFactor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "661e49a36267decacc89c42bb0374ddb4c35b9333e8a8e2179fd849ffac77d59",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedCyclicFactor:867",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedCyclicFactor:867"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.localizedMinimalPrimesEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedMinimalPrimeFamily",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2283495437435ebfbb6d41d2438d40d7c26d8bcadfabe9f4bec0dc7cdda8464f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedMinimalPrimeFamily:718",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedMinimalPrimeFamily:718"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.localized_cyclic_filtration_length",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedFiltrationLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "942731da45006c7cb76328fdb759ce90811caf9fee74f3b391894534aaf13ad6",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedFiltrationLength:334",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedFiltrationLength:334"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.localized_onecut_parent_recurrence",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedOneCutPropagation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e1cf79ef94d53f51d128895380bc8b524a4566abf8e342fe7fae47a6e7c89cfb",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedOneCutPropagation:2391",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedOneCutPropagation:2391"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.localized_prime_factor_length",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalComponentDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8720ddb78c64297923da40c7646926f260d4705cc561229b27fa94baf177804f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalComponentDegree:1889",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalComponentDegree:1889"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.localized_prime_factor_length_one",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalComponentDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "20cbd06190ae07acb6167a078838d51bd48562abead453c477d5635f92b49a7e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalComponentDegree:1140",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalComponentDegree:1140"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.localized_prime_factor_length_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalComponentDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "51d941eaad442a5ad9d0e3bc373578bfa5bdc2a61e5cb73aae63ceac9bcebcc4",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalComponentDegree:830",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalComponentDegree:830"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.localized_quotient_length_eq_of_ringEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedLengthEquivalence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "974bce09fc945140c82a2f2a3a8fb785728c4e2bfdfb088039e516a8c79e4a31",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedLengthEquivalence:1639",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedLengthEquivalence:1639"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.localized_radical_eq_maximal_of_mem_minimalPrimes",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedRadical",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "229cbee7d6bf97f52259785c132d910d49768b6459e3f1ec63914fae19fb2364",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedRadical:156",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedRadical:156"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.map_colon_singleton_localization",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedCyclicFactor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9a2c3e73b9b05d941c743a151fa1c15db7380c681d5cb748489d4df6e81ce757",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedCyclicFactor:255",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedCyclicFactor:255"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.map_ideal_eq_top_of_not_le",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalComponentDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "324fbdd43cc2d02a62aa2ee465b981ba5925dec9886ae6b000394b04bc54743f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalComponentDegree:391",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalComponentDegree:391"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.mem_minimalPrimes_of_localized_radical",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedComponent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ace4b8c3e6afc0bb7783f804c2cf5dddba7cc55e9053d7a519742bfa3f2d7b59",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedComponent:372",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedComponent:372"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.minimalParentsBelow_fintype",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedMinimalPrimeFamily",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "af1b62989a3a8cdbfec4367247ce199ee49e76599d811a2e791ac01619bfd9bb",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedMinimalPrimeFamily:307",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedMinimalPrimeFamily:307"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.minimalPrimeCutSum_localization",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedOneCutPropagation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "89e569d2eef632615a6d11c4c85ff6cadf179235c807603c61dd04c0fa16f8fa",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedOneCutPropagation:1123",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedOneCutPropagation:1123"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.minimal_cut_of_intermediate_parent",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.NaturalMultiplicityPropagation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e4dccf3f1b8c3af529a64e833b61d1e9068bc223be36519ba79d7d9b51b94bd7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.NaturalMultiplicityPropagation:296",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.NaturalMultiplicityPropagation:296"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.natural_local_onecut_recurrence",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.NaturalMultiplicityPropagation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5aaac85be5278b3c8d59b8b45426f952f919c871c8a6e649ae252c166a8538ca",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.NaturalMultiplicityPropagation:1140",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.NaturalMultiplicityPropagation:1140"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.parameterCombination",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterCombinations",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "74b5e7163875e0dd3e3834a0fbffd54643d2521acbf2d9bcb83eeafffc4f7180",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterCombinations:205",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterCombinations:205"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.parameterCombination_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterCombinations",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a83cfb33bbba327b49f466988bb9da432fabe3e490a811b6cd4c890282180042",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterCombinations:958",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterCombinations:958"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.parameterCombination_totalDegree_le",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterCombinations",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9adc245128f9d5331a117f765b6cc97a59841338c928b3d35ec4c045e07f49e0",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterCombinations:380",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterCombinations:380"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.parentChildIncidenceEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.NaturalMultiplicityPropagation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8c70112c75df35af6e034e21d4b9ac300607410f6af29dd8024bd2e0f8630b5b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.NaturalMultiplicityPropagation:2854",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.NaturalMultiplicityPropagation:2854"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.polynomial_eq_of_nat_tail",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HilbertPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "475f64c70a6b2f840d318e7e8ee1465c4cd07c218b277ddb813f5842538f4c6f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HilbertPolynomial:586",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HilbertPolynomial:586"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.primeCompl_map_eq_of_comap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedLengthEquivalence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "24c4689f74b07f99885c66e68e64cbb6d9d0f8a8f0814844d6e2cbd8ee9824b2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedLengthEquivalence:232",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedLengthEquivalence:232"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.primeCut_isHomogeneous",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeCutBudget",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6a8ebb2107a75b76bc83139433128bb1757abeff69c3d8e7014eb348d7735e8a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeCutBudget:1603",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeCutBudget:1603"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.primeLocalizationEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedLengthEquivalence",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7e2a22561f221a728f5da48bfb205a4d777e8f785df615867cc38afdd043b4fb",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedLengthEquivalence:781",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedLengthEquivalence:781"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.primeLocalizationEquiv_map_ideal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedLengthEquivalence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "85de91e141372dcef5223facaedb0046fb69f2a43676cbf18f97a2130087015c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedLengthEquivalence:1132",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedLengthEquivalence:1132"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.primeLocalizedCyclicFactorEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedCyclicFactor",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "159270af7405da990d9ef339dcd285106e6e499389c9a1b0b2876450b005c27f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedCyclicFactor:1426",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedCyclicFactor:1426"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.prime_cut_component_budget",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeCutBudget",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1cd7c1cace4c81f4ed5157bec01eb9f508c5e1bc44b87fab92a28051949c39c0",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeCutBudget:3265",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeCutBudget:3265"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.prime_not_le_of_ne_minimal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalComponentDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7d68b0ea5c87463ac0ef8fb363c0aa02a8f44c64300b68a0bee509d3a68e98c7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalComponentDegree:1651",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalComponentDegree:1651"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.quotient_length_antitone",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "266ac2ecc73fb30a87c6189561cf4d8dd793d10854789a365b294fd3f621cf09",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalLength:201",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalLength:201"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.quotient_length_eq_of_ringEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientLengthEquivalence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "62ae3e83568b2930de5e4130a49f45ba422d67dc04bc2fad28b3bcd7ba51686a",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientLengthEquivalence:579",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientLengthEquivalence:579"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.quotient_length_eq_sum_and_last",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SubquotientLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3d29838f6074a9cfbd70fe36498f564bd2d42c3816a952b40c544ecd48fe1b3d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SubquotientLength:1487",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SubquotientLength:1487"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.quotient_length_eq_sum_of_last_top",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SubquotientLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "271c024b28a20414fee561f4f2ca863764aa49f217e45ba84c45797efc4c7d50",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SubquotientLength:1954",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SubquotientLength:1954"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.quotient_length_step",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SubquotientLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "35ceae07d6acaad692f8a1eaa2010117af09e04b837472a8189ca930866ba920",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SubquotientLength:835",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SubquotientLength:835"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.radical_mem_minimalPrimes",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedComponent",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "29f4b2c339c2bca85b3b80c6dd71b6d62a6c198c3cf569c37715f77e3fcfb7c0",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedComponent:147",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedComponent:147"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.rational_filtration_telescope",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertMultiplicityFiltration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e2eb605f9d065013ca06ef1e4051bc213594479698a58af57310e8f198dfeb8a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertMultiplicityFiltration:2521",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertMultiplicityFiltration:2521"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.regular_degreeAt_product_ne_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CompleteIntersectionComponentBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1aa1aa321d76e94edd9849495d4b6a86ae8b7c04a598aeb3b1b796cfdccc7eee",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CompleteIntersectionComponentBound:1219",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CompleteIntersectionComponentBound:1219"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.span_range_list_get",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineLocalRegularBezout",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fed181ae5b44d5755ba086e49466cdf23b35de063a8d86a25fd4c35cb85d46b4",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineLocalRegularBezout:542",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineLocalRegularBezout:542"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.span_range_map_list_get",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineLocalRegularBezout",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3454fd6652311a975b99f8938239b036ec51b1101ff410720488dd1eca9a1780",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineLocalRegularBezout:728",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineLocalRegularBezout:728"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.subquotientEquivImage",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.SubquotientLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f2cc314433ed3c00581097355c6275dd457d55cd10f13c799b97f8173d0b7e19",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.SubquotientLength:281",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.SubquotientLength:281"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.zeroHomogeneousIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2586db760e8b789956c4ccd176885e183daf0c7104d31d662dfab9cc9fdca8a8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:518",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularCutHistory:518"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.affine_prime_dimension_of_closedPoint_presentation",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffinePrimeDimensionBridge",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9f792e74d3bd4c20860e38d6b8b940c854228b2477c7d4df78d0ebf9ba409454",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffinePrimeDimensionBridge:225",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffinePrimeDimensionBridge:225"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.affine_prime_quotient_dimension_eq_basis_card",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineResidueTranscendence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2b2e380aa2e22f49ef13061e0398bfdd837b5b25bc8495020b48be04c6d0e38d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineResidueTranscendence:1358",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineResidueTranscendence:1358"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.affine_prime_quotient_dimension_eq_residue_trdeg",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineResidueTranscendence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f318a7a147a7f5c60c854ce234001bd75ff9fa7b263b51e7e7036a7c4c41c522",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineResidueTranscendence:789",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineResidueTranscendence:789"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.algHom_surjective_of_residue_cotangent",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CotangentGeneration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5badaf89d801a2b41a9412b82b96f185cd9ff0302783a1e4666ad703e4ead48b",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CotangentGeneration:807",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CotangentGeneration:807"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.augmentation_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.IntrinsicLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e66ce5e56cc52deb42d2119b12091ef8beef54a3faad9ee0e559aa034d200666",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.IntrinsicLength:165",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.IntrinsicLength:165"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.coefficient_localization_dimension",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineTranscendenceDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6fdd6926f12a41e8bdd7aef092a2b59ec00be49c68ca6b5963e1a91e2fdf9430",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineTranscendenceDimension:2567",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineTranscendenceDimension:2567"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.coefficient_trdeg_eq_prime_quotient_dimension",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineResidueTranscendence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "38cf4e2095bc176c3e2921de0a0cc64fb8cf1ea94f2423adf70f91404224a10a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineResidueTranscendence:2758",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineResidueTranscendence:2758"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.corrections_of_mapCotangent_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.CotangentGeneration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9dead5cdf064afcc6ffa0e581166e334873132563bd20d740ab80bbf19c6ba00",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.CotangentGeneration:258",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.CotangentGeneration:258"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.exists_chain_lift_last",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "39fb0e67eb6774d4925714e39aab3fa026a2ebb909928ba73256d4132e053694",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertDimension:329",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertDimension:329"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.exists_eventual_cumulative_polynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCumulative",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a82a245c2cbdcd0e7a2608068d36e0351f9cfad373aa253df601c46e1605a631",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCumulative:3216",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCumulative:3216"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.exists_finite_normalization_with_dimension",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "428ab11a3917c6fa5a313a0e55b26d928cccadaf3bbb975d6b3fbea941a4afeb",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertDimension:3090",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertDimension:3090"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.fin_polynomial_prime_pair_local_dimension",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d3ebc9686599ec070f8773924cd19fec7a7ce6013759b9e32ff07da7dc43d397",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeDimension:4080",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeDimension:4080"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.finiteType_domain_krullDim_eq_trdeg",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineTranscendenceDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "355780666bb5c29135774b8109acbd706b711f459a6541bcae49f87d6b5cb96a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineTranscendenceDimension:1167",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineTranscendenceDimension:1167"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.ideal_power_corrections",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.GradedGeneration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a3c09c2cb5fa109ae7498e879210c024ccfe6cbfdbd0660dc7cbaaa2423542b3",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.GradedGeneration:671",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.GradedGeneration:671"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.imagePrime_isPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0dfacfda7cbc07aa84cee98d50bdb9a142ee99e1e04b6c9649c99b19f5fe1077",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeDimension:556",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeDimension:556"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.krullDim_le_of_goingUp",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cabac69acf03e34b8009ec04f18a2b58e9ab2596ed88a8f1764c1189d60d8624",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertDimension:996",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertDimension:996"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.length_eq_coefficient_length",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.IntrinsicLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0a17859f082fd7c7e08bed5b669a57e1d2cbe4269d72e479e94a525387b158d3",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.IntrinsicLength:2007",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.IntrinsicLength:2007"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.localization_trdeg_toNat_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineTranscendenceDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "801b59ad20b51033b0dd15c533c8601fb8f54459535a095997170d689fc02d5d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineTranscendenceDimension:1989",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineTranscendenceDimension:1989"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.minimal_prime_hypersurface_dimension",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHypersurfaceEquidimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e1638bacedc38bb225c696d2e98ce41948302ff6b5ac4d4486fa1b803e0f3f27",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHypersurfaceEquidimension:249",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHypersurfaceEquidimension:249"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.module_length_eq_finrank_of_augmentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.IntrinsicLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0f7e804e26bbe61319080923c13d65f373a3acd8ff36f5cbdfc428c81aec4a7c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.IntrinsicLength:3251",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.IntrinsicLength:3251"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.natDegree_affine_comp_le",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertGrowthComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7a84020bcd38c95caf466537d1eefc6b1275f992e1455f34e6cf6565b1689535",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertGrowthComparison:729",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertGrowthComparison:729"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.natDegree_eq_of_polynomial_growth_bounds",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertGrowthComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aff9b6723e23ea61c1eef4c6888ee321c88b74f937c278b22912583dcd6d0e9f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertGrowthComparison:1123",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertGrowthComparison:1123"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.natDegree_le_of_eventual_polynomial_le",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertGrowthComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "22e9fa00d5ad3cd89a73435a9eb4456bf4c0ef530f88109182457916940516ed",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertGrowthComparison:138",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertGrowthComparison:138"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.normalization_binomial_lower_bound",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8cc6cdb63ea9308ea58f32cc70c6b1eb9760c5e3137ad1f2789274d5575dd24b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertComparison:657",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertComparison:657"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.normalization_binomial_lower_growth",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7bfbf453954a9da9695ce7aa5f1bffc0272e48f906fbb095b756df6c4d4f4109",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertComparison:1725",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertComparison:1725"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.normalization_mem_quotientDegreeFiltration",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.NormalizationGrowth",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "076609fc06b27538fa586609ddf388a39efdb10212d354fef07417097fc4bc89",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.NormalizationGrowth:2095",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.NormalizationGrowth:2095"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.normalization_trdeg_toNat",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineTranscendenceDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ded13bac2088f382862a84ef94e7dace9083f3bbc5efa6ae3345d04c10d0367d",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineTranscendenceDimension:354",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineTranscendenceDimension:354"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.polynomialPrefix",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCumulative",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "06c72ede97add1f4e9d8d6962efcead3508f0fac40b31698ce2cb672c86cd04e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCumulative:1297",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCumulative:1297"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.polynomialPrefix_degree_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCumulative",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3e4edfc0d0bb86dcfdce6278820058a4ca5bbf043b7707e85604a6c799978c68",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCumulative:1851",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCumulative:1851"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.polynomialPrefix_eval",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCumulative",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "537f57b8a29fb8e7faececbee78722633d4cef08efaf0a2b4e682dd0121f0e03",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCumulative:1454",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCumulative:1454"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.polynomialPrefix_natDegree",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCumulative",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8f78a195fe82298de336f4631d4e035cd76dd045d9d686ec552c65ab6a0b21ea",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCumulative:2882",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCumulative:2882"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.polynomialPrefix_top_coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCumulative",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "de5de3443180572789dee18ed6e56fdcc7627c9c70a40f36a506a5b936168c8e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCumulative:2187",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCumulative:2187"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.polynomial_prime_pair_dimension",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e9c33da3c806bdf4e6b2b966d023c8012b3ef03263957931ed860b5f730c4a7a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeDimension:6328",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeDimension:6328"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.polynomial_prime_pair_local_dimension",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4f0b63e1becdff4abd7f29fc6afc3f30d232b5b863c4a0c73ff38bd7b9f086f1",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeDimension:5373",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeDimension:5373"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.powerPrefixPolynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCumulative",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5df455c6a782b3222d35aaaa8e62af6bba507e803d66799656f25ed70fe42321",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCumulative:199",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCumulative:199"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.powerPrefixPolynomial_degree_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCumulative",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2d22dcb8e1ede8234eed72037ff45ce9f67d91c7ab60dc2e64fd01e63531dbd8",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCumulative:712",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCumulative:712"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.powerPrefixPolynomial_eval",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCumulative",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9c4dfc145431b680d1fc75d63fdfe83d4d47c4141e81751ab46d674120f598ca",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCumulative:362",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCumulative:362"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.powerPrefixPolynomial_top_coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCumulative",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5408052b289163ca0c5ec39eaa59dd258e1d862b70410bd1ab72470d4b1de7b6",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCumulative:1091",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialCumulative:1091"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.prime_hilbert_natDegree_add_one_eq_krullDim",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "52a608dcea525e4a9f24e53a634a3ca0f74f4453a8bbfec14cc0fb0f5e1bb137",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertComparison:3126",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertComparison:3126"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.prime_quotientDegreeFiltration_finrank_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertComparison",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5c00c141f381b85a8d50365ecec73a9c25b73d4b5c7534d67752f66cf995e51b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertComparison:2517",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertComparison:2517"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.proper_prime_cut_relative_height_eq_one",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHypersurfaceDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "afafe17a0bde97a8a0f562e83a5092f919996f58c08c7dca0a700cabc0371c5b",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHypersurfaceDimension:1491",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHypersurfaceDimension:1491"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.quotientDegreeFiltration",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.NormalizationGrowth",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3d88fd7ec1ad1e1791b6d6d2b34de5f87c9e9c95d4e9569acb042bc37aa96a81",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.NormalizationGrowth:1671",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.NormalizationGrowth:1671"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.quotientDegreeFiltration_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.NormalizationGrowth",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d9afd4d34a5776bc9d16a535a6ae800d602abbac9b7814531c0403c8c7d9b27f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.NormalizationGrowth:1882",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.NormalizationGrowth:1882"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.quotientPrimeResidueAlgEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientPrimeResidueBasis",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a4e9a39115474c02017ce21720847efe3be486e3a9119ca8c5ead0d71468163e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientPrimeResidueBasis:1943",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientPrimeResidueBasis:1943"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.quotientPrimeResidueAlgEquiv_basis",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientPrimeResidueBasis",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bd79daf6b0616cb57ceb8efa5525545216d7951ee628391abbc25b1c56bb459f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientPrimeResidueBasis:2607",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientPrimeResidueBasis:2607"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.quotient_prime_comap",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientPrimeResidueBasis",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5b89da565042f075d4cbe777c4967736936084560568d7f26b26d02ccc1a918a",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientPrimeResidueBasis:1639",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientPrimeResidueBasis:1639"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.rational_coefficient_trdeg_lt_aleph0",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineResidueTranscendence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ad46accd091b32e3d8a69d21176e76e099abc289e0ae5c1abe4702dc3461c6ee",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineResidueTranscendence:2221",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineResidueTranscendence:2221"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.rational_coefficient_trdeg_toNat",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineResidueTranscendence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a2d18ee045e1b073cae43b5ca840f69f3dd288c639f894c4eeb436c876ada699",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineResidueTranscendence:1849",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineResidueTranscendence:1849"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.residue_corrections_of_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.GradedGeneration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "20a08e1d3fc794d9da3977b37e0b3b6f37c50b3e2bdb7136e28e6e574f789e76",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.GradedGeneration:229",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.GradedGeneration:229"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.ringEquiv_localQuotient",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeDimension",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aaf9b94e895910340b2daccec573cafe64bd47cf7913d6de35a8b968854caab5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeDimension:1115",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeDimension:1115"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.ringEquiv_localizedIdeal_map",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7e0f429b4a3822c29396e047558ffe1f0a417eb6a68a6a4b4a5ce60d25e2fa88",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeDimension:702",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeDimension:702"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.ringKrullDim_eq_of_integral_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "be9aaf7fbb4380cd91e1f01f4b8c096843d64ddc31f0b56e6d6b6fab91ebeaba",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertDimension:1489",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertDimension:1489"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.ring_length_eq_finrank_of_augmentation",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.IntrinsicLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9a5750a9473a63fa2fa6be1a02be09c04d8ccf0283c8c11bd52a117e67d4d31f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.IntrinsicLength:3856",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.IntrinsicLength:3856"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.simple_annihilator_eq_augmentation_kernel",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.IntrinsicLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c1ea3ca025b020f855ff811a3993abdff77da1de78c198b8ed19f68d5140d9f4",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.IntrinsicLength:365",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.IntrinsicLength:365"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.simple_over_coefficient_field",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.IntrinsicLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1a040cc5d3f01b0cf2f6c89e86b7ed6cdc730609bcd43d0642f2af1947c87ac3",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.IntrinsicLength:1447",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.IntrinsicLength:1447"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.simple_smul_eq_augmentation_smul",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.IntrinsicLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b76f2022e7b1fa99d8fa9a6f295d92bc7c1396a61e7de0dbf51b112ebce7de32",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.IntrinsicLength:875",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.IntrinsicLength:875"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.split_polynomial_prime_pair_local_dimension",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5aee8a1663efdd207d5c78ea66b1330c06e038d107c261f5933c5319c04b3aee",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeDimension:1666",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeDimension:1666"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.surjective_of_finite_corrections",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.FilteredLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f28f9b0d0cc3b95b3226aa7701ab7ae3cbf7099f4ee9ba397461fb0e806d3cef",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.FilteredLength:1642",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.FilteredLength:1642"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.surjective_prime_residueAlgEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientPrimeResidueBasis",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "30697e0d478b3ef33bb47dd4c3e87ab354026e6340f71ed0dbaa64ad3812a761",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientPrimeResidueBasis:317",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientPrimeResidueBasis:317"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.totalDegree_aeval_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.NormalizationGrowth",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f6d6594b111e44524eb4544e342323b900370a2285ff287e73a9c3b96ba3c273",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.NormalizationGrowth:320",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.NormalizationGrowth:320"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.trdeg_lt_aleph0_of_algebraic_tower",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineResidueTranscendence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cf819efb36edf9c3039732b3a9789388f942836aa5e63b5e7ae06cadcd9a47e9",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineResidueTranscendence:237",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineResidueTranscendence:237"
    },
    {
      sourceName := "OAI.PiExponentJets.W24.trdeg_toNat_eq_of_algebraic_tower",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineTranscendenceDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "baacba524b0adeb8a28d5a638c4aba5a5375b0eee79a094dc2c7e1b941f24f14",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineTranscendenceDimension:1697",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.AffineTranscendenceDimension:1697"
    },
    {
      sourceName := "OAI.PiExponentJets.W25.cumulativeHomogeneousQuotientEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CumulativeHilbertSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d199351dc79664e73178c28d0341254c75f15897ca2ff7e285704f9ca12c5956",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CumulativeHilbertSections:2394",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CumulativeHilbertSections:2394"
    },
    {
      sourceName := "OAI.PiExponentJets.W25.cumulativeSectionMap_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CumulativeHilbertSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d0aa4845c6e2045fb479b8727f1b5dece1ba4f5a6ab29a2f6324dd907a2e2f2c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CumulativeHilbertSections:1749",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CumulativeHilbertSections:1749"
    },
    {
      sourceName := "OAI.PiExponentJets.W25.cumulativeSectionMap_range",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CumulativeHilbertSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1ca6656b51c3becbae0157a1e91912316dd4fe614612508229156ac42f85cac1",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CumulativeHilbertSections:2084",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CumulativeHilbertSections:2084"
    },
    {
      sourceName := "OAI.PiExponentJets.W25.length_baseChange_of_flat_local",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FlatLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7c7887bb89c5da2112073daa7990453b5d94f58360f67a216fd3580ce8895993",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FlatLocalLength:1369",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FlatLocalLength:1369"
    },
    {
      sourceName := "OAI.PiExponentJets.W25.length_quotient_map_of_flat_local",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FlatLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2604d3f3d8ecfb5ec73c91d12df472c4f3173c6ab03139adf2292fcf705634eb",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FlatLocalLength:3474",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FlatLocalLength:3474"
    },
    {
      sourceName := "OAI.PiExponentJets.W25.quotientDegreeFiltration_eq_iSup_sections",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CumulativeHilbertSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3f9b7ead7b47fd8fb60d67548dc8278e3a8b923445b7d55986ce139ff6aff21e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CumulativeHilbertSections:1434",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CumulativeHilbertSections:1434"
    },
    {
      sourceName := "OAI.PiExponentJets.W25.quotientDegreeFiltration_finrank_eq_sum",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CumulativeHilbertSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "31eb28cafb09cf3216d37a9c1deb4e0c7addb6571adbdc4955fe84c24f21db58",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CumulativeHilbertSections:3661",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CumulativeHilbertSections:3661"
    },
    {
      sourceName := "OAI.PiExponentJets.W25.quotientDegreeFiltration_finrank_eq_sum_fin",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CumulativeHilbertSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4452cf5cbac5b9be79a17a26d64ecbb030ebd2777dd36aa1bd0a535298653714",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CumulativeHilbertSections:3271",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CumulativeHilbertSections:3271"
    },
    {
      sourceName := "OAI.PiExponentJets.W25.quotientDegreeProjection",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousQuotientDimension",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7047aeacc1122a549baacc3f96f79828392b081dabebf6ba4eb9530e99748273",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousQuotientDimension:456",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousQuotientDimension:456"
    },
    {
      sourceName := "OAI.PiExponentJets.W25.quotientDegreeProjection_mk",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousQuotientDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c305cc85dac589851f32290405dd849820b6e871fb49d4757a8f6009ef934884",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousQuotientDimension:1100",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousQuotientDimension:1100"
    },
    {
      sourceName := "OAI.PiExponentJets.W25.quotientDegreeProjection_of_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousQuotientDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a0ee5f457f05f6f2b633f236ea8b1c209b42c4d01d4cc061ea4b87435c01e585",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousQuotientDimension:1461",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousQuotientDimension:1461"
    },
    {
      sourceName := "OAI.PiExponentJets.W25.quotientSection_iSupIndep",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousQuotientDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ac66d4c1639f3618b7c3b5772584109b4e8ec5f4d548da6f1d666435a3d3c1d7",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousQuotientDimension:2178",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousQuotientDimension:2178"
    },
    {
      sourceName := "OAI.PiExponentJets.W25.restrictTotalDegree_eq_iSup_homogeneous",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CumulativeHilbertSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "058a016996a3a3eaff24589d794e91beb67e7765d187d45620027e4908419790",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CumulativeHilbertSections:426",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CumulativeHilbertSections:426"
    },
    {
      sourceName := "OAI.PiExponentJets.W25.simple_baseChange_of_map_maximalIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.FlatLocalLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d49c26c620467bc33551718c30a860cf8541e92e8bac7ee59bb97a049805b487",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.FlatLocalLength:375",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.FlatLocalLength:375"
    },
    {
      sourceName := "OAI.PiExponentJets.W27.backward_difference_degree_and_leading",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertDifferenceDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1ff526e043002d10ee03b37774ae39c92daf7b22b02fee2e32194593efd96ff5",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertDifferenceDegree:1689",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertDifferenceDegree:1689"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_032.jsonl"
