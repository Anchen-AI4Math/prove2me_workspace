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
      sourceName := "OAI.PiExponentJets.W27.backward_difference_eq_comp",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertDifferenceDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b39a7c5a72e536f50de6b74e0c8ecb0bcc24f85e19e3e0e4a2d3672670f505f0",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertDifferenceDegree:3073",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertDifferenceDegree:3073"
    },
    {
      sourceName := "OAI.PiExponentJets.W27.backward_difference_multiplicity",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertDifferenceDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "df6aabe5055eadd26e57b9cfedb38ec54cec639adb9652b870fcb1e10e45f20e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertDifferenceDegree:2608",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertDifferenceDegree:2608"
    },
    {
      sourceName := "OAI.PiExponentJets.W27.difference_taylor_coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertDifferenceDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "07731e5c079b6d0abe8264b28a14771952530926a85f34b2a3aff480e9986ff0",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertDifferenceDegree:187",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertDifferenceDegree:187"
    },
    {
      sourceName := "OAI.PiExponentJets.W27.difference_taylor_natDegree_le",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertDifferenceDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c45aaa7e5d64742d1764a9bd6f0d78d510eddf372f7838a0911b67a6c68ff249",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertDifferenceDegree:1112",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertDifferenceDegree:1112"
    },
    {
      sourceName := "OAI.PiExponentJets.W27.eventual_hilbert_degree_ge_one",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "26a406cad010c2a8e90b97146ce0757e584297bdf2b83b7d8234a401a7d0802a",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertDegree:3294",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertDegree:3294"
    },
    {
      sourceName := "OAI.PiExponentJets.W27.factorial_leadingCoeff_is_integer",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f950dae5ff3353e26b8adad27401068c36d78ac132647dfa484136ec6e0d4808",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertDegree:2482",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertDegree:2482"
    },
    {
      sourceName := "OAI.PiExponentJets.W27.polynomial_leadingCoeff_nonneg_of_eventually_nonneg",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5fa8fff1570d237f5adce1eccd8760e5a28de555a424af51c97ab295b0403abe",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertDegree:1090",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertDegree:1090"
    },
    {
      sourceName := "OAI.PiExponentJets.W27.polynomial_leadingCoeff_pos_of_eventually_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a152772cb64cda57d3d6295d0fecc03f1551b792e21629bd846b7ac999e32950",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertDegree:2049",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertDegree:2049"
    },
    {
      sourceName := "OAI.PiExponentJets.W27.prime_eventual_hilbert_coefficient_ge_one",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c5f5622b490bbf352a0b4e4821da411bdbfe34a324ec7397826477b52f543d49",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertDegree:4520",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertDegree:4520"
    },
    {
      sourceName := "OAI.PiExponentJets.W27.prime_eventual_hilbert_degree_ge_one",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ea9a6bace08276758167ce628227398c0418e6471245ca2c9bcfb7ef69ee255d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertDegree:4066",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertDegree:4066"
    },
    {
      sourceName := "OAI.PiExponentJets.W27.prime_quotientSection_finrank_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a2c8dab21ccf4a1dddeb40cca6ff7b978e5fbd1afa8d74ca8b5de5a7413857af",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertDegree:432",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertDegree:432"
    },
    {
      sourceName := "OAI.PiExponentJets.W27.quotient_eventual_hilbert_coefficient_nonneg",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeDegreeExistence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "feb6e33163f8e5417a65f947bb5310ca110f9fb09d3a754e109153e508e837b9",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeDegreeExistence:976",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeDegreeExistence:976"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.cokernelEquivCut",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "94e5b144edd8ae25c84140a3611bea78fe7e62801233a522494d873468ea20e9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength:3554",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength:3554"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.cokernel_length_eq_cut",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fa83b47067c2f90c23f141f249e98790c90a71ac188c03e05e2270efe9dd81b8",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength:4090",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength:4090"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.colonQuotientEquivKernel",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6c9bb117a5611c213f6426bbb55bb9bc2b9e4190c9e099532002b930b379980d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength:2733",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength:2733"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.cutEuler",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LocalIntersectionEulerFiltration",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7d341b4946693c02352db2ac191bad68d2b1083cf4d9082dd702f5fe12533152",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LocalIntersectionEulerFiltration:315",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LocalIntersectionEulerFiltration:315"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.cutEuler_bot_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LocalIntersectionRegularEuler",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ab856c8b5984a7c0f72fd76f82467e658066bd3715b09136a3273e66bf2d3a3f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LocalIntersectionRegularEuler:1335",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LocalIntersectionRegularEuler:1335"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.cutEuler_cyclic_step",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LocalIntersectionEulerFiltration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "be393204772c1fbec3da0287818ea68ac02ce30ce57c34cb8354148296949cc5",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LocalIntersectionEulerFiltration:1099",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LocalIntersectionEulerFiltration:1099"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.cutEuler_filtration",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LocalIntersectionEulerFiltration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "af5aafb82d2aa9e8224629d5683162ac4c3b9e015c48cdcbfd9e4088d6105bca",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LocalIntersectionEulerFiltration:1781",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LocalIntersectionEulerFiltration:1781"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.cutEuler_prime_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LocalIntersectionRegularEuler",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aa3515e5790439d40d2d3ffc7b4883e40e44c6466d8ca6d0407ec1eb59b9f1cc",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LocalIntersectionRegularEuler:2095",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LocalIntersectionRegularEuler:2095"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.cutEuler_top",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LocalIntersectionEulerFiltration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0647263fb85d4ba1583ebaa4522e463d8adf4deaad0ec1d5807e07ee0252c093",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LocalIntersectionEulerFiltration:1660",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LocalIntersectionEulerFiltration:1660"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.cyclic_ideal_step_cross_add",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionExactStep",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "560d868ad50918696461f152cd10df2164a944281ca832544a94ec8d0315a106",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionExactStep:1384",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionExactStep:1384"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.dimension_one_prime_factor_dichotomy",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionDimensionOne",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0b484c29d8fb3f2c2061af6e80ec224cce954cc21d45441433cec4716e07ae68",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionDimensionOne:956",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionDimensionOne:956"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.exists_cyclic_filtration_all_local_counts",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionPrimeFiltration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6bd12f34adfd516a199f76e46264c41c836e4c8044a1772a3c20a370bb755f78",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionPrimeFiltration:2421",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionPrimeFiltration:2421"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.exists_cyclic_prime_filtration_nat",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionPrimeFiltration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "688681de19ddc55b0ba420f8d32ab52a8e610e38f08db55484bca3c0bcf162d9",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionPrimeFiltration:670",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionPrimeFiltration:670"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.exists_regular_onecut_sum_and_local_counts",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LocalIntersectionRegularEuler",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "263d5d89045e390b6fc18b0cc80467eb2a517ac53890f89d8daffb63ff679f58",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LocalIntersectionRegularEuler:2723",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LocalIntersectionRegularEuler:2723"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.finite_length_cut_eq_colon",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3423df5286f7ca5f4a0fb781e07c3f7c70bfde1551a20088ac800c121a16787c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength:4314",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength:4314"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.finite_length_kernel_eq_cokernel",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5f1f87285fcd1168d5b639a83772e94d8d40a2fe26e5ce2bf88a95d2fffb953a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength:327",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength:327"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.kernel_length_eq_colon",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2fb0ecce1e247cc2015b89982fe773aa9aa3cd9e3c12cac3e21d6a6b09e9e9f9",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength:3852",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength:3852"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.local_onecut_length",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionFormula",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0444d475e8b8c45dc88c7d06249c3bd1ad15c12fc61dc85979fa625dcef47749",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionFormula:1671",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionFormula:1671"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.map_scalar_kernel",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionTransport",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bff63e8985093dc5c1e180fc04a0e41ed3fffa2b04644c86a3a72a1bf1550799",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionTransport:293",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionTransport:293"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.map_scalar_range",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionTransport",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c4262f06eae5e1545e130ce2df41d12ed108be922c1e464952f0167e95379224",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionTransport:811",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionTransport:811"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.maximal_factor_cut_eq_colon",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionDimensionOne",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0d04c2bd7b910dcce7d79c2a63ffbaa0ab2d72b242c87c39f04f3f4ea164b8b8",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionDimensionOne:237",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionDimensionOne:237"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.minimalPrimeCutSum",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionPrimeFactors",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2712b38cc75abf02bd09f92864a20c69c073dbce889bad15b46e1b52bbb3a248",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionPrimeFactors:1241",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionPrimeFactors:1241"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.minimalPrimeCutSum_quotient",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionFormula",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8c987f5fdb1c4edc0d8db3db5c0a342248808d2f84bde39c093155dd5eb2fe59",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionFormula:239",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionFormula:239"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.prime_colon_length_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionPrimeFactors",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "577c2fddf784d93bca394c7d79f0572b7796026a8404421e2c6eec8e2b108e12",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionPrimeFactors:673",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionPrimeFactors:673"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.prime_quotientMul_injective",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionPrimeFactors",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d6d2f81e6905f657eb61bde48cf7d90b328742b1f17c91a34cafe5a7c94cbf0d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionPrimeFactors:295",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionPrimeFactors:295"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.quotientMinimalPrimesEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionQuotientTransport",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6d6e2af899ac864718513183ca1b544ce4d5c6d8503fa6b20f66b29e974206e5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionQuotientTransport:2645",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionQuotientTransport:2645"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.quotientMul",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "11c0f5d2ee74e4fba60c2ff063dfc3f4356591d511034f9e03c948534904a28f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength:1447",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength:1447"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.quotientMul_kernel",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b5c5250ec09cdf2654d47b1f23aefb627c1448307afc9cf83364506cb0015a3c",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength:1943",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength:1943"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.quotientMul_mk",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f76ac134d87cb139be125d17ee74e0effe119a6de3dd901672618806ac1cd8fa",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength:1660",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength:1660"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.quotientMul_range",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b1e6a1fc6a16ce2fba2d8c2259420d86fd122c1a38d35497689f821abc0a0c16",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength:3019",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength:3019"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.quotient_annihilator_eq_colon",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionPrimeFiltration",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bc5c7ad06a81da249dd8df290797aa981797a3d175ab0cc40f72c5e0c95db3e6",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionPrimeFiltration:290",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionPrimeFiltration:290"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.quotient_cut_length",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionQuotientTransport",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "af6e10efa59692a801ae26ef2251ea555121616ef391c212a4e6130a1e8a462b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionQuotientTransport:302",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionQuotientTransport:302"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.quotient_minimal_local_length",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionQuotientTransport",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0b53fd0632129cee9fd7de677037e6d04f247d7d697c7545605ffd59b813eb2d",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionQuotientTransport:3664",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionQuotientTransport:3664"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.quotient_parameter_mem_nonZeroDivisors",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionFormula",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "641e6a7e056d1b5a508b2a58f7c9c63f5245c4078d5fd5aee9513c48bcfd905a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionFormula:1287",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionFormula:1287"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.quotient_prime_cut_length",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionQuotientTransport",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c7d567ef34e37212da30956b2e6a2696d356eb02d1a3ebbe508d5aff71bca305",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionQuotientTransport:1515",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionQuotientTransport:1515"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.quotient_principal_cut_length",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionQuotientTransport",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fdbcca10ff22d73b8aba562eacdd83c748e852b5a81b72d7aae26c18f2d53195",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionQuotientTransport:1041",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionQuotientTransport:1041"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.regular_colon_bot",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LocalIntersectionRegularEuler",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "91e475c2c8490272b7f27d99231aa664640f4c2a7efb42573413fefa74a64fbb",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LocalIntersectionRegularEuler:1030",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LocalIntersectionRegularEuler:1030"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.regular_colon_length_ne_top",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LocalIntersectionRegularEuler",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ee2c4e2253c4e5f1a6eeeac9a1689861f2e6a1a2bcc0bc4a738f928926a1c90a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LocalIntersectionRegularEuler:718",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LocalIntersectionRegularEuler:718"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.regular_colon_length_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "33df0b4ef2fc614223bdd9918741623fda7559b8f24716525c2cfc563b1925d1",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength:4683",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength:4683"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.regular_cut_length_ne_top",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.LocalIntersectionRegularEuler",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "313081060556188924e68facf7dd183939806e2d13916e30943569cd34f2342e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.LocalIntersectionRegularEuler:423",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.LocalIntersectionRegularEuler:423"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.regular_not_mem_minimalPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionDimensionOne",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e1b582c3cb8857d709dcf451bb40aad9458e497fdcd7b6794ce0ca73afd4a6af",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionDimensionOne:703",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionDimensionOne:703"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.regular_ring_onecut_length",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionMinimalSum",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "34065bdcb53272cfd17d4b021bbdfaa55b6cf8b494a613109e0f2e6b72ce0576",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionMinimalSum:1192",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionMinimalSum:1192"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.scalarCokernelEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionTransport",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3332887139df84ece45f45f2de55b3129da7603072765dbf515c5ec36e848de3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionTransport:1588",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionTransport:1588"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.scalarKernelEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionTransport",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ba7ed4abbb13e4b4f70909d4ab559397cd268b8f6c67447c8a37b8fb11e773d8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionTransport:1342",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionTransport:1342"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.scalar_cokernel_length_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionTransport",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9608432b05a5447f67b9a44159db5b7900d66be9b50cd81dc925e4d63af1b612",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionTransport:2128",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionTransport:2128"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.scalar_euler_cross_add",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionExactStep",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3569d7e616fed8c7d814cae09edbdf78af85ae14f71961d0c792cf32fc5af510",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionExactStep:386",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionExactStep:386"
    },
    {
      sourceName := "OAI.PiExponentJets.W28.LocalIntersection.scalar_kernel_length_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionTransport",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4734c8793694d38fa70ec126aadedc28b6972ad77df603a7fd0a51fffced6d35",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionTransport:1867",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionTransport:1867"
    },
    {
      sourceName := "OAI.PiExponentJets.W29.affineDomain_maximal_height",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ClosedPointLocalDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d1e0a1dca07bde05f0cd4e0c1eac35303930c80119dd8e4da85cdc7f86aa8852",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ClosedPointLocalDimension:1275",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ClosedPointLocalDimension:1275"
    },
    {
      sourceName := "OAI.PiExponentJets.W29.boundedCoefficientMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FiniteNormalizationGrowth",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "90a256ff7e6b7894ab9a0b711695a7247175e30d0a27a671544071732b000ef1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FiniteNormalizationGrowth:521",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FiniteNormalizationGrowth:521"
    },
    {
      sourceName := "OAI.PiExponentJets.W29.closedPoint_local_dimension",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ClosedPointLocalDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "371e30d5fb9f0e322f35f900e0ffbd6e98e244d2f2dbfa08339f9db24fd6fbf7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ClosedPointLocalDimension:2302",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ClosedPointLocalDimension:2302"
    },
    {
      sourceName := "OAI.PiExponentJets.W29.finite_multiplication_matrices",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FiniteNormalizationGrowth",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "64721ca0678e0a3260f56937f770200b33abdfc83efa1293f1dc819062ec7845",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FiniteNormalizationGrowth:3810",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FiniteNormalizationGrowth:3810"
    },
    {
      sourceName := "OAI.PiExponentJets.W29.finite_normalization_upper_growth",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FiniteNormalizationGrowth",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1f438a7c8c25a3e0d5c59dbfa40cda745515ddf2506ccf32b664db214aa62804",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FiniteNormalizationGrowth:8844",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FiniteNormalizationGrowth:8844"
    },
    {
      sourceName := "OAI.PiExponentJets.W29.finrank_generatorPiece_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FiniteNormalizationGrowth",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "48cd52105fdfe9757c2269fc7301969ebe713ece2db7bd7e0f3bf028578c2716",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FiniteNormalizationGrowth:2091",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FiniteNormalizationGrowth:2091"
    },
    {
      sourceName := "OAI.PiExponentJets.W29.generatorPiece",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FiniteNormalizationGrowth",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "739694f9befb5ca59046ff3d16db51f2162866ad605938f2b8e96370336b6035",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FiniteNormalizationGrowth:858",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FiniteNormalizationGrowth:858"
    },
    {
      sourceName := "OAI.PiExponentJets.W29.generatorPiece_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FiniteNormalizationGrowth",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d7f0e3314c5d982530548e8d2d5ce386d729ee28b8118726b9e871ba7f80f98f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FiniteNormalizationGrowth:1884",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FiniteNormalizationGrowth:1884"
    },
    {
      sourceName := "OAI.PiExponentJets.W29.generatorPiece_mono",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FiniteNormalizationGrowth",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8968d94c3f683c944398e3743613d80db5fe4851eac71477074b210b802f781f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FiniteNormalizationGrowth:1567",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FiniteNormalizationGrowth:1567"
    },
    {
      sourceName := "OAI.PiExponentJets.W29.local_quotient_cut_dimension_one",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPrefixCutDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fee57a894a89fa5fc97a37a7ce81b2c9b2cbed36733d10683fd4152cb15b28c5",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPrefixCutDimension:388",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPrefixCutDimension:388"
    },
    {
      sourceName := "OAI.PiExponentJets.W29.mem_generatorPiece",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FiniteNormalizationGrowth",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c7c3490ba632e05afdc12112e6401e5b7fc7e8e079613a62983d2b1a79edde41",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FiniteNormalizationGrowth:1031",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FiniteNormalizationGrowth:1031"
    },
    {
      sourceName := "OAI.PiExponentJets.W29.monomial_mem_generatorPiece",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FiniteNormalizationGrowth",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "990ae915a660ff29bcbf5dd7ff470cbcb6ec64b83db9c76744914364210fcf39",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FiniteNormalizationGrowth:6667",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FiniteNormalizationGrowth:6667"
    },
    {
      sourceName := "OAI.PiExponentJets.W29.mul_mem_generatorPiece",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FiniteNormalizationGrowth",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cc007de3586ed485463c4fea0472ffe2fa1829419defb862e543f30a4ccedad7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FiniteNormalizationGrowth:2613",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FiniteNormalizationGrowth:2613"
    },
    {
      sourceName := "OAI.PiExponentJets.W29.polynomial_mem_generatorPiece",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FiniteNormalizationGrowth",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ea8f84a54015d74ed20e33914a0590db26d0e625d0aad104f0a5377373e02745",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FiniteNormalizationGrowth:7972",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FiniteNormalizationGrowth:7972"
    },
    {
      sourceName := "OAI.PiExponentJets.W29.regularPrefix_local_cut_dimension_one",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPrefixCutDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b7d5759d376bb073a282b1ddffa957912d96aaf85e0e5a9341e34fbadcce8ef6",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPrefixCutDimension:2860",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPrefixCutDimension:2860"
    },
    {
      sourceName := "OAI.PiExponentJets.W29.under_height_le_of_goingDown",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ClosedPointLocalDimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "be171321d9824cc928de36153942bdb5cf978403c97f507da71450baeeb44134",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ClosedPointLocalDimension:479",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ClosedPointLocalDimension:479"
    },
    {
      sourceName := "OAI.PiExponentJets.W29.variable_pow_mem_generatorPiece",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.FiniteNormalizationGrowth",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2260378de41c124e54d7b86d85111fb161abd19ee746e9c6cdf991a4a5bb65b5",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.FiniteNormalizationGrowth:5933",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.FiniteNormalizationGrowth:5933"
    },
    {
      sourceName := "OAI.PiExponentJets.W32.card_exponentBall",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ac0d41c40123497246463b131dc190dcfb0d001ec90e95646ee3f39e15b81324",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks:893",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks:893"
    },
    {
      sourceName := "OAI.PiExponentJets.W32.exponentBall",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7227875163cf13259f90809a8b5e33a24059c0bd9e4f5667d368b198b5a3018b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks:346",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks:346"
    },
    {
      sourceName := "OAI.PiExponentJets.W32.finrank_restrictTotalDegree",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f996fe8ae98b9bb880135a975a2eeef8cc2281b9099980465d8efd1faa250e0d",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks:1553",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks:1553"
    },
    {
      sourceName := "OAI.PiExponentJets.W32.mem_exponentBall",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "012dad2f6854b5d5aeb65309eb211c61300914f0f5c03831bf4284f77e3787c2",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks:501",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks:501"
    },
    {
      sourceName := "OAI.PiExponentJets.W32.polynomialGrowth",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c26f0e251d10ee5e7e81d22741c72a0dd08e6bd68c5bffbd483f53e43e3bfab9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks:2389",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks:2389"
    },
    {
      sourceName := "OAI.PiExponentJets.W32.polynomialGrowth_eval",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e63afb62eaaf875af47f0af260556989c69bd0629be61b45747a13d5eee04ea9",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks:2494",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks:2494"
    },
    {
      sourceName := "OAI.PiExponentJets.W32.polynomialGrowth_eval_finrank",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f6f4900409bcf41e0ceeb51a959253163b6a543390ad5d3a697d53742b95534a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks:2745",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks:2745"
    },
    {
      sourceName := "OAI.PiExponentJets.W32.polynomialGrowth_leadingCoeff",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "31d8ecc473d7c28a391b74cab96021010d42e8266552efc944dbffb0a032e2d4",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks:3157",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks:3157"
    },
    {
      sourceName := "OAI.PiExponentJets.W32.polynomialGrowth_leadingCoeff_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "83549d70c1cf240da92bb34ff973838fc69493433fa8d7fdefe76290823d2702",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks:3329",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks:3329"
    },
    {
      sourceName := "OAI.PiExponentJets.W32.polynomialGrowth_natDegree",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d760d3c56919aa9298cfcb4f565221345a1948d765c3a8044e88095fad0ecf6e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks:3009",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks:3009"
    },
    {
      sourceName := "OAI.PiExponentJets.W32.scaledPolynomialGrowth",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ca8faa03ccd942a85265f853827933c297bae392646d11faf2e9623984bfd407",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks:3904",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks:3904"
    },
    {
      sourceName := "OAI.PiExponentJets.W32.scaledPolynomialGrowth_eval_finrank",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0044d66e56fab96fb914f67f5cfe052b1addd14baba6aabbc48276c802d68aee",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks:4229",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks:4229"
    },
    {
      sourceName := "OAI.PiExponentJets.W32.scaledPolynomialGrowth_natDegree_le",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "03c995916eff4ab9a2b28673076d495d4948abf8ce3f014c7356eb23dd6ae6cc",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks:4027",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks:4027"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.card_exponents_degree",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HilbertPolynomialBase",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "271c27790bc9fe945636ad71849bf6e92414ab31c9c6a879abb7242324ec1ad0",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HilbertPolynomialBase:957",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HilbertPolynomialBase:957"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.coeff_rationalSectionHilbertSeries",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PositiveDimensionalHilbert",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4c7bb2a13c94d36b51fdced618ae0620ed39197c4181c33ca865abc2e3f2f3d9",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PositiveDimensionalHilbert:2718",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PositiveDimensionalHilbert:2718"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.coeff_sectionHilbertSeries",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.HilbertSeries",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "08d059ba3dc37d51a4025f837c6a4a24c2c8a4f4e6d4183d12b125bb8c3269ca",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.HilbertSeries:472",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.HilbertSeries:472"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.colonHilbertNumerator",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertDenominatorReduction",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7393f794ae750a9d9843e552ebf3bf16d269c5ce8eacd8720f2614f65a83306b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertDenominatorReduction:247",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertDenominatorReduction:247"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.colon_hilbert_polynomial_eventually",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.ColonHilbertPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8f4b0114abfce746dadac7ceb43864ec0bbef8ec91916aad248437b66c42eca8",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.ColonHilbertPolynomial:2649",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.ColonHilbertPolynomial:2649"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.colon_hilbert_step",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ColonHilbertStep",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "de7432b065261a04d8880522799fe1cc0ecf704d6d3493ad8f779caf833a427d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ColonHilbertStep:2378",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ColonHilbertStep:2378"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.degreeAt",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.RegularSequenceSeries",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2408b9f4a02729adaf98835be8a9da18558557fd499b66dcb98ff3c3ce2a8c53",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.RegularSequenceSeries:355",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.RegularSequenceSeries:355"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.degreePolynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CompleteIntersectionHilbert",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bac9688eea9614b857f43519401be428cbc07b2dc2dc7cb63c9a0a3d3ce34b32",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CompleteIntersectionHilbert:201",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CompleteIntersectionHilbert:201"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.degreePolynomial_coe",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PositiveDimensionalHilbert",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e283045d927b6dad62d37e073a5735a95f8103989e5e1d1df3ba19b22a459eea",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PositiveDimensionalHilbert:995",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PositiveDimensionalHilbert:995"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.degreePolynomial_eval_one",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.CompleteIntersectionHilbert",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7d7e46d50790484f569e17dca6a36f0d3b33206f4b94ad339003b2ff7a02513d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.CompleteIntersectionHilbert:382",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.CompleteIntersectionHilbert:382"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.degree_factors_mul_invOneSubPow",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.RegularSequenceSeries",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "db1d0e1aaf9d261eb345b714b0f4953b38f8eb0f1e4b987ba952eac3343cd576",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.RegularSequenceSeries:1790",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.RegularSequenceSeries:1790"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.exists_hilbert_numerator_no_variables",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertZeroVariables",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "544edca931b39f71436474b248dcd8d9db0dbff0831fbaf66e08c903281ef382",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertZeroVariables:1064",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertZeroVariables:1064"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.exists_homogeneous_hilbert_numerator",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousHilbertExistence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5ff904b1c7c4cf214329c973e823aa609a4ec40e717a0abcff1af7e1666a88bb",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousHilbertExistence:1583",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousHilbertExistence:1583"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.exists_homogeneous_hilbert_polynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousHilbertPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "de90954f92e80ad51343339dfbe95bcc440579cc954c7a12639b742986cc295d",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousHilbertPolynomial:830",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousHilbertPolynomial:830"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.exponentDegreeEquivSym",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HilbertPolynomialBase",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "425f8ec0fa509227bc4ae1b77dc2277d5b41958811c8305f9a8e82557681ba7e",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HilbertPolynomialBase:283",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HilbertPolynomialBase:283"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.hilbertMultiplicity",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PositiveDimensionalHilbert",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aaa4ea2a6e147c673de666d2ff332ef2de767341ba336df8467d94c377cbf63f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PositiveDimensionalHilbert:7365",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PositiveDimensionalHilbert:7365"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.hilbertPolynomial_degree_and_leading",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PositiveDimensionalHilbert",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9e0fc04e7c2e0090b2147cdbfced6b4aefa5b6b5dd1245479e5f89ff129d6408",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PositiveDimensionalHilbert:6618",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PositiveDimensionalHilbert:6618"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.hilbertPolynomial_natDegree_le",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PositiveDimensionalHilbert",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "56b26d8468bdbce79e4b4c5017f2cf9151aebdacdea09c1b447fc4ebaa78f3f6",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PositiveDimensionalHilbert:6170",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PositiveDimensionalHilbert:6170"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.hilbertPolynomial_top_coefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PositiveDimensionalHilbert",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cdacb8a7270312be9a6f005d31a4c885999aabb2572331af3f412cf78b9323e6",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PositiveDimensionalHilbert:5644",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PositiveDimensionalHilbert:5644"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.hilbert_step_of_degree_lt",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularHilbertStep",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "007e5303f9331547bbb79941e77316237862903e3d3ad3bab2a24fd781af7dd5",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularHilbertStep:3998",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularHilbertStep:3998"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.homogeneousSection_finite",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d533b36ffb5829d5c3414ff255c6051ad7b68c263260e4913974f1fc16909a7c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSections:569",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSections:569"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.homogeneousSection_finrank",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a7cd3c81d3e72756ef4d4ee6fdefcee35499b3b1e63172194d89a23ba08692e3",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSections:1005",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSections:1005"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.homogeneous_mem_step_decomposition",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousIdealStep",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "24d2d71ccbbf21f38d373bbf67acbd17cc2c3f8275a5e7b9cdba8f95ba38417e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousIdealStep:308",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousIdealStep:308"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.homogeneous_mem_step_of_degree_lt",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousIdealStep",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "06b932c85c17ba8a819695656d8921054b941b1aaeb3b72ee609547bc4123074",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousIdealStep:1615",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousIdealStep:1615"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.ideal_le_colon_singleton",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ColonHilbertStep",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "090f01cfc3494a21e5f9bcaf92dd6b7cd350fbd6fb53acb2ff32e1adcca32cf6",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ColonHilbertStep:339",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ColonHilbertStep:339"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.iteratedColon",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.ColonSeriesTelescope",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3d7404609f2505458ef5c81453497e8ff948f9f18defea24b1b19fc65d649228",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.ColonSeriesTelescope:424",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.ColonSeriesTelescope:424"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.iteratedColon_eq_colon_power",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousHilbertExistence",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8a2ef325e9645462686059cfa2249cceda56273033f624cae89a926571c7d480",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousHilbertExistence:483",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.HomogeneousHilbertExistence:483"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.iteratedColon_homogeneous",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.ColonSeriesTelescope",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "70f1ba1a8126b705813d8795910eaffd8dd68a96ec7f851b63642c680b1dcdf7",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.ColonSeriesTelescope:920",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.ColonSeriesTelescope:920"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.iteratedColon_series_telescope",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.ColonSeriesTelescope",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e27e23d655bde05e823a1c649aaba5735e74a532fbb167dec352ad6175609fe8",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.ColonSeriesTelescope:1367",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.ColonSeriesTelescope:1367"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.iteratedColon_succ",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.ColonSeriesTelescope",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2cc90b825ca2b1ea80779f98f1313421e40c2bf7fc3588890c39cd87fde60688",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.ColonSeriesTelescope:744",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.ColonSeriesTelescope:744"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.map_int_invOneSubPow",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.PositiveDimensionalHilbert",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "bedd5c5d7148e4e98e3f8dbf5384ae15e2b179b6b5820d92b12423f382942cdc",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.PositiveDimensionalHilbert:3435",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.PositiveDimensionalHilbert:3435"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.prime_hypersurface_actual_hilbert_degree",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProperHypersurfaceHilbert",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "eeddc29ef511e7bda42642b3018a6e761d5134d0e696feadd7d51ab2163d91f1",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProperHypersurfaceHilbert:1833",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProperHypersurfaceHilbert:1833"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.prime_quotient_right_regular",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.ProperHypersurfaceHilbert",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "50d60b12657f65239fa299989adfab3210ce7d981f98d24839d943bfc43767c7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.ProperHypersurfaceHilbert:299",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.ProperHypersurfaceHilbert:299"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.quotientSection",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientSections",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c0877d7d7e43f449d7ead5fb0a4f46bd229ce3fdee38fba7da2d9e06dc35af7d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientSections:258",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientSections:258"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.quotientSectionCokernel_finrank_add",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientSections",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cc8f70312c5b0dcc1c3a4244de42a4489892be8e1e5e54cddd120dcfcecc6d3f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientSections:1707",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientSections:1707"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.quotientSectionFactor",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularHilbertStep",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8f1fd09c1ee557734975cf61a2f5284e2abcf191861172bd3e378a26c2c9dc5f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularHilbertStep:257",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularHilbertStep:257"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.quotientSectionFactor_colon_ker",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ColonHilbertStep",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b56c8ba7c3a6ab68bf6428756765a88d28b398880eea6d8265e4e85cfb246ba8",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ColonHilbertStep:595",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ColonHilbertStep:595"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.quotientSectionFactor_ker_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularHilbertStep",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f8bb1d1ac76b7488d8bb415b3ac7985948d1b4b2be9828c67572e72732b3843f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularHilbertStep:1192",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularHilbertStep:1192"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.quotientSectionFactor_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularHilbertStep",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "94ed857b5f804a599f8fee4943e5293f2330223e7c48943b260cd471b15d3e93",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularHilbertStep:828",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularHilbertStep:828"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/complete-source/SharedSourceSnapshot_033.jsonl"
