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
      sourceName := "OAI.PiExponent.CurveStalkGluing.isDominant_fromSpecFunctionField",
      expectedModule := "OAI.NumberTheory.PiExponent.Geometry.CurveStalkGluing",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0231c5c20017beb0ed61b0375bc5a051b5c3fdbe376d5cfd2b563033a2ab9d1b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Geometry.CurveStalkGluing:714",
      commandUnit := "OAI.NumberTheory.PiExponent.Geometry.CurveStalkGluing:714"
    },
    {
      sourceName := "OAI.PiExponent.DerivativeIdeals.derivativeCore",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1b54af6773e21ea739d03d1c672eaf3be47e48a13b68f36bffe2ce4ee327a69b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:2280",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:2280"
    },
    {
      sourceName := "OAI.PiExponent.DerivativeIdeals.derivativeIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0f498135f40e28c319f397b3a322c6a2dca0ed51618fc1343c23e637ac7f7e4a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:1290",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:1290"
    },
    {
      sourceName := "OAI.PiExponent.DerivativeIdeals.self_mem_derivativeIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8b72b5e537151719ff7b881c79c605929d9c1217cf133f51ed09a2b8ec668c3e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:2057",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:2057"
    },
    {
      sourceName := "OAI.PiExponent.DerivativeIdeals.wordCost",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dc4355c9d45cdf02187fd4bd7b042cd5d3eb94ac29e27dcafcaab0a13d8621b7",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:743",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:743"
    },
    {
      sourceName := "OAI.PiExponent.DerivativeIdeals.wordDerivative",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1140a3db04690e9d57c37850c3d7719286b78d0d31e94f5c72a1bfe75b6d8bfb",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:328",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:328"
    },
    {
      sourceName := "OAI.PiExponent.DerivativeIdeals.word_mem_derivativeIdeal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e4c6de23311f25934ec772a851afef78376bcde06056f9d46aaf13f0282ca8d0",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:1491",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals:1491"
    },
    {
      sourceName := "OAI.PiExponent.GradedLocalizationExact.degreePiece",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a54578ff0ab0d19c621acd35323cb5cfa82f2f0d7812309e9538777cba79fc3c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:2871",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:2871"
    },
    {
      sourceName := "OAI.PiExponent.GradedLocalizationExact.fraction",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1c87890a204b3afd977205b2ab8be54c59304c00d44d96bd6bdc4095abf51849",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:972",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:972"
    },
    {
      sourceName := "OAI.PiExponent.GradedLocalizationExact.fraction_add",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "691b36136f71ac7be7c3ccaa841e247715a9c4448afc1088843f2c328d5b531f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:1342",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:1342"
    },
    {
      sourceName := "OAI.PiExponent.GradedLocalizationExact.fraction_cancel",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b16ad0f130cce54138ea87efe5d4cb860e203304fda5f001fcdd2f1b4d854046",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:1620",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:1620"
    },
    {
      sourceName := "OAI.PiExponent.GradedLocalizationExact.fraction_eq_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c0561d93d158c5bb45fd84c53fcfdea9e6791e33672aba0908b6e48c154e2e0e",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:1930",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:1930"
    },
    {
      sourceName := "OAI.PiExponent.GradedLocalizationExact.fraction_neg",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "68d39e482ad1af38056654b59fef938cb388414c4e0114514996471a9bf69ef0",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:1215",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:1215"
    },
    {
      sourceName := "OAI.PiExponent.GradedLocalizationExact.fraction_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a2c711541849b7ec7560f1ae9ee5607b8495b2e1cadd3a60e74d7a3f606763e2",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:1105",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:1105"
    },
    {
      sourceName := "OAI.PiExponent.GradedLocalizationExact.homogeneous_preimage",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "42fcb10eb4563b2dd980a2fd8e3b437d776c25a0327febec7c15249072256ca7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:5532",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:5532"
    },
    {
      sourceName := "OAI.PiExponent.GradedLocalizationExact.localizedMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b68a7f3ca999331e50dfac88fc1c8da68823ded075d3cbf5b23aac7f041e6e32",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:3872",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:3872"
    },
    {
      sourceName := "OAI.PiExponent.GradedLocalizationExact.localizedMap_fraction",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4cc54ea8f9b7c0ab2de68a42716d825614cd40deb5d87c3f7e983ed526910d90",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:4131",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:4131"
    },
    {
      sourceName := "OAI.PiExponent.GradedLocalizationExact.pieceMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7badd76a902d54ea4eb2221d0222ebf92ce294edf959d5968836728af9d6626f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:4389",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:4389"
    },
    {
      sourceName := "OAI.PiExponent.GradedLocalizationExact.pieceMap_exact",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "413ffb6dc95c27521bf127df71ca4af6dee7c115c10541d165c5bb7c8d0385ed",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:6712",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:6712"
    },
    {
      sourceName := "OAI.PiExponent.GradedLocalizationExact.pieceMap_surjective",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fa5059970225ff45296405f944062d74e6bf5d7420e05cec84116a6a5075eb92",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:5995",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:5995"
    },
    {
      sourceName := "OAI.PiExponent.GradedLocalizationExact.powerDenominator",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2cf016b70e320088e230e6340f68ffb81e0d6c03b84a1e37c6a1e5c24007ef0d",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:458",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:458"
    },
    {
      sourceName := "OAI.PiExponent.GradedLocalizationExact.powerDenominator_add",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b11da4ff7156778f2b5da57e601fd1d3d7e7f77a3319d296c1e852f9e0eb48bb",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:790",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:790"
    },
    {
      sourceName := "OAI.PiExponent.GradedLocalizationExact.powerDenominator_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "413593ee3cc1ee67489fd73ab91aa25fcd8399e9e8036b643aaac958eff28b0b",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:660",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:660"
    },
    {
      sourceName := "OAI.PiExponent.GradedLocalizationExact.power_smul_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2b5da4e0f3678eb22435353cf29bab6f35badf5af174698f9880d50285846d74",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:2560",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:2560"
    },
    {
      sourceName := "OAI.PiExponent.GradedLocalizationExact.preserves_of_compatible",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fb7dc3e85b8ed2c021bc3f8bff0807eafe71b5b6bd010b3d740474cddfe7086d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:5164",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact:5164"
    },
    {
      sourceName := "OAI.PiExponent.LogTailAnalytic.hasSum_coeff_mul",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "03b3601ddc266711f4b020b29c1bdcb3039c0af40f2806aa8cf4cabd63ec57d9",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:6271",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:6271"
    },
    {
      sourceName := "OAI.PiExponent.LogTailAnalytic.hasSum_coeff_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "112f56ddb1b972c2202eb26a1b8c5396b76ca1cc2d3222e95f2f312f1958aa2b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:7074",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:7074"
    },
    {
      sourceName := "OAI.PiExponent.LogTailAnalytic.hasSum_coeff_pow",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b1660f134fe8bfdc68454b8ee1a00a5ebdd82cb8c40d2a78106bc589a423783c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:7313",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:7313"
    },
    {
      sourceName := "OAI.PiExponent.LogTailAnalytic.hasSum_formal_log",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aefa8b264882edc6b595418a42ddaee5306ed90ead76a29ade3dd581c473b1a9",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:4162",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:4162"
    },
    {
      sourceName := "OAI.PiExponent.LogTailAnalytic.logTail",
      expectedModule := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "057f36ca0c65568aaf9357a7f5fc3a412fdad1b00fdb2d7e6ddcca6f3a348e97",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:267",
      commandUnit := "OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic:267"
    },
    {
      sourceName := "OAI.PiExponent.NefAmple.combination_denominator_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Ampleness.NefAmple",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "42f02c64fb504c3960b3b510d639957fefbd5bca6621b1776d9b6051d82d98c0",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Ampleness.NefAmple:2466",
      commandUnit := "OAI.NumberTheory.PiExponent.Ampleness.NefAmple:2466"
    },
    {
      sourceName := "OAI.PiExponent.NormalBasisRigidity.IsNormalBasis",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e90fb3d2fe058ee243dbff7d003979d594988cb6513dfd8412fcf0fc13ca9626",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity:237",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity:237"
    },
    {
      sourceName := "OAI.PiExponent.NormalBasisRigidity.IsNormalBasis.card_eq",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "aadd7fddf94f88fda8025be814e769b1b533686edc5d913ecde127f44439a116",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity:2736",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity:2736"
    },
    {
      sourceName := "OAI.PiExponent.NormalBasisRigidity.exists_normalBasis_containing",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0e105247a8b314f5448f995a95d7d1fc1b61835b21731d97b573c385ac3c52e1",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity:975",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity:975"
    },
    {
      sourceName := "OAI.PiExponent.NormalBasisRigidity.frameBasis",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ae6007467e5f1880f254283240c98619a69e3550e22dc843961116db9d795fa1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis:1087",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis:1087"
    },
    {
      sourceName := "OAI.PiExponent.NormalBasisRigidity.frameBasis_succ",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "924a783a85344951874dcd36c8c37c7b4619a2d618b5aacb04eaa0f96e8fca27",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis:1658",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis:1658"
    },
    {
      sourceName := "OAI.PiExponent.NormalBasisRigidity.frameEquiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "27ec45cec336e96266aa786509fe9d597d64389b0c1f218edd708bf69b6e6483",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis:278",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis:278"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedSlopePolynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.MixedSlopePolynomial",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "721d83c7fcdb5aa642fd26566f3bd1b891fa7f793b908a9ecc41d1041235bbad",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.MixedSlopePolynomial:160",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.MixedSlopePolynomial:160"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedSlopePolynomial_eval",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.MixedSlopePolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "364816aa033332c688a0b7f7f9e43f8aeb4fc455196ae36843d69dad4f2f9b40",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.MixedSlopePolynomial:297",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.MixedSlopePolynomial:297"
    },
    {
      sourceName := "OAI.PiExponent.NumericalAmpleness.mixedSlopePolynomial_eval_div",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.MixedSlopePolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "03cf330938e3b2254a36f6c8ea5a2fb1b9fa649dca31a6712894f26680c17c12",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.MixedSlopePolynomial:1909",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.MixedSlopePolynomial:1909"
    },
    {
      sourceName := "OAI.PiExponent.Parameters",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "inductive",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1959ebb3f2aea65f610a6dccebb1d76370724d77f59615a8613f6fde38207407",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.A",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a4b59a8b4862dd1436e6b185c6ad40d37c8a10bf6b7128048cbdff8c4ba8d1c5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.A_lt_B",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "104640a061689cc71fe999651e3c55424ecf9a4e77ecd24cc21c0769b0f4970c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.A_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e48c067080464a6cdb88ca55f08a0eb904b2d7cc9fe26638ff1062af38950cb6",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:5380",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:5380"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.B",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ce4bf30b3ed54f9be5151c2a8405547f6049288790361cbc1dcbf2fca8ece291",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.B_lt_C_theta",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "8321e192bb45c64f18380c423651fdaf474e0ebcc1e0d827e539199d8c59592f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.B_lt_inv_C",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "93c64801fdd7a5307b83f52be8c091143d8da52d2d5b9011a879767655e555c1",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.B_lt_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "692e10f8930e2164c2799f0e0b4727a1fee6feb0770a8ec33e6bf53ca834a61f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.C",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "78f8bfd96546f52acaa6ecc5403daacbd937489beb030bcd3667d170ea4230c9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.C_theta_lt_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9c1e892f80d53d1583368c914bd05959fba4da7100a7c59b921c4ed990099270",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.approximation_gap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fd561b73e671cc3c7dec530c3242cbcd45a158917a9a2427bfb700951d1a8206",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.casesOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "414e266917c5ab0795344618c5171503fbe89f8fd4de3f4c795e862355a05d13",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.eta",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "91809a058c30f17b25f47973836bfcb627bbf45aa2b5d7a58df2b495bc848f0a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.eta_lt_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "083f67995d6b489dd477f85539829ae0f909e017b7b2ae98d79c97d17bc86a1b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.eta_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b7ad4122c2a230b73caa0b6389cc6104fb061ab5dfefa3e9b39bc3605a8f3628",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.gap_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "df664f2d63b6b8c38fc17236e4ce5feafffd4c8434f85135c3d44d2f63d9c3e3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.mk",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "ctor",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "96d047fab06b0c5b26def512360adacb9bb5b285bede888273d0adac5e69b4c8",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.mk.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5117ffeec9d4cc0dc67cba1eee378f06f6fd17e0dd45e3de66fac5f2bedb08eb",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.noConfusion",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ca392e756dc60c8923068c5514391b33470b162a7fa98ddc6dfc600189b73e01",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.one_lt_C",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "08c66cfec231332f79f5b9beafcd9b4ea3c7a3cae7659f61081d63a749aa054b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.rec",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "rec",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2bc2f50c6fc2cd9b3b010eb22618c5ccda2dbeb9f070da768579876195eebb37",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.recOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "55b2878abd89a225fa453669d093e9984dc054e329e650f35e579ed91ebc1c53",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.theta",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "31398ad0ca6bea5cd9f9a5281e73a6e514e34bfa9d100ab9b0137324edb592a5",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.theta_lt_A",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d4abb8c9fb3d254317e4b080b65a01f32f13042a1beccbbb9bc66c8dbe48cac3",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.Parameters.theta_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.Parameters",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "72465333cd1627e9ed4b04f240468bea82c752fa5eef9be02d37292c22a7a2bf",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.Parameters:4283"
    },
    {
      sourceName := "OAI.PiExponent.PersistentComponents.exists_adjacent_eq_of_height_bound",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "36ab207c923d7ec79be1aa566ec5a24a243e0a162a2c79ce1bec3347364a0800",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents:364",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents:364"
    },
    {
      sourceName := "OAI.PiExponent.PersistentComponents.exists_nested_minimalPrimes",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6f3d89e1953589b1c1bdb3decf57ce78a2a19952cfc2cdebe4094a93b3166149",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents:1413",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents:1413"
    },
    {
      sourceName := "OAI.PiExponent.PersistentComponents.exists_persistent_component_positive_height",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f18c8118e202c97dae787dc954a5616d387e136f69580f1ade4580b7f0bd5479",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents:6156",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents:6156"
    },
    {
      sourceName := "OAI.PiExponent.PersistentComponents.exists_persistent_minimalPrime",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2f18453054cdbbcacec2baee74a07599b79706574b778e22e85e7a5033bbef28",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents:2699",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents:2699"
    },
    {
      sourceName := "OAI.PiExponent.PersistentComponents.exists_persistent_minimalPrime_pair",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a268f0a321a1527023b077ac695d901d1f42f8999906b707d3eb92c7af15e7e7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents:4132",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents:4132"
    },
    {
      sourceName := "OAI.PiExponent.PersistentComponents.minimalPrime_height_pos_of_nonzero_mem",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "57d6dd1129655e8674c47e24e1f1283230333a4c5af07da30a7576b3fc32a940",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents:5761",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents:5761"
    },
    {
      sourceName := "OAI.PiExponent.PersistentComponents.minimalPrime_persists",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cceec43a6e2138e599c6a4ee9e92b1f46b07e437765a1887507f7b955794115d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents:3880",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents:3880"
    },
    {
      sourceName := "OAI.PiExponent.PersistentComponents.prime_height_step",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0c8857de4ddb46cebd8838b4296ac0feb39e6df4216f5128346531b6011aa4cb",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents:152",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.PersistentComponents:152"
    },
    {
      sourceName := "OAI.PiExponent.PolynomialNormal",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c6face3013130ed41f98d63d69e2ae16ec376b9fe79bf0311457fc2e253f4a4a",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential:1534",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential:1534"
    },
    {
      sourceName := "OAI.PiExponent.PolynomialPoleBound.monomial_order_lower",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPoleBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ed8c36bbbd3ec1aa79a9933a7f72172274af0bd0536ec7738adfb9b2adcff70e",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPoleBound:942",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPoleBound:942"
    },
    {
      sourceName := "OAI.PiExponent.PolynomialPoleBound.polynomial_order_lower",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPoleBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e4fd68dfb2fe6c88431d9d21276923aec7e812f3febad6ef3ce9fe71b465bd8d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPoleBound:2255",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPoleBound:2255"
    },
    {
      sourceName := "OAI.PiExponent.PolynomialPoleBound.realValuation",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPoleBound",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "57c2f673f59c9ff0ea983933561f985f97de727282da3f17465cf132202b1ec2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPoleBound:299",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPoleBound:299"
    },
    {
      sourceName := "OAI.PiExponent.PolynomialPoleBound.realValuation_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPoleBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d5d2900734eb6c9c4ef7e6cdab89450aa64ac4fea8bd441eb862ae7949277824",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPoleBound:515",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPoleBound:515"
    },
    {
      sourceName := "OAI.PiExponent.PolynomialPoleBound.valuation_prod",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPoleBound",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "cc64eed0959e158c494055ba4bc062116089927f0f61c8c17e41866a33448d8f",
      ownerKind := "definition_embedded",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPoleBound:676",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialPoleBound:676"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialCech.Laurent",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0de044fccc58ffeb55b5e0f9266c6d6d5ed988ca2b4dc9238bec61bf38141acd",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCech:441",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCech:441"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialCech.Monomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e5d353d3b8f6673e792cc603a2b199721132d56d3a05dfa6f4044379e8eed648",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCech:348",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCech:348"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialCech.RegularOn",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCech",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "286af8200827bb7a83ad9e250fcf742db117ddf1edab4fa081b5d74cce1c4022",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCech:535",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCech:535"
    },
    {
      sourceName := "OAI.PiExponent.ProjectiveMonomialCech.exists_nonnegative_coordinate",
      expectedModule := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCech",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a288776525a1a5ae8df7d663d9d60c6c7864afc11671df70636bdfb1345a7126",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCech:3065",
      commandUnit := "OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCech:3065"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.RowChoices",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "98def1acefd799e100d4889e9d9f1fa635991d2726dd3f4bfa52ea6ce4936bfb",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:10668",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:10668"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.multiIndex",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b3aac1c3795f11100810fae4a6d0bfd4e6c7efc3cbbe706511f311ab771405c9",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:2296",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:2296"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.multiIndex_apply",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c820b4360b0e8d00e40d8222918477c6530194930ff925a074714056d161c597",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:2396",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:2396"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.rowScalar",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "25e6fd5a6123637169e5cbf6ce748019c0a0e5bae583742016ef7ce609548f84",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:7272",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:7272"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.shift",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f7078d28ae849daef40dc4a03ab4592117179dd459496aa8eeb2dbd42b4cd106",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:222",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:222"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.shiftCoefficient",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c3966b6cd9032c86c56f70ab19acc6bf3d3c0c8a08f1a44f609b7caccc3bb5f2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:1019",
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
      sourceName := "OAI.PiExponent.RowTranslation.shift_monomial_one",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ba2d43d79652ded0c7412096358354b21e5f5f5506923adb7859913aebd19793",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:3500",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:3500"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.shifted_X_pow",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "96caa63129aa32a4292905db84200c2e679999cad15955051dfe14c684955b4a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:2534",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:2534"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.shifted_product_expansion",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "67570c22c7b300f23abea8f4bbe57becc5c3f7b67f02f63d86589ab4e62225d6",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:2894",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:2894"
    },
    {
      sourceName := "OAI.PiExponent.RowTranslation.tail",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "864a826c6d1078095926e1c88bdca809500d27fb0702b18adfd18fc633157061",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:12851",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RowTranslation:12851"
    },
    {
      sourceName := "OAI.PiExponent.WeightedSliceDegree.SupportBound",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6214bed6f843cacdf9117a847141081453666ff41e11a73761f369e71917cb1b",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:218",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:218"
    },
    {
      sourceName := "OAI.PiExponent.WeightedSliceDegree.SupportBound.add",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "12264e03d7a97585309f8454bb60de1cb4ad76d12a210377c9990606fb7d4fd7",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:1211",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:1211"
    },
    {
      sourceName := "OAI.PiExponent.WeightedSliceDegree.SupportBound.mono",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "83ad989a532e2f03f34123bee9ba926ddf25d97fd7d3d0d4f2be1c3851c341d2",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:350",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:350"
    },
    {
      sourceName := "OAI.PiExponent.WeightedSliceDegree.SupportBound.mul",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9eb83a1842149e2279d017be1fe850b96d1e554ae1e029c8ff5507429d752251",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:1522",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:1522"
    },
    {
      sourceName := "OAI.PiExponent.WeightedSliceDegree.SupportBound.pow",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fac29544e4ccdb74d1a3d9c6894026eae8f50cb74258f5ee5a735ae2e007c951",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:1882",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:1882"
    },
    {
      sourceName := "OAI.PiExponent.WeightedSliceDegree.enumeratedSliceMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3ff12dc9ca0b977a5200e3434b009b70e1710b00d2893d88c4da20528dd94220",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:7687",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:7687"
    },
    {
      sourceName := "OAI.PiExponent.WeightedSliceDegree.sliceMap",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f7c34deff4197e19a4dc504251cb8c7e18198281c161a8c1c2c13726e5dc91d2",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:4618",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:4618"
    },
    {
      sourceName := "OAI.PiExponent.WeightedSliceDegree.supportBound_C",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "fa34c21af3357b4f45ec908a088d1f69bfa72532546a75ec3fbda4e4cd622bd9",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:681",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:681"
    },
    {
      sourceName := "OAI.PiExponent.WeightedSliceDegree.supportBound_X",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2699342205e057af34d3335b2de8e35a9af01d1632b928dfe0c7928f60d2445c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:904",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:904"
    },
    {
      sourceName := "OAI.PiExponent.WeightedSliceDegree.supportBound_aeval",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "c69ecfcabf3011e35eec8d7aa451b14971d4f7c23938c0a689fab48ef4e3f6f6",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:4123",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:4123"
    },
    {
      sourceName := "OAI.PiExponent.WeightedSliceDegree.supportBound_aeval_monomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "116b2949783f6e85b7835c933588a5557eecfeaff570ed29ca9bb4af1653be1a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:3416",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:3416"
    },
    {
      sourceName := "OAI.PiExponent.WeightedSliceDegree.supportBound_prod",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a3c68dfda46fad9a86de3ae9a672a4aff8c5573ae3f72c5bc9b691b82c1b1f5f",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:2289",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:2289"
    },
    {
      sourceName := "OAI.PiExponent.WeightedSliceDegree.supportBound_sum",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "815c4bfeb3cac70ded83f97a7f73516f4ea665ef70ff5559305bfffe9aeb0159",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:2902",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:2902"
    },
    {
      sourceName := "OAI.PiExponent.WeightedSliceDegree.supportBound_zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "dc441061a873843e7f236da8a53a943be85bb5945bc66072859af8a02aebf90c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:541",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree:541"
    },
    {
      sourceName := "OAI.PiExponent.card_unweightedSimplex",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7512611b07e6fe56eb9839dcf211cce5ccab3676a47790ddbc0e29c05ba8177a",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted:751",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted:751"
    },
    {
      sourceName := "OAI.PiExponent.derivation_mem_polynomialTangent",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3df31054008d3653128f2e05bbb56978f734a54faf362b8307d68c1443ada607",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential:1676",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential:1676"
    },
    {
      sourceName := "OAI.PiExponent.derivation_polynomial_map",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "39505a239f3b34cbd8d8be8d1f817d3cebe6d106f114649c2210cb3362459f6a",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential:477",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential:477"
    },
    {
      sourceName := "OAI.PiExponent.differential_eq_zero_of_polynomialTangent",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "956f2ef324b824206e440cecff6932b059c143f2c1321dcc03da855a2d9b4e6e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential:3414",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential:3414"
    },
    {
      sourceName := "OAI.PiExponent.dimensionK",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f3045b67fedd17de5cd0ff4b327d1ee153229e76dd52c9aae93545eb0da21145",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:338",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:338"
    },
    {
      sourceName := "OAI.PiExponent.dimensionK_le",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "ff9c8385d6295513aa8d89002112afe6d73ce04c110a0659e309ff086817c1a5",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:574",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:574"
    },
    {
      sourceName := "OAI.PiExponent.dimensionV",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "80bfe228db13db7ba55f64588ebdbe776aa94e9632cc48e093bee9d988109a45",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:460",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:460"
    },
    {
      sourceName := "OAI.PiExponent.dimensionW",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "177680d0c0bed82b9a91b92f44da3ef4cf2d6bcae1f6cade40b10918b8fc6b99",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:400",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension:400"
    },
    {
      sourceName := "OAI.PiExponent.mem_unweightedSimplex",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f7ba98b1b9326590a091f40cfbb36e0b9173df80973b96c35decac1b5aa471b8",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted:327",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted:327"
    },
    {
      sourceName := "OAI.PiExponent.polynomialJacobian",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b7dfd1fff6ceddacc7d3c4aac67ca24ad042d6b36ec99432f278884d04b84b9f",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential:1043",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential:1043"
    },
    {
      sourceName := "OAI.PiExponent.polynomialTangent",
      expectedModule := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5a3db68c0ffadb71289c26bf0f6e532350794100aa8b18769b52d1be6fd730fc",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential:1364",
      commandUnit := "OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential:1364"
    },
    {
      sourceName := "OAI.PiExponent.rectangularCutoff",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "680fa678c00673d3b7023b5a008f7469e98cc0e142888445440d6ce7b4012226",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume:122",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume:122"
    },
    {
      sourceName := "OAI.PiExponent.rectangularCutoff_coordinate_weight_lt",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "da49c7d4f0c2b5fd74bf12778a528ee8700997ede9d93756e6e8657cbd8affbc",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume:1537",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume:1537"
    },
    {
      sourceName := "OAI.PiExponent.rectangularCutoff_pos",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "e9e022d9d07453da9b8d7b41ff0eb626e5c7406377b6699200f88860b399a6fe",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume:258",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume:258"
    },
    {
      sourceName := "OAI.PiExponent.rectangularCutoff_product_lower",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "07b0058ab20a268d4cc5f6df2974435e2bb88ca0494caae8ac7121b49fbf958e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume:2927",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume:2927"
    },
    {
      sourceName := "OAI.PiExponent.rectangularCutoff_weight_lt",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "5323b915bbf957691b4b43cd0d09437043213775faac40d1f109be9827b3d6a2",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume:2104",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume:2104"
    },
    {
      sourceName := "OAI.PiExponent.tendsto_card_unweightedSimplex",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "17367159d1d669fdcb3048f40adc9a3c33be399837c0dd543c17787fcdb6ea89",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted:3702",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted:3702"
    },
    {
      sourceName := "OAI.PiExponent.tendsto_card_unweightedSimplex_add",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9d0d7cae99aac1178dbcce1f818f7d9cf238d7e183f7f3d70ac51e58cd8c1bb0",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted:3970",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted:3970"
    },
    {
      sourceName := "OAI.PiExponent.tendsto_choose_add_normalized",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f3154e730a3708ea4887f24837dff71fb9b443a979db28c15dfaa5f549aec9d5",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted:2924",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted:2924"
    },
    {
      sourceName := "OAI.PiExponent.tendsto_choose_normalized",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "2bc3f7569452caa6d03f6293b22fedece8d6b13903a9e0ab03a5dcbee8eae397",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted:2321",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted:2321"
    },
    {
      sourceName := "OAI.PiExponent.tendsto_natFloor_affine_atTop",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexFloor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "6a115ed6ba4a6ab3667260e0cf20d104ec5ce7cb428826aca63459718f295837",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexFloor:115",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexFloor:115"
    },
    {
      sourceName := "OAI.PiExponent.tendsto_natFloor_affine_div",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexFloor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a645952e449e46d2e1bf4b93d68de9a0d9e8329301bb6a5661f89dffd85f99c6",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexFloor:372",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexFloor:372"
    },
    {
      sourceName := "OAI.PiExponent.tendsto_normalized_natFloor_affine",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexFloor",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1aa63b34e5cfa5765689216c94242e1cfddd918e86a7b33f18cdd6e602ac375c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexFloor:1383",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexFloor:1383"
    },
    {
      sourceName := "OAI.PiExponent.two_le_rectangularCutoff",
      expectedModule := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "d716a86b4d00c902f5045bc2dc0c266f25a18f8bb615c4980d2212733655416b",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume:559",
      commandUnit := "OAI.NumberTheory.PiExponent.Approximation.RectangularVolume:559"
    },
    {
      sourceName := "OAI.PiExponent.unweightedSimplex",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "038ab30ff7c2537f5dbb153ad137d4922b0bcdd3e92eaaa581ef2a4303a968ab",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted:168",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.SimplexUnweighted:168"
    },
    {
      sourceName := "OAI.PiExponentApprox.HasWeightedDegreeLE",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3362a18e5d51e6ddf686b09a93ebf6931988c7b35cf5775efb34c0c353216e69",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:303",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:303"
    },
    {
      sourceName := "OAI.PiExponentApprox.HasWeightedDegreeLE.X_mul",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4204ba343dc70a89f4bfb3c10568072d290ddf9f0c32afc73f86dd892c488add",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:3146",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:3146"
    },
    {
      sourceName := "OAI.PiExponentApprox.HasWeightedDegreeLE.X_mul_pderiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "0907538fcbfd918f839157c57d341ae39ab4be378a0eeddc24c6d261a7b3bf61",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:3692",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:3692"
    },
    {
      sourceName := "OAI.PiExponentApprox.HasWeightedDegreeLE.add",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "103a2bf3155dcd580208d6f8962ac658498056e4d926e0e44b486f3638eeeba4",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:1386",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:1386"
    },
    {
      sourceName := "OAI.PiExponentApprox.HasWeightedDegreeLE.mono",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "de87bff23abf78a87b11fbb58436e33bc87dbd45727852243952e3a9850d4148",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:1140",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:1140"
    },
    {
      sourceName := "OAI.PiExponentApprox.HasWeightedDegreeLE.pderiv",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "a7971ed83d60f91a0e034a3b00b4b1daab8a39e227e550671b335f8f5b243b1e",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:2712",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:2712"
    },
    {
      sourceName := "OAI.PiExponentApprox.HasWeightedDegreeLE.pderiv_preserves",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "95981be8a7715db650464fe1909f6e24d79667e6758da0588ff24e8a4864678c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:4016",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:4016"
    },
    {
      sourceName := "OAI.PiExponentApprox.HasWeightedDegreeLE.sum",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7db2c2a0cc1ed1d981bfcf01cbcfe4e1f3469e9d89a939a79a0885a6667e34a3",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:1754",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:1754"
    },
    {
      sourceName := "OAI.PiExponentApprox.HasWeightedDegreeLE.zero",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "29295d8889b92748852be70073e15298451c39c042e52c92d5b32208fedbd9f3",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:954",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:954"
    },
    {
      sourceName := "OAI.PiExponentApprox.monomialWeight",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "01f36c75bdf6fe96787cba2023e52f0479a6f634b366d2f13e44d10c1c7da5cc",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:174",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:174"
    },
    {
      sourceName := "OAI.PiExponentApprox.monomialWeight_add",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4a01e6720c14b43b01d7176658132d60e089d1954571468873d509489497fd31",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:477",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:477"
    },
    {
      sourceName := "OAI.PiExponentApprox.monomialWeight_single",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "1e5c9f37295eaf2563b9544691aa44de00848fce4eb55c16c75372555547aabc",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:750",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:750"
    },
    {
      sourceName := "OAI.PiExponentApprox.pderiv_support_shift",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "53db4743b7904a9d344f0b152696647c811da2f0649a09b2f8107edef92f198c",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:2313",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree:2313"
    },
    {
      sourceName := "OAI.PiExponentJets.W06.isArtinianRing_quotient_parameter",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterKilledFiniteLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "705f8a0cfb48cc7b06f74a1d66620cf4a20a65efe6b60526ba628d0195dac586",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterKilledFiniteLength:275",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterKilledFiniteLength:275"
    },
    {
      sourceName := "OAI.PiExponentJets.W06.isFiniteLength_coker_parameter_mul",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterKilledFiniteLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "3e1a91f482a7077cca609525d56e65ee939656100aeef62c93ec3d8845b57e16",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterKilledFiniteLength:3144",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterKilledFiniteLength:3144"
    },
    {
      sourceName := "OAI.PiExponentJets.W06.isFiniteLength_of_parameter_killed",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterKilledFiniteLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "688e7b4f4fe414b0190995f1b3cafbc8d605c094b2763f9e88fcaa4443f55e25",
      ownerKind := "node",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterKilledFiniteLength:727",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterKilledFiniteLength:727"
    },
    {
      sourceName := "OAI.PiExponentJets.W06.parameter_kills_mul_cokernel",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterKilledFiniteLength",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "54ab237977ca194536cb755b82221ccfcca85174123bbedfb0eb22b35b8096a3",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterKilledFiniteLength:2332",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterKilledFiniteLength:2332"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.dehomogenize",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.Homogenization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4083b7b17726a48055ae60d6f6cee6011783a59d38d1dc4cd7df2d78b279d27c",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.Homogenization:228",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.Homogenization:228"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.dehomogenize_X_none",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.Homogenization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "7bd24cbc6666decaf5363d4440d60de95e1dc85c9cb350e54dc28f9731f58ed8",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.Homogenization:407",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.Homogenization:407"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.dehomogenize_homogenize",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.Homogenization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "20070dbb39555aa61eec8591ac5d6fecea2702001979f48df1e64b230feaf0b4",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.Homogenization:1204",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.Homogenization:1204"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.dehomogenize_rename",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.Homogenization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "90c542014c0c55f7d4c43237a25a0746d55da970b1c0deabfab07cd6f98d75b8",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.Homogenization:550",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.Homogenization:550"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.homogenize",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.Homogenization",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "f7cd58eee6cc97f20f8c239b6558a17ec54a47a85fe66062a3b3b581f0570871",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.Homogenization:948",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.Homogenization:948"
    },
    {
      sourceName := "OAI.PiExponentJets.W22.homogenize_isHomogeneous",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.Homogenization",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "23cc83d4e264fd6e2145953b156b1bc9baa165fe455e7af3e087148fbd709c34",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.Homogenization:1483",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.Homogenization:1483"
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
      sourceName := "OAI.PiExponentJets.W64.shiftHilbertPolynomial",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.ColonHilbertPolynomial",
      graphKind := "def",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "9395458646bd3beeb9aaaadeaf1529b4937fe0f55ebe67eb35d65860a7546f35",
      ownerKind := "definition",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.ColonHilbertPolynomial:297",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.ColonHilbertPolynomial:297"
    },
    {
      sourceName := "OAI.PiExponentJets.W64.shiftHilbertPolynomial_eval",
      expectedModule := "OAI.NumberTheory.PiExponent.Polynomials.ColonHilbertPolynomial",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "4a445174f246f74e7180ad6e334c257b800924d58c83e18c99db92b98d9ca6eb",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.Polynomials.ColonHilbertPolynomial:442",
      commandUnit := "OAI.NumberTheory.PiExponent.Polynomials.ColonHilbertPolynomial:442"
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
      sourceName := "OAI.PiExponentSiegel.W20.regular_sequence_term_not_isUnit",
      expectedModule := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularDegreePositivity",
      graphKind := "theorem",
      declGraphSha256 := "dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4",
      declGraphRowSha256 := "b1d445f57b91306519db90f71597465992c186ec46884d9a77c36124cbbc906d",
      ownerKind := "inline",
      ownerId := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularDegreePositivity:596",
      commandUnit := "OAI.NumberTheory.PiExponent.LocalAlgebra.RegularDegreePositivity:596"
    }
  ]

run_meta do
  exportSourceSnapshotJsonl sharedSourceRequests "missions/pi-irrationality-measure/verification/shared-source-snapshot/provider-subset/ProviderSourceSubset_000.jsonl"
