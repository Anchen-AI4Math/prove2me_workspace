import Theorems.Thm_ZetaNine_CoefficientMapNumeratorPF_global
import Lean
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
noncomputable section
open scoped BigOperators
open Finset Polynomial ZetaNine
open ZetaNine.CoefficientMapJet ZetaNine.CoefficientMapInjectivity
open ZetaNine.CoefficientMapPartialFractions
open ZetaNine.CoefficientMapFormalTransportData
open ZetaNine.CoefficientMapNumeratorPartialFractions
open Lean Meta
private def requireStd3 (name : Name) : MetaM (Array Name) := do
  let axioms ← Lean.collectAxioms name
  unless axioms.toList.all (fun n => ([`propext, `Classical.choice, `Quot.sound] : List Name).contains n) do
    throwError "Nonstandard axiom in actual declaration: {name}"
  return axioms
private def requireClosed (name : Name) (ty : Expr) (value : Expr) : MetaM Unit := do
  unless !(ty.hasFVar || ty.hasMVar || value.hasFVar || value.hasMVar) do
    throwError "Actual declaration has unclosed type or value: {name}"
private def emitDefinition (name : Name) : MetaM Unit := do
  let .defnInfo info ← getConstInfo name | throwError "Expected actual definition {name}"
  requireClosed name info.type info.value
  let axioms ← requireStd3 name
  IO.println (Json.mkObj [("kind",Json.str "independent_full_definition"),
    ("declaration",Json.str name.toString),("closed",toJson true),
    ("level_parameters",toJson (info.levelParams.map Name.toString)),
    ("full_type_raw_Expr",Json.str (reprStr info.type)),
    ("full_value_raw_Expr",Json.str (reprStr info.value)),
    ("axioms",toJson (axioms.toList.map Name.toString))]).compress
private def emitProof (name : Name) (kind : String) : MetaM Unit := do
  let .thmInfo info ← getConstInfo name | throwError "Expected actual theorem {name}"
  requireClosed name info.type info.value
  let axioms ← requireStd3 name
  IO.println (Json.mkObj [("kind",Json.str kind),("declaration",Json.str name.toString),
    ("closed",toJson true),("full_type_raw_Expr",Json.str (reprStr info.type)),
    ("axioms",toJson (axioms.toList.map Name.toString))]).compress
private def compareWhole (name expected : Name) : MetaM Unit := do
  let .defnInfo actualInfo ← getConstInfo name | throwError "Expected actual definition"
  let .defnInfo expectedInfo ← getConstInfo expected | throwError "Expected independently written definition"
  let typeKernel ← isDefEq actualInfo.type expectedInfo.type
  let valueKernel ← isDefEq actualInfo.value expectedInfo.value
  let typeRaw := Expr.equal actualInfo.type expectedInfo.type
  let valueRaw := Expr.equal actualInfo.value expectedInfo.value
  unless typeKernel && valueKernel && typeRaw && valueRaw do
    throwError "Full-function Expr/kernel mismatch: {name}"
  IO.println (Json.mkObj [("kind",Json.str "independent_whole_definition_comparison"),
    ("declaration",Json.str name.toString),("expected",Json.str expected.toString),
    ("type_kernel_equal",toJson typeKernel),("value_kernel_equal",toJson valueKernel),
    ("type_Expr_equal",toJson typeRaw),("value_Expr_equal",toJson valueRaw),
    ("actual_full_type_raw_Expr",Json.str (reprStr actualInfo.type)),
    ("expected_full_type_raw_Expr",Json.str (reprStr expectedInfo.type)),
    ("actual_full_value_raw_Expr",Json.str (reprStr actualInfo.value)),
    ("expected_full_value_raw_Expr",Json.str (reprStr expectedInfo.value))]).compress
private def compareType (name expected : Name) : MetaM Unit := do
  let actualInfo ← getConstInfo name
  let expectedInfo ← getConstInfo expected
  let same ← isDefEq actualInfo.type expectedInfo.type
  unless same do throwError "Whole forall type mismatch: {name}"
  IO.println (Json.mkObj [("kind",Json.str "independent_complete_forall_kernel_comparison"),
    ("declaration",Json.str name.toString),("expected",Json.str expected.toString),
    ("whole_type_kernel_equal",toJson same),
    ("actual_full_type_raw_Expr",Json.str (reprStr actualInfo.type)),
    ("expected_full_type_raw_Expr",Json.str (reprStr expectedInfo.type))]).compress
private def compareDefinitionSnapshot (name : Name) (nativeType nativeValue : Expr) : MetaM Unit := do
  let .defnInfo actualInfo ← getConstInfo name | throwError "Expected actual definition"
  let typeKernel ← isDefEq actualInfo.type nativeType
  let valueKernel ← isDefEq actualInfo.value nativeValue
  let typeRaw := Expr.equal actualInfo.type nativeType
  let valueRaw := Expr.equal actualInfo.value nativeValue
  unless typeKernel && valueKernel && typeRaw && valueRaw do
    throwError "Fresh native/staged full definition mismatch: {name}"
  IO.println (Json.mkObj [("kind",Json.str "independent_native_staged_definition_snapshot"),
    ("declaration",Json.str name.toString),("type_kernel_equal",toJson typeKernel),
    ("value_kernel_equal",toJson valueKernel),("type_Expr_equal",toJson typeRaw),
    ("value_Expr_equal",toJson valueRaw),
    ("native_full_type_raw_Expr",Json.str (reprStr nativeType)),
    ("native_full_value_raw_Expr",Json.str (reprStr nativeValue))]).compress
private def compareProofSnapshot (name : Name) (nativeType : Expr) : MetaM Unit := do
  let actualInfo ← getConstInfo name
  let same ← isDefEq actualInfo.type nativeType
  let raw := Expr.equal actualInfo.type nativeType
  unless same && raw do throwError "Fresh native/staged whole proof type mismatch: {name}"
  IO.println (Json.mkObj [("kind",Json.str "independent_native_staged_proof_snapshot"),
    ("declaration",Json.str name.toString),("whole_type_kernel_equal",toJson same),("whole_type_Expr_equal",toJson raw),
    ("native_full_type_raw_Expr",Json.str (reprStr nativeType)),
    ("actual_full_type_raw_Expr",Json.str (reprStr actualInfo.type))]).compress
private def emitInternalHelpers (modules : List Name) : MetaM Unit := do
  let env ← getEnv
  let mut found : List Name := []
  for (name, info) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let some moduleName := env.header.moduleNames[index.toNat]? | continue
    if modules.contains moduleName && (name.isInternal || (privateToUserName? name).isSome) then
      found := name :: found
      if ← isProp info.type then
        let proofValue ← match info with
          | .thmInfo actual => pure actual.value
          | .defnInfo actual => pure actual.value
          | .opaqueInfo actual => pure actual.value
          | _ => throwError "Unexpected proof helper kind: {name}"
        requireClosed name info.type proofValue
        let axioms ← requireStd3 name
        IO.println (Json.mkObj [("kind",Json.str "independent_internal_helper_proof"),
          ("declaration",Json.str name.toString),("closed",toJson true),
          ("full_type_raw_Expr",Json.str (reprStr info.type)),
          ("axioms",toJson (axioms.toList.map Name.toString))]).compress
      else if let .defnInfo _ := info then
        emitDefinition name
      else
        let axioms ← requireStd3 name
        IO.println (Json.mkObj [("kind",Json.str "independent_internal_helper_other"),
          ("declaration",Json.str name.toString),("full_type_raw_Expr",Json.str (reprStr info.type)),
          ("axioms",toJson (axioms.toList.map Name.toString))]).compress
  IO.println (Json.mkObj [("kind",Json.str "independent_actual_internal_helper_inventory"),
    ("modules",toJson (modules.map Name.toString)),("names",toJson (found.map Name.toString))]).compress

run_meta do
  compareProofSnapshot `ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_global_partial_fractions (Lean.Expr.forallE (Lean.Name.mkStr Lean.Name.anonymous "m") (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Nat") []) (Lean.Expr.forallE (Lean.Name.mkStr Lean.Name.anonymous "A") (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Polynomial") [Lean.Level.zero]) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Rat") [])) (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Rat") "semiring") [])) (Lean.Expr.forallE (Lean.Name.mkStr Lean.Name.anonymous "hproper") (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "LT") "lt") [Lean.Level.zero]) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Nat") [])) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "instLTNat") [])) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Polynomial") "natDegree") [Lean.Level.zero]) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Rat") [])) (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Rat") "semiring") [])) (Lean.Expr.bvar 0))) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "HMul") "hMul") [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero]) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Nat") [])) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Nat") [])) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Nat") [])) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "instHMul") [Lean.Level.zero]) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Nat") [])) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "instMulNat") []))) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "OfNat") "ofNat") [Lean.Level.zero]) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Nat") [])) (Lean.Expr.lit (Lean.Literal.natVal 9))) (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "instOfNatNat") []) (Lean.Expr.lit (Lean.Literal.natVal 9))))) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "HAdd") "hAdd") [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero]) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Nat") [])) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Nat") [])) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Nat") [])) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "instHAdd") [Lean.Level.zero]) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Nat") [])) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "instAddNat") []))) (Lean.Expr.bvar 1)) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "OfNat") "ofNat") [Lean.Level.zero]) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Nat") [])) (Lean.Expr.lit (Lean.Literal.natVal 1))) (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "instOfNatNat") []) (Lean.Expr.lit (Lean.Literal.natVal 1))))))) (Lean.Expr.forallE (Lean.Name.mkStr Lean.Name.anonymous "t") (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Rat") []) (Lean.Expr.forallE (Lean.Name.mkStr Lean.Name.anonymous "hregular") (Lean.Expr.forallE (Lean.Name.mkStr Lean.Name.anonymous "k") (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Nat") []) (Lean.Expr.forallE (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "a") "_@") "_internal") "_hyg") 0) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "LE") "le") [Lean.Level.zero]) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Nat") [])) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "instLENat") [])) (Lean.Expr.bvar 0)) (Lean.Expr.bvar 4)) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Ne") [(Lean.Level.succ Lean.Level.zero)]) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Rat") [])) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "HAdd") "hAdd") [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero]) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Rat") [])) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Rat") [])) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Rat") [])) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "instHAdd") [Lean.Level.zero]) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Rat") [])) (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Rat") "instAdd") []))) (Lean.Expr.bvar 2)) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Nat") "cast") [Lean.Level.zero]) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Rat") [])) (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Rat") "instNatCast") [])) (Lean.Expr.bvar 1)))) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "OfNat") "ofNat") [Lean.Level.zero]) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Rat") [])) (Lean.Expr.lit (Lean.Literal.natVal 0))) (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Rat") "instOfNat") []) (Lean.Expr.lit (Lean.Literal.natVal 0))))) Lean.BinderInfo.default) Lean.BinderInfo.default) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Eq") [(Lean.Level.succ Lean.Level.zero)]) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Rat") [])) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "HDiv") "hDiv") [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero]) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Rat") [])) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Rat") [])) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Rat") [])) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "instHDiv") [Lean.Level.zero]) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Rat") [])) (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Rat") "instDiv") []))) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Polynomial") "eval") [Lean.Level.zero]) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Rat") [])) (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Rat") "semiring") [])) (Lean.Expr.bvar 1)) (Lean.Expr.bvar 3))) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "HPow") "hPow") [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero]) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Rat") [])) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Nat") [])) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Rat") [])) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "instHPow") [Lean.Level.zero, Lean.Level.zero]) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Rat") [])) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Nat") [])) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "NPow") "toPow") [Lean.Level.zero]) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Rat") [])) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Monoid") "toNPow") [Lean.Level.zero]) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Rat") [])) (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Rat") "monoid") []))))) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Polynomial") "eval") [Lean.Level.zero]) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Rat") [])) (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Rat") "semiring") [])) (Lean.Expr.bvar 1)) (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "ZetaNine") "CoefficientMapInjectivity") "polePolynomial") []) (Lean.Expr.bvar 4)))) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "OfNat") "ofNat") [Lean.Level.zero]) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Nat") [])) (Lean.Expr.lit (Lean.Literal.natVal 9))) (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "instOfNatNat") []) (Lean.Expr.lit (Lean.Literal.natVal 9))))))) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Finset") "sum") [Lean.Level.zero, Lean.Level.zero]) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Nat") [])) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Rat") [])) (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Rat") "addCommMonoid") [])) (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Finset") "range") []) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "HAdd") "hAdd") [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero]) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Nat") [])) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Nat") [])) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Nat") [])) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "instHAdd") [Lean.Level.zero]) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Nat") [])) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "instAddNat") []))) (Lean.Expr.bvar 4)) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "OfNat") "ofNat") [Lean.Level.zero]) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Nat") [])) (Lean.Expr.lit (Lean.Literal.natVal 1))) (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "instOfNatNat") []) (Lean.Expr.lit (Lean.Literal.natVal 1))))))) (Lean.Expr.lam (Lean.Name.mkStr Lean.Name.anonymous "j") (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Nat") []) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Finset") "sum") [Lean.Level.zero, Lean.Level.zero]) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Nat") [])) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Rat") [])) (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Rat") "addCommMonoid") [])) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Finset") "Icc") [Lean.Level.zero]) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Nat") [])) (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Nat") "instPreorder") [])) (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Nat") "instLocallyFiniteOrder") [])) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "OfNat") "ofNat") [Lean.Level.zero]) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Nat") [])) (Lean.Expr.lit (Lean.Literal.natVal 1))) (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "instOfNatNat") []) (Lean.Expr.lit (Lean.Literal.natVal 1))))) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "OfNat") "ofNat") [Lean.Level.zero]) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Nat") [])) (Lean.Expr.lit (Lean.Literal.natVal 9))) (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "instOfNatNat") []) (Lean.Expr.lit (Lean.Literal.natVal 9)))))) (Lean.Expr.lam (Lean.Name.mkStr Lean.Name.anonymous "s") (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Nat") []) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "HDiv") "hDiv") [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero]) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Rat") [])) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Rat") [])) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Rat") [])) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "instHDiv") [Lean.Level.zero]) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Rat") [])) (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Rat") "instDiv") []))) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "ZetaNine") "CoefficientMapFormalTransportData") "numeratorLocalCoefficient") []) (Lean.Expr.bvar 6)) (Lean.Expr.bvar 1)) (Lean.Expr.bvar 0)) (Lean.Expr.bvar 5))) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "HPow") "hPow") [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero]) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Rat") [])) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Nat") [])) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Rat") [])) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "instHPow") [Lean.Level.zero, Lean.Level.zero]) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Rat") [])) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Nat") [])) (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Rat") "instPowNat") []))) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "HAdd") "hAdd") [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero]) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Rat") [])) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Rat") [])) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Rat") [])) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "instHAdd") [Lean.Level.zero]) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Rat") [])) (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Rat") "instAdd") []))) (Lean.Expr.bvar 3)) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Nat") "cast") [Lean.Level.zero]) (Lean.Expr.const (Lean.Name.mkStr Lean.Name.anonymous "Rat") [])) (Lean.Expr.const (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Rat") "instNatCast") [])) (Lean.Expr.bvar 1)))) (Lean.Expr.bvar 0))) Lean.BinderInfo.default)) Lean.BinderInfo.default))) Lean.BinderInfo.default) Lean.BinderInfo.default) Lean.BinderInfo.default) Lean.BinderInfo.default) Lean.BinderInfo.default)
  let .thmInfo info ← getConstInfo `ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_global_partial_fractions | throwError "Reference must be theorem"
  requireClosed `ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_global_partial_fractions info.type info.value
  let axioms ← Lean.collectAxioms `ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_global_partial_fractions
  unless axioms.contains `sorryAx && axioms.toList.all (fun n => ([`propext, `Classical.choice, `Quot.sound, `sorryAx] : List Name).contains n) do
    throwError "Reference stub axiom boundary differs"
  IO.println (Json.mkObj [("kind",Json.str "independent_reference_stub_only"),("declaration",Json.str "ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_global_partial_fractions"),
    ("full_type_raw_Expr",Json.str (reprStr info.type)),("closed",toJson true),
    ("axioms",toJson (axioms.toList.map Name.toString)),("excluded_from_proof_PASS",toJson true)]).compress
  let env ← getEnv
  unless !(env.header.moduleNames.toList.any (fun n => n.toString.startsWith "Solutions." || n.toString.startsWith "missions.zeta9.formalization.")) do
    throwError "Reference environment loaded native/solution proof module"
