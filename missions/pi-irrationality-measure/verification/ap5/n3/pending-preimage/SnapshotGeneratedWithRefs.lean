import Lean
import Theorems.Thm_OAI_PiExponent_exists_successive_approximations
import Theorems.Thm_OAI_PiExponent_exists_normalized_selection_of_selector

theorem solution
    (nu X D : ℝ) (hnu : 0 < nu)
    (hbad : ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
      Q ≤ q ∧ |Real.pi - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu)) :
    ∃ p : ℕ → ℤ, ∃ q : ℕ → ℕ, ∃ x : ℕ → ℝ,
      x 0 = 1 ∧
      (∀ n, x (n + 1) = (Nat.ceil (Real.log (q n)) : ℝ)) ∧
      (∀ n, 2 ≤ q n ∧ p n ≠ 0 ∧
        |Real.pi - (p n : ℝ) / q n| ≤ (q n : ℝ) ^ (-nu) ∧
        1 ≤ Nat.ceil (Real.log (q n)) ∧ X < x (n + 1)) ∧
      (∀ i, 1 ≤ x i) ∧
      (∀ i, 0 < i → D * (∏ j ∈ Finset.range i, x j) < x i) := by
  exact OAI.PiExponent.exists_normalized_selection_of_selector nu X D
    (OAI.PiExponent.exists_successive_approximations nu hnu hbad)

open Lean Meta

namespace PiExponentInterfaceSnapshot

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

-- Keep binder information, constant names, universe levels and de Bruijn
-- indices. Binder display names and source metadata have no kernel meaning.
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

def exportSnapshot (names : Array Name) (output : String) : MetaM Unit := do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for name in names do
    let some ci := env.find? name | throwError "Missing interface declaration: {name}"
    if ci.type.hasMVar || ci.type.hasFVar then
      throwError "The exported declaration type is not closed: {name}"
    let value := match ci with
      | .defnInfo d => some d.value
      | .thmInfo _ => none
      | _ => none
    let typeText ← ppExpr ci.type
    rows := rows.push <| Json.mkObj [
      ("name", toJson name.toString),
      ("levelParams", toJson (ci.levelParams.map Name.toString)),
      ("type", exprJson ci.type),
      ("value", value.map exprJson |>.getD Json.null),
      ("prettyType", toJson typeText.pretty)]
  IO.FS.writeFile output (Json.arr rows |>.compress)

end PiExponentInterfaceSnapshot

set_option pp.universes true
set_option pp.fullNames true
set_option pp.explicit true
run_meta do
  PiExponentInterfaceSnapshot.exportSnapshot #[`solution] "missions/pi-irrationality-measure/verification/ap5/n3/generated-type.json"
#print axioms solution


namespace FormalLogProofReferenceSnapshot

open Lean Meta

def refs (value : Expr) : Array String :=
  (value.getUsedConstants.map Name.toString).qsort (fun a b => a < b)

def exportProofRefs (requests : Array Name) (output : String) : MetaM Unit := do
  let env ← getEnv
  let mut seen : Array Name := #[]
  let mut rows : Array Json := #[]
  for name in requests do
    if seen.contains name then
      throwError "Duplicate proof-reference request: {name}"
    seen := seen.push name
    unless (env.getModuleIdxFor? name).isNone do
      throwError "Proof-reference request was inherited instead of declared here: {name}"
    let some ci := env.find? name | throwError "Missing proof-reference request: {name}"
    let value ← match ci with
      | .thmInfo theoremInfo => pure theoremInfo.value
      | _ => throwError "Proof-reference request is not a theorem: {name}"
    if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars then
      throwError "Proof-reference theorem type is not closed: {name}"
    if value.hasMVar || value.hasFVar || value.hasLooseBVars then
      throwError "Proof-reference theorem value is not closed: {name}"
    let axioms ← collectAxioms name
    unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
      throwError "Proof-reference theorem has nonstandard axioms: {name}"
    rows := rows.push <| Json.mkObj [
      ("name", toJson name.toString), ("userName", toJson name.toString),
      ("kind", toJson "theorem"),
      ("levelParams", toJson (ci.levelParams.map Name.toString)),
      ("closedType", toJson true), ("closedValue", toJson true),
      ("typeRefs", toJson (refs ci.type)), ("valueRefs", toJson (refs value)),
      ("axioms", toJson (axioms.map Name.toString)),
      ("owner", Json.mkObj [("kind", toJson "OwnModule"),
        ("module", toJson env.mainModule.toString)])]
  IO.FS.writeFile output <| (Json.mkObj [
    ("schemaVersion", toJson 1), ("probeMainModule", toJson env.mainModule.toString),
    ("rows", Json.arr rows)]).pretty

end FormalLogProofReferenceSnapshot

open Lean Meta in
run_meta do
  FormalLogProofReferenceSnapshot.exportProofRefs #[`solution] "missions/pi-irrationality-measure/verification/ap5/n3/proof-references.json"
