import Lean
import Theorems.Thm_OAI_PiExponent_exists_successive_approximations
import Theorems.Thm_OAI_PiExponent_exists_normalized_selection_of_selector

theorem OAI.PiExponent.exists_normalized_successive_approximations
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

#print axioms OAI.PiExponent.exists_normalized_successive_approximations


open Lean Meta
namespace C4Snapshot
partial def levelJson : Level -> Json
  | .zero => Json.arr #[toJson "zero"]
  | .succ u => Json.arr #[toJson "succ", levelJson u]
  | .max u v => Json.arr #[toJson "max", levelJson u, levelJson v]
  | .imax u v => Json.arr #[toJson "imax", levelJson u, levelJson v]
  | .param n => Json.arr #[toJson "param", toJson n.toString]
  | .mvar n => Json.arr #[toJson "mvar", toJson n.name.toString]
def binderTag : BinderInfo -> String
  | .default => "explicit" | .implicit => "implicit"
  | .strictImplicit => "strictImplicit" | .instImplicit => "instance"
partial def exprJson : Expr -> Json
  | .bvar i => Json.arr #[toJson "bvar", toJson i]
  | .fvar n => Json.arr #[toJson "fvar", toJson n.name.toString]
  | .mvar n => Json.arr #[toJson "mvar", toJson n.name.toString]
  | .sort u => Json.arr #[toJson "sort", levelJson u]
  | .const n us => Json.arr #[toJson "const", toJson n.toString, Json.arr (us.map levelJson).toArray]
  | .app f a => Json.arr #[toJson "app", exprJson f, exprJson a]
  | .lam _ t b bi => Json.arr #[toJson "lambda", toJson (binderTag bi), exprJson t, exprJson b]
  | .forallE _ t b bi => Json.arr #[toJson "forall", toJson (binderTag bi), exprJson t, exprJson b]
  | .letE _ t v b nondep => Json.arr #[toJson "let", exprJson t, exprJson v, exprJson b, toJson nondep]
  | .lit (.natVal n) => Json.arr #[toJson "natLiteral", toJson n]
  | .lit (.strVal s) => Json.arr #[toJson "stringLiteral", toJson s]
  | .mdata _ e => exprJson e
  | .proj n i e => Json.arr #[toJson "projection", toJson n.toString, toJson i, exprJson e]
def refs (e : Expr) : Array String := (e.getUsedConstants.map Name.toString).qsort (fun a b => a < b)
def exportSnapshot (name : Name) (expectedOwner outputType outputRefs : String) (imported : Bool) : MetaM Unit := do
  let env <- getEnv
  let some ci := env.find? name | throwError "missing declaration"
  let value <- match ci with | .thmInfo t => pure t.value | _ => throwError "not theorem"
  if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars || value.hasMVar || value.hasFVar || value.hasLooseBVars then
    throwError "open theorem CI"
  let owner <- if imported then do
    let some idx := env.getModuleIdxFor? name | throwError "theorem is not imported"
    let some actual := env.header.moduleNames[idx.toNat]? | throwError "bad module index"
    unless actual.toString == expectedOwner do throwError "wrong actual owner"
    pure (Json.mkObj [("kind", toJson "ImportedModule"), ("module", toJson actual.toString), ("index", toJson idx.toNat)])
  else do
    unless (env.getModuleIdxFor? name).isNone do throwError "source theorem was inherited"
    pure (Json.mkObj [("kind", toJson "OwnModule"), ("module", toJson env.mainModule.toString)])
  let axioms <- collectAxioms name
  unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
    throwError "non-Std3 axiom"
  let typeText <- ppExpr ci.type
  IO.FS.writeFile outputType (Json.arr #[Json.mkObj [("name", toJson name.toString),
    ("levelParams", toJson (ci.levelParams.map Name.toString)), ("type", exprJson ci.type),
    ("value", Json.null), ("prettyType", toJson typeText.pretty)]] |>.compress)
  IO.FS.writeFile outputRefs ((Json.mkObj [("schemaVersion", toJson 1),
    ("probeMainModule", toJson env.mainModule.toString), ("rows", Json.arr #[Json.mkObj [
      ("name", toJson name.toString), ("kind", toJson "theorem"), ("closedType", toJson true),
      ("closedValue", toJson true), ("typeRefs", toJson (refs ci.type)), ("valueRefs", toJson (refs value)),
      ("axioms", toJson (axioms.map Name.toString)), ("owner", owner)]])]).pretty)
end C4Snapshot

set_option pp.universes true
set_option pp.fullNames true
set_option pp.explicit true
run_meta do
  C4Snapshot.exportSnapshot `OAI.PiExponent.exists_normalized_successive_approximations "SourceSnapshot" "missions/pi-irrationality-measure/verification/ap6/c4e/source-type.json" "missions/pi-irrationality-measure/verification/ap6/c4e/source-proof-references.json" false
