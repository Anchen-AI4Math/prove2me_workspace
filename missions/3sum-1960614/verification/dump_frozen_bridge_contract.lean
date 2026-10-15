import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum1960614


theorem ThreeSum1960614.costs_solve_3sum (r : ℚ)
    (hr : 0 < r) (hcost : ∀ z ∈ costs, z < (r : ℝ)) :
    EndStatement.ThreeSum.SolvedInTime r := by sorry

open Lean
set_option pp.fullNames true
set_option pp.universes true
set_option pp.explicit true
set_option pp.notation false

private partial def alphaThreeSumFrozenContract (expr : Expr) : Expr :=
  match expr with
  | .app f a => .app (alphaThreeSumFrozenContract f) (alphaThreeSumFrozenContract a)
  | .lam _ t b i => .lam .anonymous (alphaThreeSumFrozenContract t) (alphaThreeSumFrozenContract b) i
  | .forallE _ t b i => .forallE .anonymous (alphaThreeSumFrozenContract t) (alphaThreeSumFrozenContract b) i
  | .letE _ t v b d => .letE .anonymous (alphaThreeSumFrozenContract t) (alphaThreeSumFrozenContract v) (alphaThreeSumFrozenContract b) d
  | .mdata _ e => alphaThreeSumFrozenContract e
  | .proj n i e => .proj n i (alphaThreeSumFrozenContract e)
  | e => e

run_meta do
  let ci ← getConstInfo `ThreeSum1960614.costs_solve_3sum
  let levels := ci.levelParams.zipIdx |>.map fun (_,i) => Level.param (Name.num `universe i)
  let normalized := alphaThreeSumFrozenContract (ci.type.instantiateLevelParams ci.levelParams levels)
  let record := Json.mkObj [
    ("name",toJson "ThreeSum1960614.costs_solve_3sum"),
    ("universeCount",toJson ci.levelParams.length),
    ("rawType",toJson (reprStr ci.type)),
    ("printedType",toJson (← Meta.ppExpr ci.type).pretty),
    ("normalizedType",toJson (reprStr normalized))]
  IO.FS.writeFile "missions/3sum-1960614/verification/machine-frozen-bridge-type.json" record.pretty
  logInfo "Read back the exact reviewed public bridge type"

/- Actual filtered-open scope transplanted from the pinned source. -/
open _root_.EndStatement renaming Instr -> Instr
open _root_.EndStatement renaming exec -> exec
open _root_.EndStatement renaming loadWords -> loadWords

example : Instr := EndStatement.Instr.accept
#check exec
#check loadWords
