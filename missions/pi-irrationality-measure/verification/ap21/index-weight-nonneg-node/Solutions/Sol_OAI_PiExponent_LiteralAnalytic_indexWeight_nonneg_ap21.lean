import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Log
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_RowTranslation_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.LiteralAnalytic OAI.PiExponent.DeterminantContradiction


namespace OAI.PiExponent.DeterminantContradiction
open Filter
open scoped Topology
private theorem logWeights_eq {nu : ℝ} (d : FixedData nu) (i : Fin d.m) :
    MatrixArithmetic.logWeights (finiteDenominators d) i = d.x (i.val + 1) :=
  (d.x_log i.val).symm
end OAI.PiExponent.DeterminantContradiction

namespace OAI.PiExponent.LiteralAnalytic
open scoped BigOperators
open DeterminantContradiction
private theorem fixedWeights_pos {nu : ℝ} (d : FixedData nu) (i : Fin d.m) :
    0 < fixedWeights d i := by
  change 0 < MatrixArithmetic.logWeights (finiteDenominators d) i
  rw [logWeights_eq]
  exact lt_of_lt_of_le zero_lt_one (d.x_one_le _)
end OAI.PiExponent.LiteralAnalytic

theorem solution {nu : ℝ} (d : FixedData nu) {H : ℝ} (a : Transverse d H) :
    0 ≤ indexWeight d a := by
  unfold indexWeight MatrixTranslationBounds.weight
  exact Finset.sum_nonneg fun i _ => mul_nonneg (fixedWeights_pos d i).le (Nat.cast_nonneg _)
