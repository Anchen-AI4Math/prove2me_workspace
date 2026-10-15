import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_tendsto_analyticRemainder
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_actual_minor_analytic_bound

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.LiteralAnalytic

theorem solution : AnalyticAggregateStatement := by
  intro nu hnu d
  refine ⟨analyticRemainder d, tendsto_analyticRemainder d, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
  intro selection hne
  exact actual_minor_analytic_bound d (by linarith) hH selection hne
