import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.LiteralAnalytic

theorem OAI.PiExponent.LiteralAnalytic.tendsto_analyticRemainder {nu : ℝ} (d : FixedData nu) :
    Tendsto (analyticRemainder d) atTop (𝓝 0) := by
  sorry
