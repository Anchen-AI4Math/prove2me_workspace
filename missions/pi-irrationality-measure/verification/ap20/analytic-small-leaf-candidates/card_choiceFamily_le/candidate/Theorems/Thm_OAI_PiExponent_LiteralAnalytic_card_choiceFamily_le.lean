import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.LiteralAnalytic

theorem OAI.PiExponent.LiteralAnalytic.card_choiceFamily_le {nu : ℝ} (d : FixedData nu) (H : ℝ) :
    Fintype.card (ChoiceFamily d H) ≤ translationTermCount d.m d.v0 H ^ actualRowCount d H := by
  sorry
