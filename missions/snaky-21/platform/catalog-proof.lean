import Definitions.Def_Snaky21Catalog
open OAI.Snaky21.Certificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem solution : numberedCards.length = 728 ∧ (numberedCards.map (fun c => decide (0 < c.height ∧ c.height ≤ 21))).all id = true := by
  decide +kernel

#print axioms solution
