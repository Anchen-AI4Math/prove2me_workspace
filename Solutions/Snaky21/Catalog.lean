import Definitions.Def_Snaky21Catalog

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace OAI.Snaky21.Certificate

theorem catalog_correct :
    numberedCards.length = 728 ∧
    (numberedCards.map (fun c => decide (0 < c.height ∧ c.height ≤ 21))).all id = true := by
  decide +kernel

end OAI.Snaky21.Certificate

#print axioms OAI.Snaky21.Certificate.catalog_correct
