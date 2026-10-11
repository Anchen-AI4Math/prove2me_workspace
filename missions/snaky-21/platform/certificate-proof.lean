import Definitions.Def_Snaky21Data11
import Theorems.Thm_OAI_Snaky21_Certificate_block11_valid
import Theorems.Thm_OAI_Snaky21_Certificate_catalog_correct
open OAI.Snaky21 OAI.SnakyPrototype OAI.Snaky21.Certificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem solution : Valid card_727 ∧ (card_727.required = ∅ ∧ card_727.height = 21 ∧ card_727.envelope.card = 251 ∧ (∀ x ∈ card_727.envelope, 0 ≤ x.1 ∧ x.1 ≤ 16 ∧ 0 ≤ x.2 ∧ x.2 ≤ 16)) ∧ (numberedCards.length = 728 ∧ (numberedCards.map (fun c => decide (0 < c.height ∧ c.height ≤ 21))).all id = true) := by
  refine ⟨block11_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, ?_, catalog_correct⟩
  decide +kernel
