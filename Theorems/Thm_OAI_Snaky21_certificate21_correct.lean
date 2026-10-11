-- Exact public interface; reference placeholder, not proof evidence.
import Definitions.Def_Snaky21Catalog
import Definitions.Def_Snaky21Data11
open OAI.Snaky21 OAI.SnakyPrototype OAI.Snaky21.Certificate

theorem OAI.Snaky21.certificate21_correct : Valid card_727 ∧ (card_727.required = ∅ ∧ card_727.height = 21 ∧ card_727.envelope.card = 251 ∧ (∀ x ∈ card_727.envelope, 0 ≤ x.1 ∧ x.1 ≤ 16 ∧ 0 ≤ x.2 ∧ x.2 ≤ 16)) ∧ (numberedCards.length = 728 ∧ (numberedCards.map (fun c => decide (0 < c.height ∧ c.height ≤ 21))).all id = true) := by sorry
