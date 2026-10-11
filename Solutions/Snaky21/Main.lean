import Solutions.Snaky21.Certificate11
import Solutions.Snaky21.Strategy
import Solutions.Snaky21.Catalog

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace OAI.Snaky21
open SnakyPrototype SnakyPrototype.OrdinaryStrategy Certificate

theorem certificate21_endpoint :
    card_727.required = ∅ ∧ card_727.height = 21 ∧
    card_727.envelope.card = 251 ∧
    (∀ x ∈ card_727.envelope, 0 ≤ x.1 ∧ x.1 ≤ 16 ∧ 0 ≤ x.2 ∧ x.2 ≤ 16) := by
  decide +kernel

theorem certificate21_force : CanForce 21 ∅ ∅ := by
  have hv := valid_727
  have hh := hv.2.2 ∅ ∅ (by rw [certificate21_endpoint.1]) (by simp)
  rw [certificate21_endpoint.2.1] at hh
  exact hh

theorem snaky21_complete :
    ∃ σ : Policy Cell,
      (∀ r M B, σ r M B ∉ M ∧ σ r M B ∉ B) ∧
      ∀ β : ℕ → Cell, LegalRepliesBeforeFinal σ 21 β ∅ ∅ →
        HasSnaky (playState σ 21 β ∅ ∅ 21).1 ∧
        (playState σ 21 β ∅ ∅ 21).1.card = 21 ∧
        Disjoint (playState σ 21 β ∅ ∅ 21).1 (playState σ 21 β ∅ ∅ 20).2 ∧
        ∀ k, k < 21 →
          Disjoint (playState σ 21 β ∅ ∅ k).1 (playState σ 21 β ∅ ∅ k).2 ∧
          (playState σ 21 β ∅ ∅ k).2.card = k := by
  exact force_extract 21 (by decide) certificate21_force

end OAI.Snaky21

#print axioms OAI.Snaky21.combination_rule
#print axioms OAI.Snaky21.placed_valid
#print axioms OAI.Snaky21.force_extract
#print axioms OAI.Snaky21.certificate21_endpoint
#print axioms OAI.Snaky21.snaky21_complete
