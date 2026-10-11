import Solutions.Snaky21.Forcing

namespace OAI.Snaky21
open SnakyPrototype

theorem orient_add (r : Fin 8) (x y : Cell) :
    orient r (x + y) = orient r x + orient r y := by
  fin_cases r <;> ext <;> simp [orient] <;> ring

theorem orient_neg (r : Fin 8) (x : Cell) : orient r (-x) = -orient r x := by
  fin_cases r <;> ext <;> simp [orient]

theorem orient_closed (r s : Fin 8) :
    ∃ u : Fin 8, ∀ x : Cell, orient r (orient s x) = orient u x := by
  fin_cases r <;> fin_cases s
  · exact ⟨0, by intro x; ext <;> simp [orient]⟩
  · exact ⟨1, by intro x; ext <;> simp [orient]⟩
  · exact ⟨2, by intro x; ext <;> simp [orient]⟩
  · exact ⟨3, by intro x; ext <;> simp [orient]⟩
  · exact ⟨4, by intro x; ext <;> simp [orient]⟩
  · exact ⟨5, by intro x; ext <;> simp [orient]⟩
  · exact ⟨6, by intro x; ext <;> simp [orient]⟩
  · exact ⟨7, by intro x; ext <;> simp [orient]⟩
  · exact ⟨1, by intro x; ext <;> simp [orient]⟩
  · exact ⟨0, by intro x; ext <;> simp [orient]⟩
  · exact ⟨3, by intro x; ext <;> simp [orient]⟩
  · exact ⟨2, by intro x; ext <;> simp [orient]⟩
  · exact ⟨5, by intro x; ext <;> simp [orient]⟩
  · exact ⟨4, by intro x; ext <;> simp [orient]⟩
  · exact ⟨7, by intro x; ext <;> simp [orient]⟩
  · exact ⟨6, by intro x; ext <;> simp [orient]⟩
  · exact ⟨2, by intro x; ext <;> simp [orient]⟩
  · exact ⟨5, by intro x; ext <;> simp [orient]⟩
  · exact ⟨0, by intro x; ext <;> simp [orient]⟩
  · exact ⟨7, by intro x; ext <;> simp [orient]⟩
  · exact ⟨6, by intro x; ext <;> simp [orient]⟩
  · exact ⟨1, by intro x; ext <;> simp [orient]⟩
  · exact ⟨4, by intro x; ext <;> simp [orient]⟩
  · exact ⟨3, by intro x; ext <;> simp [orient]⟩
  · exact ⟨3, by intro x; ext <;> simp [orient]⟩
  · exact ⟨4, by intro x; ext <;> simp [orient]⟩
  · exact ⟨1, by intro x; ext <;> simp [orient]⟩
  · exact ⟨6, by intro x; ext <;> simp [orient]⟩
  · exact ⟨7, by intro x; ext <;> simp [orient]⟩
  · exact ⟨0, by intro x; ext <;> simp [orient]⟩
  · exact ⟨5, by intro x; ext <;> simp [orient]⟩
  · exact ⟨2, by intro x; ext <;> simp [orient]⟩
  · exact ⟨4, by intro x; ext <;> simp [orient]⟩
  · exact ⟨3, by intro x; ext <;> simp [orient]⟩
  · exact ⟨6, by intro x; ext <;> simp [orient]⟩
  · exact ⟨1, by intro x; ext <;> simp [orient]⟩
  · exact ⟨0, by intro x; ext <;> simp [orient]⟩
  · exact ⟨7, by intro x; ext <;> simp [orient]⟩
  · exact ⟨2, by intro x; ext <;> simp [orient]⟩
  · exact ⟨5, by intro x; ext <;> simp [orient]⟩
  · exact ⟨5, by intro x; ext <;> simp [orient]⟩
  · exact ⟨2, by intro x; ext <;> simp [orient]⟩
  · exact ⟨7, by intro x; ext <;> simp [orient]⟩
  · exact ⟨0, by intro x; ext <;> simp [orient]⟩
  · exact ⟨1, by intro x; ext <;> simp [orient]⟩
  · exact ⟨6, by intro x; ext <;> simp [orient]⟩
  · exact ⟨3, by intro x; ext <;> simp [orient]⟩
  · exact ⟨4, by intro x; ext <;> simp [orient]⟩
  · exact ⟨6, by intro x; ext <;> simp [orient]⟩
  · exact ⟨7, by intro x; ext <;> simp [orient]⟩
  · exact ⟨4, by intro x; ext <;> simp [orient]⟩
  · exact ⟨5, by intro x; ext <;> simp [orient]⟩
  · exact ⟨2, by intro x; ext <;> simp [orient]⟩
  · exact ⟨3, by intro x; ext <;> simp [orient]⟩
  · exact ⟨0, by intro x; ext <;> simp [orient]⟩
  · exact ⟨1, by intro x; ext <;> simp [orient]⟩
  · exact ⟨7, by intro x; ext <;> simp [orient]⟩
  · exact ⟨6, by intro x; ext <;> simp [orient]⟩
  · exact ⟨5, by intro x; ext <;> simp [orient]⟩
  · exact ⟨4, by intro x; ext <;> simp [orient]⟩
  · exact ⟨3, by intro x; ext <;> simp [orient]⟩
  · exact ⟨2, by intro x; ext <;> simp [orient]⟩
  · exact ⟨1, by intro x; ext <;> simp [orient]⟩
  · exact ⟨0, by intro x; ext <;> simp [orient]⟩

theorem orient_injective (r : Fin 8) : Function.Injective (orient r) := by
  intro x y h
  fin_cases r <;> simp only [orient, Prod.mk.injEq, neg_inj] at h <;>
    apply Prod.ext <;> tauto

theorem orient_surjective (r : Fin 8) : Function.Surjective (orient r) := by
  intro x
  fin_cases r
  · exact ⟨x, rfl⟩
  · exact ⟨(x.2, x.1), rfl⟩
  · exact ⟨(x.1, -x.2), by simp [orient]⟩
  · exact ⟨(x.2, -x.1), by simp [orient]⟩
  · exact ⟨(-x.1, x.2), by simp [orient]⟩
  · exact ⟨(-x.2, x.1), by simp [orient]⟩
  · exact ⟨(-x.1, -x.2), by simp [orient]⟩
  · exact ⟨(-x.2, -x.1), by simp [orient]⟩

theorem placement_injective (r : Fin 8) (t : Cell) :
    Function.Injective (placement r t) := by
  intro x y h
  apply orient_injective r
  exact add_right_cancel h

theorem placement_surjective (r : Fin 8) (t : Cell) :
    Function.Surjective (placement r t) := by
  intro y
  obtain ⟨x, hx⟩ := orient_surjective r (y - t)
  exact ⟨x, by simp [placement, hx]⟩

theorem mem_placement_image (r : Fin 8) (t : Cell) (x : Cell) (s : Finset Cell) :
    placement r t x ∈ s.image (placement r t) ↔ x ∈ s := by
  constructor
  · intro h
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp h
    have hxy := placement_injective r t he
    simpa only [hxy] using hy
  · intro hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

theorem hasSnaky_placed (r : Fin 8) (t : Cell) {M : Finset Cell}
    (h : HasSnaky M) : HasSnaky (M.image (placement r t)) := by
  obtain ⟨s, u, hu⟩ := h
  obtain ⟨v, hv⟩ := orient_closed r s
  refine ⟨v, orient r u + t, ?_⟩
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  have hh : placement r t (placement s u x) = placement v (orient r u + t) x := by
    simp only [placement, orient_add, hv]
    abel
  rw [← hh]
  exact Finset.mem_image.mpr ⟨placement s u x, hu (Finset.mem_image.mpr ⟨x, hx, rfl⟩), rfl⟩

theorem canForce_transport (n : ℕ) (r : Fin 8) (t : Cell)
    {M B : Finset Cell} (h : CanForce n M B) :
    CanForce n (M.image (placement r t)) (B.image (placement r t)) := by
  induction n generalizing M B with
  | zero => exact hasSnaky_placed r t h
  | succ n ih =>
    obtain ⟨m, hmM, hmB, hw⟩ := h
    have hinj := placement_injective r t
    refine ⟨placement r t m, ?_, ?_, ?_⟩
    · simpa only [mem_placement_image] using hmM
    · simpa only [mem_placement_image] using hmB
    rw [← Finset.image_insert]
    rcases hw with hw | hw
    · exact Or.inl (hasSnaky_placed r t hw)
    · refine Or.inr ?_
      intro b hbM hbB
      obtain ⟨b₀, rfl⟩ := placement_surjective r t b
      rw [← Finset.image_insert]
      apply ih
      apply hw
      · simpa only [mem_placement_image] using hbM
      · simpa only [mem_placement_image] using hbB

theorem placed_valid (r : Fin 8) (t : Cell) {c : Card} (h : Valid c) :
    Valid (placed r t c) := by
  refine ⟨Finset.image_subset_image h.1, h.2.1, ?_⟩
  intro M B hM hB
  let f := placement r t
  let M₀ := M.preimage f (placement_injective r t).injOn
  let B₀ := B.preimage f (placement_injective r t).injOn
  have hforce : CanForce c.height M₀ B₀ := by
    apply h.2.2
    · intro x hx
      apply Finset.mem_preimage.mpr
      exact hM (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    · apply Finset.disjoint_left.mpr
      intro x hxB hxT
      exact Finset.disjoint_left.mp hB (Finset.mem_preimage.mp hxB)
        (Finset.mem_image.mpr ⟨x, hxT, rfl⟩)
  have himg (s : Finset Cell) :
      (s.preimage f (placement_injective r t).injOn).image f = s := by
    apply Finset.ext
    intro y
    constructor
    · rintro hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_preimage.mp hx
    · intro hy
      obtain ⟨x, rfl⟩ := placement_surjective r t y
      exact Finset.mem_image.mpr ⟨x, Finset.mem_preimage.mpr hy, rfl⟩
  have hh := canForce_transport c.height r t hforce
  change CanForce c.height (M₀.image f) (B₀.image f) at hh
  rw [show M₀.image f = M from himg M, show B₀.image f = B from himg B] at hh
  exact hh

end OAI.Snaky21
