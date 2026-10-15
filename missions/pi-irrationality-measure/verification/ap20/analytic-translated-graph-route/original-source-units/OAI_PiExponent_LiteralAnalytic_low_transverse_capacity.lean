theorem low_transverse_capacity {nu : ℝ} (d : FixedData nu) (H : ℝ) :
    (((Finset.univ : Finset (Transverse d H)).filter
      (fun A => indexWeight d A ≤ (d.base.A : ℝ) * H)).card : ℝ) ≤ lowIndexCount d H := by
  classical
  let f : {A : Transverse d H // indexWeight d A ≤ (d.base.A : ℝ) * H} →
      ↥(MatrixTranslation.transverseIndices (fixedWeights d) ((d.base.A : ℝ) * H)) :=
    fun A => ⟨A.1.1, (MatrixTranslation.mem_transverseIndices _ _ (fixedWeights_pos d) _).mpr A.2⟩
  have hinj : Function.Injective f := by
    intro A B h
    apply Subtype.ext
    apply Subtype.ext
    have hh := congrArg Subtype.val h
    simpa only [f] using hh
  have hh := Fintype.card_le_of_injective f hinj
  rw [Fintype.card_subtype] at hh
  have hc : Fintype.card ↥(MatrixTranslation.transverseIndices (fixedWeights d)
      ((d.base.A : ℝ) * H)) = lowIndexCount d H := by
    simp only [Fintype.card_coe, MatrixTranslation.card_transverseIndices]
    rfl
  rw [hc] at hh
  exact_mod_cast hh