import Definitions.Def_Snaky35Cache12
import Solutions.SnakyMilestones.Certificate35Part11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_384_checked : entryAt 384 = entry_384 := by
  rw [entry_chunk_18 18 (by decide)]
  decide +kernel
theorem row_384 : rowAt 384 = data_384 := by
  rw [rowAt, dif_neg (by decide : ¬ 384 < 6), entry_384_checked]
  change forkRow [placeRow ⟨173, 2, 6, 4⟩ (rowAt 173), placeRow ⟨282, 4, 2, 4⟩ (rowAt 282), placeRow ⟨220, 2, 6, 4⟩ (rowAt 220), placeRow ⟨246, 2, 6, 4⟩ (rowAt 246), placeRow ⟨263, 2, 6, 4⟩ (rowAt 263), placeRow ⟨183, 6, 2, 4⟩ (rowAt 183), placeRow ⟨295, 0, 6, 4⟩ (rowAt 295)] = data_384
  rw [row_173, row_282, row_220, row_246, row_263, row_183, row_295]
  apply row_ext <;> decide +kernel
theorem entry_good_384 : EntryGood 384 := by
  unfold EntryGood
  rw [entry_384_checked]
  decide +kernel
theorem good_384 : Good (rowAt 384) := by
  rw [row_384]
  unfold Good
  decide +kernel

theorem entry_385_checked : entryAt 385 = entry_385 := by
  rw [entry_chunk_18 19 (by decide)]
  decide +kernel
theorem row_385 : rowAt 385 = data_385 := by
  rw [rowAt, dif_neg (by decide : ¬ 385 < 6), entry_385_checked]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (rowAt 63), placeRow ⟨64, 2, 1, 5⟩ (rowAt 64), placeRow ⟨55, 0, 5, 4⟩ (rowAt 55), placeRow ⟨369, 4, 1, 5⟩ (rowAt 369)] = data_385
  rw [row_63, row_64, row_55, row_369]
  apply row_ext <;> decide +kernel
theorem entry_good_385 : EntryGood 385 := by
  unfold EntryGood
  rw [entry_385_checked]
  decide +kernel
theorem good_385 : Good (rowAt 385) := by
  rw [row_385]
  unfold Good
  decide +kernel

theorem entry_386_checked : entryAt 386 = entry_386 := by
  rw [entry_chunk_19 0 (by decide)]
  decide +kernel
theorem row_386 : rowAt 386 = data_386 := by
  rw [rowAt, dif_neg (by decide : ¬ 386 < 6), entry_386_checked]
  change forkRow [placeRow ⟨217, 4, 1, 4⟩ (rowAt 217), placeRow ⟨172, 0, 5, 4⟩ (rowAt 172), placeRow ⟨173, 4, 1, 4⟩ (rowAt 173), placeRow ⟨217, 0, 5, 4⟩ (rowAt 217), placeRow ⟨294, 0, 5, 4⟩ (rowAt 294), placeRow ⟨294, 4, 1, 4⟩ (rowAt 294)] = data_386
  rw [row_217, row_172, row_173, row_294]
  apply row_ext <;> decide +kernel
theorem entry_good_386 : EntryGood 386 := by
  unfold EntryGood
  rw [entry_386_checked]
  decide +kernel
theorem good_386 : Good (rowAt 386) := by
  rw [row_386]
  unfold Good
  decide +kernel

theorem entry_387_checked : entryAt 387 = entry_387 := by
  rw [entry_chunk_19 1 (by decide)]
  decide +kernel
theorem row_387 : rowAt 387 = data_387 := by
  rw [rowAt, dif_neg (by decide : ¬ 387 < 6), entry_387_checked]
  change forkRow [placeRow ⟨14, 1, 4, 6⟩ (rowAt 14), placeRow ⟨370, 0, 5, 4⟩ (rowAt 370)] = data_387
  rw [row_14, row_370]
  apply row_ext <;> decide +kernel
theorem entry_good_387 : EntryGood 387 := by
  unfold EntryGood
  rw [entry_387_checked]
  decide +kernel
theorem good_387 : Good (rowAt 387) := by
  rw [row_387]
  unfold Good
  decide +kernel


theorem block12_group00_piece00_correct : (rowAt 384 = data_384 ∧ Good (rowAt 384) ∧ EntryGood 384) ∧ (rowAt 385 = data_385 ∧ Good (rowAt 385) ∧ EntryGood 385) ∧ (rowAt 386 = data_386 ∧ Good (rowAt 386) ∧ EntryGood 386) ∧ (rowAt 387 = data_387 ∧ Good (rowAt 387) ∧ EntryGood 387) ∧ True := by
  exact ⟨⟨row_384, good_384, entry_good_384⟩, ⟨row_385, good_385, entry_good_385⟩, ⟨row_386, good_386, entry_good_386⟩, ⟨row_387, good_387, entry_good_387⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
