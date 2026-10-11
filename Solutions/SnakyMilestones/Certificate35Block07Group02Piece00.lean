import Definitions.Def_Snaky35Cache07
import Solutions.SnakyMilestones.Certificate35Block07Group01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_240_checked : entryAt 240 = entry_240 := by
  rw [entry_chunk_11 14 (by decide)]
  decide +kernel
theorem row_240 : rowAt 240 = data_240 := by
  rw [rowAt, dif_neg (by decide : ¬ 240 < 6), entry_240_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨237, 0, 2, 4⟩ (rowAt 237)] = data_240
  rw [row_6, row_237]
  apply row_ext <;> decide +kernel
theorem entry_good_240 : EntryGood 240 := by
  unfold EntryGood
  rw [entry_240_checked]
  decide +kernel
theorem good_240 : Good (rowAt 240) := by
  rw [row_240]
  unfold Good
  decide +kernel

theorem entry_241_checked : entryAt 241 = entry_241 := by
  rw [entry_chunk_11 15 (by decide)]
  decide +kernel
theorem row_241 : rowAt 241 = data_241 := by
  rw [rowAt, dif_neg (by decide : ¬ 241 < 6), entry_241_checked]
  change forkRow [placeRow ⟨131, 1, 5, 4⟩ (rowAt 131), placeRow ⟨159, 1, 5, 4⟩ (rowAt 159), placeRow ⟨61, 0, 4, 5⟩ (rowAt 61)] = data_241
  rw [row_131, row_159, row_61]
  apply row_ext <;> decide +kernel
theorem entry_good_241 : EntryGood 241 := by
  unfold EntryGood
  rw [entry_241_checked]
  decide +kernel
theorem good_241 : Good (rowAt 241) := by
  rw [row_241]
  unfold Good
  decide +kernel

theorem entry_242_checked : entryAt 242 = entry_242 := by
  rw [entry_chunk_11 16 (by decide)]
  decide +kernel
theorem row_242 : rowAt 242 = data_242 := by
  rw [rowAt, dif_neg (by decide : ¬ 242 < 6), entry_242_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨190, 0, 5, 4⟩ (rowAt 190)] = data_242
  rw [row_6, row_190]
  apply row_ext <;> decide +kernel
theorem entry_good_242 : EntryGood 242 := by
  unfold EntryGood
  rw [entry_242_checked]
  decide +kernel
theorem good_242 : Good (rowAt 242) := by
  rw [row_242]
  unfold Good
  decide +kernel

theorem entry_243_checked : entryAt 243 = entry_243 := by
  rw [entry_chunk_11 17 (by decide)]
  decide +kernel
theorem row_243 : rowAt 243 = data_243 := by
  rw [rowAt, dif_neg (by decide : ¬ 243 < 6), entry_243_checked]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (rowAt 6), placeRow ⟨233, 0, 2, 5⟩ (rowAt 233)] = data_243
  rw [row_6, row_233]
  apply row_ext <;> decide +kernel
theorem entry_good_243 : EntryGood 243 := by
  unfold EntryGood
  rw [entry_243_checked]
  decide +kernel
theorem good_243 : Good (rowAt 243) := by
  rw [row_243]
  unfold Good
  decide +kernel


theorem block07_group02_piece00_correct : (rowAt 240 = data_240 ∧ Good (rowAt 240) ∧ EntryGood 240) ∧ (rowAt 241 = data_241 ∧ Good (rowAt 241) ∧ EntryGood 241) ∧ (rowAt 242 = data_242 ∧ Good (rowAt 242) ∧ EntryGood 242) ∧ (rowAt 243 = data_243 ∧ Good (rowAt 243) ∧ EntryGood 243) ∧ True := by
  exact ⟨⟨row_240, good_240, entry_good_240⟩, ⟨row_241, good_241, entry_good_241⟩, ⟨row_242, good_242, entry_good_242⟩, ⟨row_243, good_243, entry_good_243⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
