import Definitions.Def_Snaky35Cache09
import Solutions.SnakyMilestones.Certificate35Block09Group01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_304_checked : entryAt 304 = entry_304 := by
  rw [entry_chunk_14 18 (by decide)]
  decide +kernel
theorem row_304 : rowAt 304 = data_304 := by
  rw [rowAt, dif_neg (by decide : ¬ 304 < 6), entry_304_checked]
  change forkRow [placeRow ⟨55, 4, 3, 4⟩ (rowAt 55), placeRow ⟨202, 0, 8, 4⟩ (rowAt 202), placeRow ⟨131, 3, 3, 4⟩ (rowAt 131)] = data_304
  rw [row_55, row_202, row_131]
  apply row_ext <;> decide +kernel
theorem entry_good_304 : EntryGood 304 := by
  unfold EntryGood
  rw [entry_304_checked]
  decide +kernel
theorem good_304 : Good (rowAt 304) := by
  rw [row_304]
  unfold Good
  decide +kernel

theorem entry_305_checked : entryAt 305 = entry_305 := by
  rw [entry_chunk_14 19 (by decide)]
  decide +kernel
theorem row_305 : rowAt 305 = data_305 := by
  rw [rowAt, dif_neg (by decide : ¬ 305 < 6), entry_305_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨278, 0, 1, 4⟩ (rowAt 278)] = data_305
  rw [row_6, row_278]
  apply row_ext <;> decide +kernel
theorem entry_good_305 : EntryGood 305 := by
  unfold EntryGood
  rw [entry_305_checked]
  decide +kernel
theorem good_305 : Good (rowAt 305) := by
  rw [row_305]
  unfold Good
  decide +kernel

theorem entry_306_checked : entryAt 306 = entry_306 := by
  rw [entry_chunk_15 0 (by decide)]
  decide +kernel
theorem row_306 : rowAt 306 = data_306 := by
  rw [rowAt, dif_neg (by decide : ¬ 306 < 6), entry_306_checked]
  change forkRow [placeRow ⟨4, 1, 4, 3⟩ (rowAt 4), placeRow ⟨288, 0, 6, 4⟩ (rowAt 288)] = data_306
  rw [row_4, row_288]
  apply row_ext <;> decide +kernel
theorem entry_good_306 : EntryGood 306 := by
  unfold EntryGood
  rw [entry_306_checked]
  decide +kernel
theorem good_306 : Good (rowAt 306) := by
  rw [row_306]
  unfold Good
  decide +kernel

theorem entry_307_checked : entryAt 307 = entry_307 := by
  rw [entry_chunk_15 1 (by decide)]
  decide +kernel
theorem row_307 : rowAt 307 = data_307 := by
  rw [rowAt, dif_neg (by decide : ¬ 307 < 6), entry_307_checked]
  change forkRow [placeRow ⟨0, 7, 4, 6⟩ (rowAt 0), placeRow ⟨273, 0, 5, 5⟩ (rowAt 273)] = data_307
  rw [row_0, row_273]
  apply row_ext <;> decide +kernel
theorem entry_good_307 : EntryGood 307 := by
  unfold EntryGood
  rw [entry_307_checked]
  decide +kernel
theorem good_307 : Good (rowAt 307) := by
  rw [row_307]
  unfold Good
  decide +kernel


theorem block09_group02_piece00_correct : (rowAt 304 = data_304 ∧ Good (rowAt 304) ∧ EntryGood 304) ∧ (rowAt 305 = data_305 ∧ Good (rowAt 305) ∧ EntryGood 305) ∧ (rowAt 306 = data_306 ∧ Good (rowAt 306) ∧ EntryGood 306) ∧ (rowAt 307 = data_307 ∧ Good (rowAt 307) ∧ EntryGood 307) ∧ True := by
  exact ⟨⟨row_304, good_304, entry_good_304⟩, ⟨row_305, good_305, entry_good_305⟩, ⟨row_306, good_306, entry_good_306⟩, ⟨row_307, good_307, entry_good_307⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
