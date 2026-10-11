import Definitions.Def_Snaky35Cache05
import Solutions.SnakyMilestones.Certificate35Block05Group02
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_184_checked : entryAt 184 = entry_184 := by
  rw [entry_chunk_8 18 (by decide)]
  decide +kernel
theorem row_184 : rowAt 184 = data_184 := by
  rw [rowAt, dif_neg (by decide : ¬ 184 < 6), entry_184_checked]
  change forkRow [placeRow ⟨34, 3, 4, 2⟩ (rowAt 34), placeRow ⟨35, 2, 5, 4⟩ (rowAt 35)] = data_184
  rw [row_34, row_35]
  apply row_ext <;> decide +kernel
theorem entry_good_184 : EntryGood 184 := by
  unfold EntryGood
  rw [entry_184_checked]
  decide +kernel
theorem good_184 : Good (rowAt 184) := by
  rw [row_184]
  unfold Good
  decide +kernel

theorem entry_185_checked : entryAt 185 = entry_185 := by
  rw [entry_chunk_8 19 (by decide)]
  decide +kernel
theorem row_185 : rowAt 185 = data_185 := by
  rw [rowAt, dif_neg (by decide : ¬ 185 < 6), entry_185_checked]
  change forkRow [placeRow ⟨44, 3, 4, 5⟩ (rowAt 44), placeRow ⟨49, 0, 4, 5⟩ (rowAt 49), placeRow ⟨84, 0, 3, 4⟩ (rowAt 84)] = data_185
  rw [row_44, row_49, row_84]
  apply row_ext <;> decide +kernel
theorem entry_good_185 : EntryGood 185 := by
  unfold EntryGood
  rw [entry_185_checked]
  decide +kernel
theorem good_185 : Good (rowAt 185) := by
  rw [row_185]
  unfold Good
  decide +kernel

theorem entry_186_checked : entryAt 186 = entry_186 := by
  rw [entry_chunk_9 0 (by decide)]
  decide +kernel
theorem row_186 : rowAt 186 = data_186 := by
  rw [rowAt, dif_neg (by decide : ¬ 186 < 6), entry_186_checked]
  change forkRow [placeRow ⟨7, 6, 0, 3⟩ (rowAt 7), placeRow ⟨141, 2, 5, 4⟩ (rowAt 141)] = data_186
  rw [row_7, row_141]
  apply row_ext <;> decide +kernel
theorem entry_good_186 : EntryGood 186 := by
  unfold EntryGood
  rw [entry_186_checked]
  decide +kernel
theorem good_186 : Good (rowAt 186) := by
  rw [row_186]
  unfold Good
  decide +kernel

theorem entry_187_checked : entryAt 187 = entry_187 := by
  rw [entry_chunk_9 1 (by decide)]
  decide +kernel
theorem row_187 : rowAt 187 = data_187 := by
  rw [rowAt, dif_neg (by decide : ¬ 187 < 6), entry_187_checked]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (rowAt 6), placeRow ⟨108, 3, 4, 5⟩ (rowAt 108)] = data_187
  rw [row_6, row_108]
  apply row_ext <;> decide +kernel
theorem entry_good_187 : EntryGood 187 := by
  unfold EntryGood
  rw [entry_187_checked]
  decide +kernel
theorem good_187 : Good (rowAt 187) := by
  rw [row_187]
  unfold Good
  decide +kernel


theorem block05_group03_piece00_correct : (rowAt 184 = data_184 ∧ Good (rowAt 184) ∧ EntryGood 184) ∧ (rowAt 185 = data_185 ∧ Good (rowAt 185) ∧ EntryGood 185) ∧ (rowAt 186 = data_186 ∧ Good (rowAt 186) ∧ EntryGood 186) ∧ (rowAt 187 = data_187 ∧ Good (rowAt 187) ∧ EntryGood 187) ∧ True := by
  exact ⟨⟨row_184, good_184, entry_good_184⟩, ⟨row_185, good_185, entry_good_185⟩, ⟨row_186, good_186, entry_good_186⟩, ⟨row_187, good_187, entry_good_187⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
