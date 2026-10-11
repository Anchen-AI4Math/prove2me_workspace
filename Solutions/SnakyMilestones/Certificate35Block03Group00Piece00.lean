import Definitions.Def_Snaky35Cache03
import Solutions.SnakyMilestones.Certificate35Part02
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_96_checked : entryAt 96 = entry_96 := by
  rw [entry_chunk_4 10 (by decide)]
  decide +kernel
theorem row_96 : rowAt 96 = data_96 := by
  rw [rowAt, dif_neg (by decide : ¬ 96 < 6), entry_96_checked]
  change forkRow [placeRow ⟨6, 1, 5, 5⟩ (rowAt 6), placeRow ⟨70, 0, 3, 5⟩ (rowAt 70)] = data_96
  rw [row_6, row_70]
  apply row_ext <;> decide +kernel
theorem entry_good_96 : EntryGood 96 := by
  unfold EntryGood
  rw [entry_96_checked]
  decide +kernel
theorem good_96 : Good (rowAt 96) := by
  rw [row_96]
  unfold Good
  decide +kernel

theorem entry_97_checked : entryAt 97 = entry_97 := by
  rw [entry_chunk_4 11 (by decide)]
  decide +kernel
theorem row_97 : rowAt 97 = data_97 := by
  rw [rowAt, dif_neg (by decide : ¬ 97 < 6), entry_97_checked]
  change forkRow [placeRow ⟨6, 6, 0, 3⟩ (rowAt 6), placeRow ⟨44, 0, 5, 4⟩ (rowAt 44)] = data_97
  rw [row_6, row_44]
  apply row_ext <;> decide +kernel
theorem entry_good_97 : EntryGood 97 := by
  unfold EntryGood
  rw [entry_97_checked]
  decide +kernel
theorem good_97 : Good (rowAt 97) := by
  rw [row_97]
  unfold Good
  decide +kernel

theorem entry_98_checked : entryAt 98 = entry_98 := by
  rw [entry_chunk_4 12 (by decide)]
  decide +kernel
theorem row_98 : rowAt 98 = data_98 := by
  rw [rowAt, dif_neg (by decide : ¬ 98 < 6), entry_98_checked]
  change forkRow [placeRow ⟨6, 6, 2, 3⟩ (rowAt 6), placeRow ⟨44, 0, 7, 4⟩ (rowAt 44)] = data_98
  rw [row_6, row_44]
  apply row_ext <;> decide +kernel
theorem entry_good_98 : EntryGood 98 := by
  unfold EntryGood
  rw [entry_98_checked]
  decide +kernel
theorem good_98 : Good (rowAt 98) := by
  rw [row_98]
  unfold Good
  decide +kernel

theorem entry_99_checked : entryAt 99 = entry_99 := by
  rw [entry_chunk_4 13 (by decide)]
  decide +kernel
theorem row_99 : rowAt 99 = data_99 := by
  rw [rowAt, dif_neg (by decide : ¬ 99 < 6), entry_99_checked]
  change forkRow [placeRow ⟨2, 1, 3, 2⟩ (rowAt 2), placeRow ⟨24, 0, 5, 4⟩ (rowAt 24)] = data_99
  rw [row_2, row_24]
  apply row_ext <;> decide +kernel
theorem entry_good_99 : EntryGood 99 := by
  unfold EntryGood
  rw [entry_99_checked]
  decide +kernel
theorem good_99 : Good (rowAt 99) := by
  rw [row_99]
  unfold Good
  decide +kernel


theorem block03_group00_piece00_correct : (rowAt 96 = data_96 ∧ Good (rowAt 96) ∧ EntryGood 96) ∧ (rowAt 97 = data_97 ∧ Good (rowAt 97) ∧ EntryGood 97) ∧ (rowAt 98 = data_98 ∧ Good (rowAt 98) ∧ EntryGood 98) ∧ (rowAt 99 = data_99 ∧ Good (rowAt 99) ∧ EntryGood 99) ∧ True := by
  exact ⟨⟨row_96, good_96, entry_good_96⟩, ⟨row_97, good_97, entry_good_97⟩, ⟨row_98, good_98, entry_good_98⟩, ⟨row_99, good_99, entry_good_99⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
