import Definitions.Def_Snaky35Cache03
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_group00_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_5 (j : ℕ) (hj : j < 20) : entryAt (106 + j) = tableChunk_5[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.1) j hj
theorem row_0 : rowAt 0 = data_0 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.1).1
theorem row_1 : rowAt 1 = data_1 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.1).1
theorem row_4 : rowAt 4 = data_4 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_24 : rowAt 24 = data_24 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_36 : rowAt 36 = data_36 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.1).1
theorem row_55 : rowAt 55 = data_55 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_61 : rowAt 61 = data_61 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_67 : rowAt 67 = data_67 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.2.2.2.1).1
theorem row_70 : rowAt 70 = data_70 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.2.2.2.2.2.2.1).1
theorem row_93 : rowAt 93 = data_93 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_100 : rowAt 100 = data_100 := (OAI.SnakyCertificate.MilestoneChecks.block03_group00_correct.2.2.2.2.1).1
theorem entry_116_checked : entryAt 116 = entry_116 := by
  rw [entry_chunk_5 10 (by decide)]
  decide +kernel
theorem row_116 : rowAt 116 = data_116 := by
  rw [rowAt, dif_neg (by decide : ¬ 116 < 6), entry_116_checked]
  change forkRow [placeRow ⟨0, 7, 4, 6⟩ (rowAt 0), placeRow ⟨24, 2, 5, 4⟩ (rowAt 24)] = data_116
  rw [row_0, row_24]
  apply row_ext <;> decide +kernel
theorem entry_good_116 : EntryGood 116 := by
  unfold EntryGood
  rw [entry_116_checked]
  decide +kernel
theorem good_116 : Good (rowAt 116) := by
  rw [row_116]
  unfold Good
  decide +kernel

theorem entry_117_checked : entryAt 117 = entry_117 := by
  rw [entry_chunk_5 11 (by decide)]
  decide +kernel
theorem row_117 : rowAt 117 = data_117 := by
  rw [rowAt, dif_neg (by decide : ¬ 117 < 6), entry_117_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨100, 0, 5, 4⟩ (rowAt 100)] = data_117
  rw [row_6, row_100]
  apply row_ext <;> decide +kernel
theorem entry_good_117 : EntryGood 117 := by
  unfold EntryGood
  rw [entry_117_checked]
  decide +kernel
theorem good_117 : Good (rowAt 117) := by
  rw [row_117]
  unfold Good
  decide +kernel

theorem entry_118_checked : entryAt 118 = entry_118 := by
  rw [entry_chunk_5 12 (by decide)]
  decide +kernel
theorem row_118 : rowAt 118 = data_118 := by
  rw [rowAt, dif_neg (by decide : ¬ 118 < 6), entry_118_checked]
  change forkRow [placeRow ⟨4, 7, 3, 1⟩ (rowAt 4), placeRow ⟨61, 1, 5, 4⟩ (rowAt 61)] = data_118
  rw [row_4, row_61]
  apply row_ext <;> decide +kernel
theorem entry_good_118 : EntryGood 118 := by
  unfold EntryGood
  rw [entry_118_checked]
  decide +kernel
theorem good_118 : Good (rowAt 118) := by
  rw [row_118]
  unfold Good
  decide +kernel

theorem entry_119_checked : entryAt 119 = entry_119 := by
  rw [entry_chunk_5 13 (by decide)]
  decide +kernel
theorem row_119 : rowAt 119 = data_119 := by
  rw [rowAt, dif_neg (by decide : ¬ 119 < 6), entry_119_checked]
  change forkRow [placeRow ⟨6, 6, 1, 3⟩ (rowAt 6), placeRow ⟨55, 0, 6, 4⟩ (rowAt 55)] = data_119
  rw [row_6, row_55]
  apply row_ext <;> decide +kernel
theorem entry_good_119 : EntryGood 119 := by
  unfold EntryGood
  rw [entry_119_checked]
  decide +kernel
theorem good_119 : Good (rowAt 119) := by
  rw [row_119]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 116 = data_116 ∧ Good (rowAt 116) ∧ EntryGood 116) ∧ (rowAt 117 = data_117 ∧ Good (rowAt 117) ∧ EntryGood 117) ∧ (rowAt 118 = data_118 ∧ Good (rowAt 118) ∧ EntryGood 118) ∧ (rowAt 119 = data_119 ∧ Good (rowAt 119) ∧ EntryGood 119) ∧ True := by
  exact ⟨⟨row_116, good_116, entry_good_116⟩, ⟨row_117, good_117, entry_good_117⟩, ⟨row_118, good_118, entry_good_118⟩, ⟨row_119, good_119, entry_good_119⟩, trivial⟩
