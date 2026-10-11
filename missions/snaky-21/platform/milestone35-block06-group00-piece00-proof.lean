import Definitions.Def_Snaky35Cache06
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_9 (j : ℕ) (hj : j < 20) : entryAt (186 + j) = tableChunk_9[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_0 : rowAt 0 = data_0 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_7 : rowAt 7 = data_7 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.1).1
theorem row_55 : rowAt 55 = data_55 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_63 : rowAt 63 = data_63 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_64 : rowAt 64 = data_64 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.1).1
theorem row_84 : rowAt 84 = data_84 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_103 : rowAt 103 = data_103 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.1).1
theorem row_131 : rowAt 131 = data_131 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.1).1
theorem row_146 : rowAt 146 = data_146 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_162 : rowAt 162 = data_162 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.1).1
theorem row_187 : rowAt 187 = data_187 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem entry_192_checked : entryAt 192 = entry_192 := by
  rw [entry_chunk_9 6 (by decide)]
  decide +kernel
theorem row_192 : rowAt 192 = data_192 := by
  rw [rowAt, dif_neg (by decide : ¬ 192 < 6), entry_192_checked]
  change forkRow [placeRow ⟨64, 1, 3, 1⟩ (rowAt 64), placeRow ⟨103, 0, 3, 4⟩ (rowAt 103), placeRow ⟨55, 3, 4, 5⟩ (rowAt 55)] = data_192
  rw [row_64, row_103, row_55]
  apply row_ext <;> decide +kernel
theorem entry_good_192 : EntryGood 192 := by
  unfold EntryGood
  rw [entry_192_checked]
  decide +kernel
theorem good_192 : Good (rowAt 192) := by
  rw [row_192]
  unfold Good
  decide +kernel

theorem entry_193_checked : entryAt 193 = entry_193 := by
  rw [entry_chunk_9 7 (by decide)]
  decide +kernel
theorem row_193 : rowAt 193 = data_193 := by
  rw [rowAt, dif_neg (by decide : ¬ 193 < 6), entry_193_checked]
  change forkRow [placeRow ⟨6, 6, 2, 3⟩ (rowAt 6), placeRow ⟨162, 1, 7, 4⟩ (rowAt 162)] = data_193
  rw [row_6, row_162]
  apply row_ext <;> decide +kernel
theorem entry_good_193 : EntryGood 193 := by
  unfold EntryGood
  rw [entry_193_checked]
  decide +kernel
theorem good_193 : Good (rowAt 193) := by
  rw [row_193]
  unfold Good
  decide +kernel

theorem entry_194_checked : entryAt 194 = entry_194 := by
  rw [entry_chunk_9 8 (by decide)]
  decide +kernel
theorem row_194 : rowAt 194 = data_194 := by
  rw [rowAt, dif_neg (by decide : ¬ 194 < 6), entry_194_checked]
  change forkRow [placeRow ⟨0, 0, 0, 3⟩ (rowAt 0), placeRow ⟨146, 4, 2, 5⟩ (rowAt 146)] = data_194
  rw [row_0, row_146]
  apply row_ext <;> decide +kernel
theorem entry_good_194 : EntryGood 194 := by
  unfold EntryGood
  rw [entry_194_checked]
  decide +kernel
theorem good_194 : Good (rowAt 194) := by
  rw [row_194]
  unfold Good
  decide +kernel

theorem entry_195_checked : entryAt 195 = entry_195 := by
  rw [entry_chunk_9 9 (by decide)]
  decide +kernel
theorem row_195 : rowAt 195 = data_195 := by
  rw [rowAt, dif_neg (by decide : ¬ 195 < 6), entry_195_checked]
  change forkRow [placeRow ⟨6, 6, 0, 3⟩ (rowAt 6), placeRow ⟨162, 1, 5, 4⟩ (rowAt 162)] = data_195
  rw [row_6, row_162]
  apply row_ext <;> decide +kernel
theorem entry_good_195 : EntryGood 195 := by
  unfold EntryGood
  rw [entry_195_checked]
  decide +kernel
theorem good_195 : Good (rowAt 195) := by
  rw [row_195]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 192 = data_192 ∧ Good (rowAt 192) ∧ EntryGood 192) ∧ (rowAt 193 = data_193 ∧ Good (rowAt 193) ∧ EntryGood 193) ∧ (rowAt 194 = data_194 ∧ Good (rowAt 194) ∧ EntryGood 194) ∧ (rowAt 195 = data_195 ∧ Good (rowAt 195) ∧ EntryGood 195) ∧ True := by
  exact ⟨⟨row_192, good_192, entry_good_192⟩, ⟨row_193, good_193, entry_good_193⟩, ⟨row_194, good_194, entry_good_194⟩, ⟨row_195, good_195, entry_good_195⟩, trivial⟩
