import Definitions.Def_Snaky35Cache07
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_group00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_group01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_12 (j : ℕ) (hj : j < 20) : entryAt (246 + j) = tableChunk_12[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_0 : rowAt 0 = data_0 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_7 : rowAt 7 = data_7 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.1).1
theorem row_29 : rowAt 29 = data_29 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_63 : rowAt 63 = data_63 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_64 : rowAt 64 = data_64 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.1).1
theorem row_69 : rowAt 69 = data_69 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.2.2.2.2.2.1).1
theorem row_96 : rowAt 96 = data_96 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.1).1
theorem row_108 : rowAt 108 = data_108 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_111 : rowAt 111 = data_111 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_143 : rowAt 143 = data_143 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_144 : rowAt 144 = data_144 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_154 : rowAt 154 = data_154 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_155 : rowAt 155 = data_155 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_175 : rowAt 175 = data_175 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_177 : rowAt 177 = data_177 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_186 : rowAt 186 = data_186 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_205 : rowAt 205 = data_205 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_225 : rowAt 225 = data_225 := (OAI.SnakyCertificate.MilestoneChecks.block07_group00_correct.2.1).1
theorem row_238 : rowAt 238 = data_238 := (OAI.SnakyCertificate.MilestoneChecks.block07_group01_correct.2.2.2.2.2.2.1).1
theorem row_239 : rowAt 239 = data_239 := (OAI.SnakyCertificate.MilestoneChecks.block07_group01_correct.2.2.2.2.2.2.2.1).1
theorem entry_252_checked : entryAt 252 = entry_252 := by
  rw [entry_chunk_12 6 (by decide)]
  decide +kernel
theorem row_252 : rowAt 252 = data_252 := by
  rw [rowAt, dif_neg (by decide : ¬ 252 < 6), entry_252_checked]
  change forkRow [placeRow ⟨111, 3, 4, 3⟩ (rowAt 111), placeRow ⟨154, 6, 5, 4⟩ (rowAt 154), placeRow ⟨144, 2, 5, 4⟩ (rowAt 144), placeRow ⟨63, 1, 5, 3⟩ (rowAt 63), placeRow ⟨155, 1, 5, 4⟩ (rowAt 155)] = data_252
  rw [row_111, row_154, row_144, row_63, row_155]
  apply row_ext <;> decide +kernel
theorem entry_good_252 : EntryGood 252 := by
  unfold EntryGood
  rw [entry_252_checked]
  decide +kernel
theorem good_252 : Good (rowAt 252) := by
  rw [row_252]
  unfold Good
  decide +kernel

theorem entry_253_checked : entryAt 253 = entry_253 := by
  rw [entry_chunk_12 7 (by decide)]
  decide +kernel
theorem row_253 : rowAt 253 = data_253 := by
  rw [rowAt, dif_neg (by decide : ¬ 253 < 6), entry_253_checked]
  change forkRow [placeRow ⟨29, 3, 3, 0⟩ (rowAt 29), placeRow ⟨177, 1, 6, 2⟩ (rowAt 177)] = data_253
  rw [row_29, row_177]
  apply row_ext <;> decide +kernel
theorem entry_good_253 : EntryGood 253 := by
  unfold EntryGood
  rw [entry_253_checked]
  decide +kernel
theorem good_253 : Good (rowAt 253) := by
  rw [row_253]
  unfold Good
  decide +kernel

theorem entry_254_checked : entryAt 254 = entry_254 := by
  rw [entry_chunk_12 8 (by decide)]
  decide +kernel
theorem row_254 : rowAt 254 = data_254 := by
  rw [rowAt, dif_neg (by decide : ¬ 254 < 6), entry_254_checked]
  change forkRow [placeRow ⟨96, 7, 4, 5⟩ (rowAt 96), placeRow ⟨108, 0, 8, 5⟩ (rowAt 108)] = data_254
  rw [row_96, row_108]
  apply row_ext <;> decide +kernel
theorem entry_good_254 : EntryGood 254 := by
  unfold EntryGood
  rw [entry_254_checked]
  decide +kernel
theorem good_254 : Good (rowAt 254) := by
  rw [row_254]
  unfold Good
  decide +kernel

theorem entry_255_checked : entryAt 255 = entry_255 := by
  rw [entry_chunk_12 9 (by decide)]
  decide +kernel
theorem row_255 : rowAt 255 = data_255 := by
  rw [rowAt, dif_neg (by decide : ¬ 255 < 6), entry_255_checked]
  change forkRow [placeRow ⟨69, 0, 3, 3⟩ (rowAt 69), placeRow ⟨205, 0, 5, 5⟩ (rowAt 205), placeRow ⟨7, 3, 3, 4⟩ (rowAt 7)] = data_255
  rw [row_69, row_205, row_7]
  apply row_ext <;> decide +kernel
theorem entry_good_255 : EntryGood 255 := by
  unfold EntryGood
  rw [entry_255_checked]
  decide +kernel
theorem good_255 : Good (rowAt 255) := by
  rw [row_255]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 252 = data_252 ∧ Good (rowAt 252) ∧ EntryGood 252) ∧ (rowAt 253 = data_253 ∧ Good (rowAt 253) ∧ EntryGood 253) ∧ (rowAt 254 = data_254 ∧ Good (rowAt 254) ∧ EntryGood 254) ∧ (rowAt 255 = data_255 ∧ Good (rowAt 255) ∧ EntryGood 255) ∧ True := by
  exact ⟨⟨row_252, good_252, entry_good_252⟩, ⟨row_253, good_253, entry_good_253⟩, ⟨row_254, good_254, entry_good_254⟩, ⟨row_255, good_255, entry_good_255⟩, trivial⟩
