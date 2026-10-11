import Definitions.Def_Snaky35Cache07
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_group00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_group01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_11 (j : ℕ) (hj : j < 20) : entryAt (226 + j) = tableChunk_11[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem entry_chunk_12 (j : ℕ) (hj : j < 20) : entryAt (246 + j) = tableChunk_12[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_11 : rowAt 11 = data_11 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_61 : rowAt 61 = data_61 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_64 : rowAt 64 = data_64 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.1).1
theorem row_99 : rowAt 99 = data_99 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.1).1
theorem row_131 : rowAt 131 = data_131 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.1).1
theorem row_143 : rowAt 143 = data_143 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_159 : rowAt 159 = data_159 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_173 : rowAt 173 = data_173 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_175 : rowAt 175 = data_175 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_186 : rowAt 186 = data_186 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_190 : rowAt 190 = data_190 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_229 : rowAt 229 = data_229 := (OAI.SnakyCertificate.MilestoneChecks.block07_group00_correct.2.2.2.2.2.1).1
theorem row_233 : rowAt 233 = data_233 := (OAI.SnakyCertificate.MilestoneChecks.block07_group01_correct.2.1).1
theorem row_237 : rowAt 237 = data_237 := (OAI.SnakyCertificate.MilestoneChecks.block07_group01_correct.2.2.2.2.2.1).1
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


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 240 = data_240 ∧ Good (rowAt 240) ∧ EntryGood 240) ∧ (rowAt 241 = data_241 ∧ Good (rowAt 241) ∧ EntryGood 241) ∧ (rowAt 242 = data_242 ∧ Good (rowAt 242) ∧ EntryGood 242) ∧ (rowAt 243 = data_243 ∧ Good (rowAt 243) ∧ EntryGood 243) ∧ True := by
  exact ⟨⟨row_240, good_240, entry_good_240⟩, ⟨row_241, good_241, entry_good_241⟩, ⟨row_242, good_242, entry_good_242⟩, ⟨row_243, good_243, entry_good_243⟩, trivial⟩
