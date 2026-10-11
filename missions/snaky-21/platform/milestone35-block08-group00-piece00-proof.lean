import Definitions.Def_Snaky35Cache08
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_12 (j : ℕ) (hj : j < 20) : entryAt (246 + j) = tableChunk_12[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_0 : rowAt 0 = data_0 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.1).1
theorem row_4 : rowAt 4 = data_4 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_55 : rowAt 55 = data_55 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_143 : rowAt 143 = data_143 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_144 : rowAt 144 = data_144 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_175 : rowAt 175 = data_175 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_213 : rowAt 213 = data_213 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_227 : rowAt 227 = data_227 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.1).1
theorem row_231 : rowAt 231 = data_231 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.1).1
theorem row_235 : rowAt 235 = data_235 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_242 : rowAt 242 = data_242 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem entry_256_checked : entryAt 256 = entry_256 := by
  rw [entry_chunk_12 10 (by decide)]
  decide +kernel
theorem row_256 : rowAt 256 = data_256 := by
  rw [rowAt, dif_neg (by decide : ¬ 256 < 6), entry_256_checked]
  change forkRow [placeRow ⟨0, 5, 4, 5⟩ (rowAt 0), placeRow ⟨231, 0, 3, 4⟩ (rowAt 231)] = data_256
  rw [row_0, row_231]
  apply row_ext <;> decide +kernel
theorem entry_good_256 : EntryGood 256 := by
  unfold EntryGood
  rw [entry_256_checked]
  decide +kernel
theorem good_256 : Good (rowAt 256) := by
  rw [row_256]
  unfold Good
  decide +kernel

theorem entry_257_checked : entryAt 257 = entry_257 := by
  rw [entry_chunk_12 11 (by decide)]
  decide +kernel
theorem row_257 : rowAt 257 = data_257 := by
  rw [rowAt, dif_neg (by decide : ¬ 257 < 6), entry_257_checked]
  change forkRow [placeRow ⟨4, 1, 5, 4⟩ (rowAt 4), placeRow ⟨235, 0, 4, 5⟩ (rowAt 235)] = data_257
  rw [row_4, row_235]
  apply row_ext <;> decide +kernel
theorem entry_good_257 : EntryGood 257 := by
  unfold EntryGood
  rw [entry_257_checked]
  decide +kernel
theorem good_257 : Good (rowAt 257) := by
  rw [row_257]
  unfold Good
  decide +kernel

theorem entry_258_checked : entryAt 258 = entry_258 := by
  rw [entry_chunk_12 12 (by decide)]
  decide +kernel
theorem row_258 : rowAt 258 = data_258 := by
  rw [rowAt, dif_neg (by decide : ¬ 258 < 6), entry_258_checked]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (rowAt 6), placeRow ⟨227, 0, 4, 5⟩ (rowAt 227)] = data_258
  rw [row_6, row_227]
  apply row_ext <;> decide +kernel
theorem entry_good_258 : EntryGood 258 := by
  unfold EntryGood
  rw [entry_258_checked]
  decide +kernel
theorem good_258 : Good (rowAt 258) := by
  rw [row_258]
  unfold Good
  decide +kernel

theorem entry_259_checked : entryAt 259 = entry_259 := by
  rw [entry_chunk_12 13 (by decide)]
  decide +kernel
theorem row_259 : rowAt 259 = data_259 := by
  rw [rowAt, dif_neg (by decide : ¬ 259 < 6), entry_259_checked]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (rowAt 6), placeRow ⟨231, 1, 7, 2⟩ (rowAt 231)] = data_259
  rw [row_6, row_231]
  apply row_ext <;> decide +kernel
theorem entry_good_259 : EntryGood 259 := by
  unfold EntryGood
  rw [entry_259_checked]
  decide +kernel
theorem good_259 : Good (rowAt 259) := by
  rw [row_259]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 256 = data_256 ∧ Good (rowAt 256) ∧ EntryGood 256) ∧ (rowAt 257 = data_257 ∧ Good (rowAt 257) ∧ EntryGood 257) ∧ (rowAt 258 = data_258 ∧ Good (rowAt 258) ∧ EntryGood 258) ∧ (rowAt 259 = data_259 ∧ Good (rowAt 259) ∧ EntryGood 259) ∧ True := by
  exact ⟨⟨row_256, good_256, entry_good_256⟩, ⟨row_257, good_257, entry_good_257⟩, ⟨row_258, good_258, entry_good_258⟩, ⟨row_259, good_259, entry_good_259⟩, trivial⟩
