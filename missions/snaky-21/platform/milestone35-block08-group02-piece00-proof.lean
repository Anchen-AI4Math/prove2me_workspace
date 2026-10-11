import Definitions.Def_Snaky35Cache08
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_13 (j : ℕ) (hj : j < 20) : entryAt (266 + j) = tableChunk_13[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_1 : rowAt 1 = data_1 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_7 : rowAt 7 = data_7 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.1).1
theorem row_14 : rowAt 14 = data_14 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_33 : rowAt 33 = data_33 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.1).1
theorem row_44 : rowAt 44 = data_44 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_63 : rowAt 63 = data_63 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_162 : rowAt 162 = data_162 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.1).1
theorem row_177 : rowAt 177 = data_177 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_198 : rowAt 198 = data_198 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.1).1
theorem row_204 : rowAt 204 = data_204 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_223 : rowAt 223 = data_223 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_234 : rowAt 234 = data_234 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_240 : rowAt 240 = data_240 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_249 : rowAt 249 = data_249 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem entry_272_checked : entryAt 272 = entry_272 := by
  rw [entry_chunk_13 6 (by decide)]
  decide +kernel
theorem row_272 : rowAt 272 = data_272 := by
  rw [rowAt, dif_neg (by decide : ¬ 272 < 6), entry_272_checked]
  change forkRow [placeRow ⟨1, 1, 3, 1⟩ (rowAt 1), placeRow ⟨249, 0, 4, 5⟩ (rowAt 249)] = data_272
  rw [row_1, row_249]
  apply row_ext <;> decide +kernel
theorem entry_good_272 : EntryGood 272 := by
  unfold EntryGood
  rw [entry_272_checked]
  decide +kernel
theorem good_272 : Good (rowAt 272) := by
  rw [row_272]
  unfold Good
  decide +kernel

theorem entry_273_checked : entryAt 273 = entry_273 := by
  rw [entry_chunk_13 7 (by decide)]
  decide +kernel
theorem row_273 : rowAt 273 = data_273 := by
  rw [rowAt, dif_neg (by decide : ¬ 273 < 6), entry_273_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨223, 0, 5, 4⟩ (rowAt 223)] = data_273
  rw [row_6, row_223]
  apply row_ext <;> decide +kernel
theorem entry_good_273 : EntryGood 273 := by
  unfold EntryGood
  rw [entry_273_checked]
  decide +kernel
theorem good_273 : Good (rowAt 273) := by
  rw [row_273]
  unfold Good
  decide +kernel

theorem entry_274_checked : entryAt 274 = entry_274 := by
  rw [entry_chunk_13 8 (by decide)]
  decide +kernel
theorem row_274 : rowAt 274 = data_274 := by
  rw [rowAt, dif_neg (by decide : ¬ 274 < 6), entry_274_checked]
  change forkRow [placeRow ⟨6, 7, 3, 1⟩ (rowAt 6), placeRow ⟨240, 0, 5, 5⟩ (rowAt 240)] = data_274
  rw [row_6, row_240]
  apply row_ext <;> decide +kernel
theorem entry_good_274 : EntryGood 274 := by
  unfold EntryGood
  rw [entry_274_checked]
  decide +kernel
theorem good_274 : Good (rowAt 274) := by
  rw [row_274]
  unfold Good
  decide +kernel

theorem entry_275_checked : entryAt 275 = entry_275 := by
  rw [entry_chunk_13 9 (by decide)]
  decide +kernel
theorem row_275 : rowAt 275 = data_275 := by
  rw [rowAt, dif_neg (by decide : ¬ 275 < 6), entry_275_checked]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (rowAt 63), placeRow ⟨198, 4, 0, 4⟩ (rowAt 198), placeRow ⟨44, 2, 5, 4⟩ (rowAt 44)] = data_275
  rw [row_63, row_198, row_44]
  apply row_ext <;> decide +kernel
theorem entry_good_275 : EntryGood 275 := by
  unfold EntryGood
  rw [entry_275_checked]
  decide +kernel
theorem good_275 : Good (rowAt 275) := by
  rw [row_275]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 272 = data_272 ∧ Good (rowAt 272) ∧ EntryGood 272) ∧ (rowAt 273 = data_273 ∧ Good (rowAt 273) ∧ EntryGood 273) ∧ (rowAt 274 = data_274 ∧ Good (rowAt 274) ∧ EntryGood 274) ∧ (rowAt 275 = data_275 ∧ Good (rowAt 275) ∧ EntryGood 275) ∧ True := by
  exact ⟨⟨row_272, good_272, entry_good_272⟩, ⟨row_273, good_273, entry_good_273⟩, ⟨row_274, good_274, entry_good_274⟩, ⟨row_275, good_275, entry_good_275⟩, trivial⟩
