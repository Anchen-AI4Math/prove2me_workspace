import Definitions.Def_Snaky35Cache09
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_group00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_group01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_14 (j : ℕ) (hj : j < 20) : entryAt (286 + j) = tableChunk_14[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem entry_chunk_15 (j : ℕ) (hj : j < 20) : entryAt (306 + j) = tableChunk_15[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_0 : rowAt 0 = data_0 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.1).1
theorem row_4 : rowAt 4 = data_4 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_28 : rowAt 28 = data_28 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_55 : rowAt 55 = data_55 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_131 : rowAt 131 = data_131 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.1).1
theorem row_202 : rowAt 202 = data_202 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_268 : rowAt 268 = data_268 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_273 : rowAt 273 = data_273 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_278 : rowAt 278 = data_278 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_281 : rowAt 281 = data_281 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_288 : rowAt 288 = data_288 := (OAI.SnakyCertificate.MilestoneChecks.block09_group00_correct.1).1
theorem row_299 : rowAt 299 = data_299 := (OAI.SnakyCertificate.MilestoneChecks.block09_group01_correct.2.2.2.1).1
theorem entry_308_checked : entryAt 308 = entry_308 := by
  rw [entry_chunk_15 2 (by decide)]
  decide +kernel
theorem row_308 : rowAt 308 = data_308 := by
  rw [rowAt, dif_neg (by decide : ¬ 308 < 6), entry_308_checked]
  change forkRow [placeRow ⟨6, 6, 3, 4⟩ (rowAt 6), placeRow ⟨299, 0, 4, 6⟩ (rowAt 299)] = data_308
  rw [row_6, row_299]
  apply row_ext <;> decide +kernel
theorem entry_good_308 : EntryGood 308 := by
  unfold EntryGood
  rw [entry_308_checked]
  decide +kernel
theorem good_308 : Good (rowAt 308) := by
  rw [row_308]
  unfold Good
  decide +kernel

theorem entry_309_checked : entryAt 309 = entry_309 := by
  rw [entry_chunk_15 3 (by decide)]
  decide +kernel
theorem row_309 : rowAt 309 = data_309 := by
  rw [rowAt, dif_neg (by decide : ¬ 309 < 6), entry_309_checked]
  change forkRow [placeRow ⟨28, 6, 3, 4⟩ (rowAt 28), placeRow ⟨268, 1, 5, 7⟩ (rowAt 268)] = data_309
  rw [row_28, row_268]
  apply row_ext <;> decide +kernel
theorem entry_good_309 : EntryGood 309 := by
  unfold EntryGood
  rw [entry_309_checked]
  decide +kernel
theorem good_309 : Good (rowAt 309) := by
  rw [row_309]
  unfold Good
  decide +kernel

theorem entry_310_checked : entryAt 310 = entry_310 := by
  rw [entry_chunk_15 4 (by decide)]
  decide +kernel
theorem row_310 : rowAt 310 = data_310 := by
  rw [rowAt, dif_neg (by decide : ¬ 310 < 6), entry_310_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨281, 0, 5, 3⟩ (rowAt 281)] = data_310
  rw [row_6, row_281]
  apply row_ext <;> decide +kernel
theorem entry_good_310 : EntryGood 310 := by
  unfold EntryGood
  rw [entry_310_checked]
  decide +kernel
theorem good_310 : Good (rowAt 310) := by
  rw [row_310]
  unfold Good
  decide +kernel

theorem entry_311_checked : entryAt 311 = entry_311 := by
  rw [entry_chunk_15 5 (by decide)]
  decide +kernel
theorem row_311 : rowAt 311 = data_311 := by
  rw [rowAt, dif_neg (by decide : ¬ 311 < 6), entry_311_checked]
  change forkRow [placeRow ⟨6, 3, 3, 5⟩ (rowAt 6), placeRow ⟨278, 0, 2, 4⟩ (rowAt 278)] = data_311
  rw [row_6, row_278]
  apply row_ext <;> decide +kernel
theorem entry_good_311 : EntryGood 311 := by
  unfold EntryGood
  rw [entry_311_checked]
  decide +kernel
theorem good_311 : Good (rowAt 311) := by
  rw [row_311]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 308 = data_308 ∧ Good (rowAt 308) ∧ EntryGood 308) ∧ (rowAt 309 = data_309 ∧ Good (rowAt 309) ∧ EntryGood 309) ∧ (rowAt 310 = data_310 ∧ Good (rowAt 310) ∧ EntryGood 310) ∧ (rowAt 311 = data_311 ∧ Good (rowAt 311) ∧ EntryGood 311) ∧ True := by
  exact ⟨⟨row_308, good_308, entry_good_308⟩, ⟨row_309, good_309, entry_good_309⟩, ⟨row_310, good_310, entry_good_310⟩, ⟨row_311, good_311, entry_good_311⟩, trivial⟩
