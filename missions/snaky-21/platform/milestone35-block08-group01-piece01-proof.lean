import Definitions.Def_Snaky35Cache08
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
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
theorem entry_chunk_13 (j : ℕ) (hj : j < 20) : entryAt (266 + j) = tableChunk_13[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_28 : rowAt 28 = data_28 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_55 : rowAt 55 = data_55 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_63 : rowAt 63 = data_63 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_107 : rowAt 107 = data_107 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_143 : rowAt 143 = data_143 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_144 : rowAt 144 = data_144 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_175 : rowAt 175 = data_175 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_202 : rowAt 202 = data_202 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_242 : rowAt 242 = data_242 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_247 : rowAt 247 = data_247 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_250 : rowAt 250 = data_250 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_251 : rowAt 251 = data_251 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem entry_268_checked : entryAt 268 = entry_268 := by
  rw [entry_chunk_13 2 (by decide)]
  decide +kernel
theorem row_268 : rowAt 268 = data_268 := by
  rw [rowAt, dif_neg (by decide : ¬ 268 < 6), entry_268_checked]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (rowAt 6), placeRow ⟨251, 0, 4, 2⟩ (rowAt 251)] = data_268
  rw [row_6, row_251]
  apply row_ext <;> decide +kernel
theorem entry_good_268 : EntryGood 268 := by
  unfold EntryGood
  rw [entry_268_checked]
  decide +kernel
theorem good_268 : Good (rowAt 268) := by
  rw [row_268]
  unfold Good
  decide +kernel

theorem entry_269_checked : entryAt 269 = entry_269 := by
  rw [entry_chunk_13 3 (by decide)]
  decide +kernel
theorem row_269 : rowAt 269 = data_269 := by
  rw [rowAt, dif_neg (by decide : ¬ 269 < 6), entry_269_checked]
  change forkRow [placeRow ⟨28, 3, 3, 6⟩ (rowAt 28), placeRow ⟨202, 0, 7, 5⟩ (rowAt 202)] = data_269
  rw [row_28, row_202]
  apply row_ext <;> decide +kernel
theorem entry_good_269 : EntryGood 269 := by
  unfold EntryGood
  rw [entry_269_checked]
  decide +kernel
theorem good_269 : Good (rowAt 269) := by
  rw [row_269]
  unfold Good
  decide +kernel

theorem entry_270_checked : entryAt 270 = entry_270 := by
  rw [entry_chunk_13 4 (by decide)]
  decide +kernel
theorem row_270 : rowAt 270 = data_270 := by
  rw [rowAt, dif_neg (by decide : ¬ 270 < 6), entry_270_checked]
  change forkRow [placeRow ⟨63, 0, 3, 7⟩ (rowAt 63), placeRow ⟨6, 7, 3, 2⟩ (rowAt 6)] = data_270
  rw [row_63, row_6]
  apply row_ext <;> decide +kernel
theorem entry_good_270 : EntryGood 270 := by
  unfold EntryGood
  rw [entry_270_checked]
  decide +kernel
theorem good_270 : Good (rowAt 270) := by
  rw [row_270]
  unfold Good
  decide +kernel

theorem entry_271_checked : entryAt 271 = entry_271 := by
  rw [entry_chunk_13 5 (by decide)]
  decide +kernel
theorem row_271 : rowAt 271 = data_271 := by
  rw [rowAt, dif_neg (by decide : ¬ 271 < 6), entry_271_checked]
  change forkRow [placeRow ⟨107, 2, 7, 3⟩ (rowAt 107), placeRow ⟨107, 3, 4, 6⟩ (rowAt 107)] = data_271
  rw [row_107]
  apply row_ext <;> decide +kernel
theorem entry_good_271 : EntryGood 271 := by
  unfold EntryGood
  rw [entry_271_checked]
  decide +kernel
theorem good_271 : Good (rowAt 271) := by
  rw [row_271]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 268 = data_268 ∧ Good (rowAt 268) ∧ EntryGood 268) ∧ (rowAt 269 = data_269 ∧ Good (rowAt 269) ∧ EntryGood 269) ∧ (rowAt 270 = data_270 ∧ Good (rowAt 270) ∧ EntryGood 270) ∧ (rowAt 271 = data_271 ∧ Good (rowAt 271) ∧ EntryGood 271) ∧ True := by
  exact ⟨⟨row_268, good_268, entry_good_268⟩, ⟨row_269, good_269, entry_good_269⟩, ⟨row_270, good_270, entry_good_270⟩, ⟨row_271, good_271, entry_good_271⟩, trivial⟩
