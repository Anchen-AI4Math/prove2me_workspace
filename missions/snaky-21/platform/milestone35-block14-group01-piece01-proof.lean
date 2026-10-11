import Definitions.Def_Snaky35Cache14
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block10_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block13_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block14_group00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block14_group01_piece00_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_22 (j : ℕ) (hj : j < 20) : entryAt (446 + j) = tableChunk_22[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_4 : rowAt 4 = data_4 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.1).1
theorem row_28 : rowAt 28 = data_28 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_55 : rowAt 55 = data_55 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_63 : rowAt 63 = data_63 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_64 : rowAt 64 = data_64 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.1).1
theorem row_65 : rowAt 65 = data_65 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.2.1).1
theorem row_76 : rowAt 76 = data_76 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_86 : rowAt 86 = data_86 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_97 : rowAt 97 = data_97 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.1).1
theorem row_130 : rowAt 130 = data_130 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.1).1
theorem row_170 : rowAt 170 = data_170 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_173 : rowAt 173 = data_173 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_177 : rowAt 177 = data_177 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_183 : rowAt 183 = data_183 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_220 : rowAt 220 = data_220 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_246 : rowAt 246 = data_246 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_263 : rowAt 263 = data_263 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.1).1
theorem row_282 : rowAt 282 = data_282 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_295 : rowAt 295 = data_295 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.1).1
theorem row_308 : rowAt 308 = data_308 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_328 : rowAt 328 = data_328 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.2.2.2.2.2.2.2.1).1
theorem row_447 : rowAt 447 = data_447 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_448 : rowAt 448 = data_448 := (OAI.SnakyCertificate.MilestoneChecks.block14_group00_correct.1).1
theorem row_450 : rowAt 450 = data_450 := (OAI.SnakyCertificate.MilestoneChecks.block14_group00_correct.2.2.1).1
theorem row_452 : rowAt 452 = data_452 := (OAI.SnakyCertificate.MilestoneChecks.block14_group00_correct.2.2.2.2.1).1
theorem row_454 : rowAt 454 = data_454 := (OAI.SnakyCertificate.MilestoneChecks.block14_group00_correct.2.2.2.2.2.2.1).1
theorem row_458 : rowAt 458 = data_458 := (OAI.SnakyCertificate.MilestoneChecks.block14_group01_piece00_correct.2.2.1).1
theorem entry_460_checked : entryAt 460 = entry_460 := by
  rw [entry_chunk_22 14 (by decide)]
  decide +kernel
theorem row_460 : rowAt 460 = data_460 := by
  rw [rowAt, dif_neg (by decide : ¬ 460 < 6), entry_460_checked]
  change forkRow [placeRow ⟨183, 6, 1, 4⟩ (rowAt 183), placeRow ⟨173, 2, 5, 4⟩ (rowAt 173), placeRow ⟨295, 0, 5, 4⟩ (rowAt 295), placeRow ⟨282, 4, 1, 4⟩ (rowAt 282), placeRow ⟨246, 2, 5, 4⟩ (rowAt 246), placeRow ⟨263, 2, 5, 4⟩ (rowAt 263), placeRow ⟨220, 2, 5, 4⟩ (rowAt 220)] = data_460
  rw [row_183, row_173, row_295, row_282, row_246, row_263, row_220]
  apply row_ext <;> decide +kernel
theorem entry_good_460 : EntryGood 460 := by
  unfold EntryGood
  rw [entry_460_checked]
  decide +kernel
theorem good_460 : Good (rowAt 460) := by
  rw [row_460]
  unfold Good
  decide +kernel

theorem entry_461_checked : entryAt 461 = entry_461 := by
  rw [entry_chunk_22 15 (by decide)]
  decide +kernel
theorem row_461 : rowAt 461 = data_461 := by
  rw [rowAt, dif_neg (by decide : ¬ 461 < 6), entry_461_checked]
  change forkRow [placeRow ⟨4, 1, 4, 3⟩ (rowAt 4), placeRow ⟨458, 0, 6, 4⟩ (rowAt 458)] = data_461
  rw [row_4, row_458]
  apply row_ext <;> decide +kernel
theorem entry_good_461 : EntryGood 461 := by
  unfold EntryGood
  rw [entry_461_checked]
  decide +kernel
theorem good_461 : Good (rowAt 461) := by
  rw [row_461]
  unfold Good
  decide +kernel

theorem entry_462_checked : entryAt 462 = entry_462 := by
  rw [entry_chunk_22 16 (by decide)]
  decide +kernel
theorem row_462 : rowAt 462 = data_462 := by
  rw [rowAt, dif_neg (by decide : ¬ 462 < 6), entry_462_checked]
  change forkRow [placeRow ⟨452, 0, 3, 2⟩ (rowAt 452), placeRow ⟨86, 0, 5, 4⟩ (rowAt 86), placeRow ⟨328, 1, 5, 4⟩ (rowAt 328)] = data_462
  rw [row_452, row_86, row_328]
  apply row_ext <;> decide +kernel
theorem entry_good_462 : EntryGood 462 := by
  unfold EntryGood
  rw [entry_462_checked]
  decide +kernel
theorem good_462 : Good (rowAt 462) := by
  rw [row_462]
  unfold Good
  decide +kernel

theorem entry_463_checked : entryAt 463 = entry_463 := by
  rw [entry_chunk_22 17 (by decide)]
  decide +kernel
theorem row_463 : rowAt 463 = data_463 := by
  rw [rowAt, dif_neg (by decide : ¬ 463 < 6), entry_463_checked]
  change forkRow [placeRow ⟨170, 0, 6, 3⟩ (rowAt 170), placeRow ⟨76, 1, 3, 2⟩ (rowAt 76), placeRow ⟨447, 0, 5, 4⟩ (rowAt 447)] = data_463
  rw [row_170, row_76, row_447]
  apply row_ext <;> decide +kernel
theorem entry_good_463 : EntryGood 463 := by
  unfold EntryGood
  rw [entry_463_checked]
  decide +kernel
theorem good_463 : Good (rowAt 463) := by
  rw [row_463]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 460 = data_460 ∧ Good (rowAt 460) ∧ EntryGood 460) ∧ (rowAt 461 = data_461 ∧ Good (rowAt 461) ∧ EntryGood 461) ∧ (rowAt 462 = data_462 ∧ Good (rowAt 462) ∧ EntryGood 462) ∧ (rowAt 463 = data_463 ∧ Good (rowAt 463) ∧ EntryGood 463) ∧ True := by
  exact ⟨⟨row_460, good_460, entry_good_460⟩, ⟨row_461, good_461, entry_good_461⟩, ⟨row_462, good_462, entry_good_462⟩, ⟨row_463, good_463, entry_good_463⟩, trivial⟩
