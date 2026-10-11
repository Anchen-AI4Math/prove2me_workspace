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
theorem entry_456_checked : entryAt 456 = entry_456 := by
  rw [entry_chunk_22 10 (by decide)]
  decide +kernel
theorem row_456 : rowAt 456 = data_456 := by
  rw [rowAt, dif_neg (by decide : ¬ 456 < 6), entry_456_checked]
  change forkRow [placeRow ⟨308, 4, 4, 3⟩ (rowAt 308), placeRow ⟨64, 2, 1, 5⟩ (rowAt 64), placeRow ⟨63, 1, 5, 3⟩ (rowAt 63), placeRow ⟨55, 0, 5, 4⟩ (rowAt 55)] = data_456
  rw [row_308, row_64, row_63, row_55]
  apply row_ext <;> decide +kernel
theorem entry_good_456 : EntryGood 456 := by
  unfold EntryGood
  rw [entry_456_checked]
  decide +kernel
theorem good_456 : Good (rowAt 456) := by
  rw [row_456]
  unfold Good
  decide +kernel

theorem entry_457_checked : entryAt 457 = entry_457 := by
  rw [entry_chunk_22 11 (by decide)]
  decide +kernel
theorem row_457 : rowAt 457 = data_457 := by
  rw [rowAt, dif_neg (by decide : ¬ 457 < 6), entry_457_checked]
  change forkRow [placeRow ⟨28, 7, 3, 2⟩ (rowAt 28), placeRow ⟨454, 0, 5, 4⟩ (rowAt 454)] = data_457
  rw [row_28, row_454]
  apply row_ext <;> decide +kernel
theorem entry_good_457 : EntryGood 457 := by
  unfold EntryGood
  rw [entry_457_checked]
  decide +kernel
theorem good_457 : Good (rowAt 457) := by
  rw [row_457]
  unfold Good
  decide +kernel

theorem entry_458_checked : entryAt 458 = entry_458 := by
  rw [entry_chunk_22 12 (by decide)]
  decide +kernel
theorem row_458 : rowAt 458 = data_458 := by
  rw [rowAt, dif_neg (by decide : ¬ 458 < 6), entry_458_checked]
  change forkRow [placeRow ⟨130, 1, 4, 2⟩ (rowAt 130), placeRow ⟨177, 1, 4, 2⟩ (rowAt 177), placeRow ⟨450, 0, 1, 4⟩ (rowAt 450)] = data_458
  rw [row_130, row_177, row_450]
  apply row_ext <;> decide +kernel
theorem entry_good_458 : EntryGood 458 := by
  unfold EntryGood
  rw [entry_458_checked]
  decide +kernel
theorem good_458 : Good (rowAt 458) := by
  rw [row_458]
  unfold Good
  decide +kernel

theorem entry_459_checked : entryAt 459 = entry_459 := by
  rw [entry_chunk_22 13 (by decide)]
  decide +kernel
theorem row_459 : rowAt 459 = data_459 := by
  rw [rowAt, dif_neg (by decide : ¬ 459 < 6), entry_459_checked]
  change forkRow [placeRow ⟨97, 2, 7, 3⟩ (rowAt 97), placeRow ⟨448, 0, 5, 4⟩ (rowAt 448), placeRow ⟨65, 2, 7, 3⟩ (rowAt 65)] = data_459
  rw [row_97, row_448, row_65]
  apply row_ext <;> decide +kernel
theorem entry_good_459 : EntryGood 459 := by
  unfold EntryGood
  rw [entry_459_checked]
  decide +kernel
theorem good_459 : Good (rowAt 459) := by
  rw [row_459]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 456 = data_456 ∧ Good (rowAt 456) ∧ EntryGood 456) ∧ (rowAt 457 = data_457 ∧ Good (rowAt 457) ∧ EntryGood 457) ∧ (rowAt 458 = data_458 ∧ Good (rowAt 458) ∧ EntryGood 458) ∧ (rowAt 459 = data_459 ∧ Good (rowAt 459) ∧ EntryGood 459) ∧ True := by
  exact ⟨⟨row_456, good_456, entry_good_456⟩, ⟨row_457, good_457, entry_good_457⟩, ⟨row_458, good_458, entry_good_458⟩, ⟨row_459, good_459, entry_good_459⟩, trivial⟩
