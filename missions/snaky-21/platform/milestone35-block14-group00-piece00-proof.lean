import Definitions.Def_Snaky35Cache14
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block11_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block12_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block13_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_22 (j : ℕ) (hj : j < 20) : entryAt (446 + j) = tableChunk_22[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_1 : rowAt 1 = data_1 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_9 : rowAt 9 = data_9 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.1).1
theorem row_20 : rowAt 20 = data_20 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_24 : rowAt 24 = data_24 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_25 : rowAt 25 = data_25 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_26 : rowAt 26 = data_26 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_39 : rowAt 39 = data_39 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.1).1
theorem row_58 : rowAt 58 = data_58 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_118 : rowAt 118 = data_118 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_226 : rowAt 226 = data_226 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.1).1
theorem row_244 : rowAt 244 = data_244 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_307 : rowAt 307 = data_307 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_359 : rowAt 359 = data_359 := (OAI.SnakyCertificate.MilestoneChecks.block11_correct.2.2.2.2.2.2.2.1).1
theorem row_386 : rowAt 386 = data_386 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.1).1
theorem row_389 : rowAt 389 = data_389 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.2.2.2.1).1
theorem row_414 : rowAt 414 = data_414 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_436 : rowAt 436 = data_436 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_439 : rowAt 439 = data_439 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_440 : rowAt 440 = data_440 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem entry_448_checked : entryAt 448 = entry_448 := by
  rw [entry_chunk_22 2 (by decide)]
  decide +kernel
theorem row_448 : rowAt 448 = data_448 := by
  rw [rowAt, dif_neg (by decide : ¬ 448 < 6), entry_448_checked]
  change forkRow [placeRow ⟨9, 4, 1, 3⟩ (rowAt 9), placeRow ⟨436, 0, 3, 6⟩ (rowAt 436)] = data_448
  rw [row_9, row_436]
  apply row_ext <;> decide +kernel
theorem entry_good_448 : EntryGood 448 := by
  unfold EntryGood
  rw [entry_448_checked]
  decide +kernel
theorem good_448 : Good (rowAt 448) := by
  rw [row_448]
  unfold Good
  decide +kernel

theorem entry_449_checked : entryAt 449 = entry_449 := by
  rw [entry_chunk_22 3 (by decide)]
  decide +kernel
theorem row_449 : rowAt 449 = data_449 := by
  rw [rowAt, dif_neg (by decide : ¬ 449 < 6), entry_449_checked]
  change forkRow [placeRow ⟨26, 3, 4, 3⟩ (rowAt 26), placeRow ⟨244, 0, 5, 4⟩ (rowAt 244), placeRow ⟨439, 0, 5, 4⟩ (rowAt 439), placeRow ⟨307, 0, 4, 3⟩ (rowAt 307)] = data_449
  rw [row_26, row_244, row_439, row_307]
  apply row_ext <;> decide +kernel
theorem entry_good_449 : EntryGood 449 := by
  unfold EntryGood
  rw [entry_449_checked]
  decide +kernel
theorem good_449 : Good (rowAt 449) := by
  rw [row_449]
  unfold Good
  decide +kernel

theorem entry_450_checked : entryAt 450 = entry_450 := by
  rw [entry_chunk_22 4 (by decide)]
  decide +kernel
theorem row_450 : rowAt 450 = data_450 := by
  rw [rowAt, dif_neg (by decide : ¬ 450 < 6), entry_450_checked]
  change forkRow [placeRow ⟨6, 1, 5, 5⟩ (rowAt 6), placeRow ⟨440, 0, 6, 4⟩ (rowAt 440)] = data_450
  rw [row_6, row_440]
  apply row_ext <;> decide +kernel
theorem entry_good_450 : EntryGood 450 := by
  unfold EntryGood
  rw [entry_450_checked]
  decide +kernel
theorem good_450 : Good (rowAt 450) := by
  rw [row_450]
  unfold Good
  decide +kernel

theorem entry_451_checked : entryAt 451 = entry_451 := by
  rw [entry_chunk_22 5 (by decide)]
  decide +kernel
theorem row_451 : rowAt 451 = data_451 := by
  rw [rowAt, dif_neg (by decide : ¬ 451 < 6), entry_451_checked]
  change forkRow [placeRow ⟨1, 5, 4, 3⟩ (rowAt 1), placeRow ⟨449, 0, 5, 4⟩ (rowAt 449)] = data_451
  rw [row_1, row_449]
  apply row_ext <;> decide +kernel
theorem entry_good_451 : EntryGood 451 := by
  unfold EntryGood
  rw [entry_451_checked]
  decide +kernel
theorem good_451 : Good (rowAt 451) := by
  rw [row_451]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 448 = data_448 ∧ Good (rowAt 448) ∧ EntryGood 448) ∧ (rowAt 449 = data_449 ∧ Good (rowAt 449) ∧ EntryGood 449) ∧ (rowAt 450 = data_450 ∧ Good (rowAt 450) ∧ EntryGood 450) ∧ (rowAt 451 = data_451 ∧ Good (rowAt 451) ∧ EntryGood 451) ∧ True := by
  exact ⟨⟨row_448, good_448, entry_good_448⟩, ⟨row_449, good_449, entry_good_449⟩, ⟨row_450, good_450, entry_good_450⟩, ⟨row_451, good_451, entry_good_451⟩, trivial⟩
