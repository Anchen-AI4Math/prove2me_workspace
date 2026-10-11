import Definitions.Def_Snaky35Cache10
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_15 (j : ℕ) (hj : j < 20) : entryAt (306 + j) = tableChunk_15[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem entry_chunk_16 (j : ℕ) (hj : j < 20) : entryAt (326 + j) = tableChunk_16[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_19 : rowAt 19 = data_19 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_24 : rowAt 24 = data_24 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_25 : rowAt 25 = data_25 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_63 : rowAt 63 = data_63 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_96 : rowAt 96 = data_96 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.1).1
theorem row_97 : rowAt 97 = data_97 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.1).1
theorem row_115 : rowAt 115 = data_115 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_165 : rowAt 165 = data_165 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.1).1
theorem row_195 : rowAt 195 = data_195 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.1).1
theorem row_205 : rowAt 205 = data_205 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_223 : rowAt 223 = data_223 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_255 : rowAt 255 = data_255 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_267 : rowAt 267 = data_267 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_278 : rowAt 278 = data_278 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_298 : rowAt 298 = data_298 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_313 : rowAt 313 = data_313 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem entry_320_checked : entryAt 320 = entry_320 := by
  rw [entry_chunk_15 14 (by decide)]
  decide +kernel
theorem row_320 : rowAt 320 = data_320 := by
  rw [rowAt, dif_neg (by decide : ¬ 320 < 6), entry_320_checked]
  change forkRow [placeRow ⟨19, 1, 4, 3⟩ (rowAt 19), placeRow ⟨267, 2, 6, 4⟩ (rowAt 267), placeRow ⟨115, 7, 4, 3⟩ (rowAt 115)] = data_320
  rw [row_19, row_267, row_115]
  apply row_ext <;> decide +kernel
theorem entry_good_320 : EntryGood 320 := by
  unfold EntryGood
  rw [entry_320_checked]
  decide +kernel
theorem good_320 : Good (rowAt 320) := by
  rw [row_320]
  unfold Good
  decide +kernel

theorem entry_321_checked : entryAt 321 = entry_321 := by
  rw [entry_chunk_15 15 (by decide)]
  decide +kernel
theorem row_321 : rowAt 321 = data_321 := by
  rw [rowAt, dif_neg (by decide : ¬ 321 < 6), entry_321_checked]
  change forkRow [placeRow ⟨165, 1, 3, 4⟩ (rowAt 165), placeRow ⟨97, 0, 7, 5⟩ (rowAt 97), placeRow ⟨223, 3, 4, 7⟩ (rowAt 223)] = data_321
  rw [row_165, row_97, row_223]
  apply row_ext <;> decide +kernel
theorem entry_good_321 : EntryGood 321 := by
  unfold EntryGood
  rw [entry_321_checked]
  decide +kernel
theorem good_321 : Good (rowAt 321) := by
  rw [row_321]
  unfold Good
  decide +kernel

theorem entry_322_checked : entryAt 322 = entry_322 := by
  rw [entry_chunk_15 16 (by decide)]
  decide +kernel
theorem row_322 : rowAt 322 = data_322 := by
  rw [rowAt, dif_neg (by decide : ¬ 322 < 6), entry_322_checked]
  change forkRow [placeRow ⟨96, 0, 1, 4⟩ (rowAt 96), placeRow ⟨205, 1, 5, 2⟩ (rowAt 205)] = data_322
  rw [row_96, row_205]
  apply row_ext <;> decide +kernel
theorem entry_good_322 : EntryGood 322 := by
  unfold EntryGood
  rw [entry_322_checked]
  decide +kernel
theorem good_322 : Good (rowAt 322) := by
  rw [row_322]
  unfold Good
  decide +kernel

theorem entry_323_checked : entryAt 323 = entry_323 := by
  rw [entry_chunk_15 17 (by decide)]
  decide +kernel
theorem row_323 : rowAt 323 = data_323 := by
  rw [rowAt, dif_neg (by decide : ¬ 323 < 6), entry_323_checked]
  change forkRow [placeRow ⟨165, 6, 4, 5⟩ (rowAt 165), placeRow ⟨278, 0, 1, 4⟩ (rowAt 278), placeRow ⟨25, 1, 4, 5⟩ (rowAt 25)] = data_323
  rw [row_165, row_278, row_25]
  apply row_ext <;> decide +kernel
theorem entry_good_323 : EntryGood 323 := by
  unfold EntryGood
  rw [entry_323_checked]
  decide +kernel
theorem good_323 : Good (rowAt 323) := by
  rw [row_323]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 320 = data_320 ∧ Good (rowAt 320) ∧ EntryGood 320) ∧ (rowAt 321 = data_321 ∧ Good (rowAt 321) ∧ EntryGood 321) ∧ (rowAt 322 = data_322 ∧ Good (rowAt 322) ∧ EntryGood 322) ∧ (rowAt 323 = data_323 ∧ Good (rowAt 323) ∧ EntryGood 323) ∧ True := by
  exact ⟨⟨row_320, good_320, entry_good_320⟩, ⟨row_321, good_321, entry_good_321⟩, ⟨row_322, good_322, entry_good_322⟩, ⟨row_323, good_323, entry_good_323⟩, trivial⟩
