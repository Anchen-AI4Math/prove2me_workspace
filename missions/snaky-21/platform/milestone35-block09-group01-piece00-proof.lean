import Definitions.Def_Snaky35Cache09
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_group00_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_14 (j : ℕ) (hj : j < 20) : entryAt (286 + j) = tableChunk_14[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_24 : rowAt 24 = data_24 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_44 : rowAt 44 = data_44 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_49 : rowAt 49 = data_49 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_55 : rowAt 55 = data_55 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_57 : rowAt 57 = data_57 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_59 : rowAt 59 = data_59 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_63 : rowAt 63 = data_63 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_64 : rowAt 64 = data_64 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.1).1
theorem row_65 : rowAt 65 = data_65 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.2.1).1
theorem row_107 : rowAt 107 = data_107 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_125 : rowAt 125 = data_125 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_162 : rowAt 162 = data_162 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.1).1
theorem row_195 : rowAt 195 = data_195 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.1).1
theorem row_209 : rowAt 209 = data_209 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_240 : rowAt 240 = data_240 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_258 : rowAt 258 = data_258 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.1).1
theorem row_261 : rowAt 261 = data_261 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.1).1
theorem row_284 : rowAt 284 = data_284 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_289 : rowAt 289 = data_289 := (OAI.SnakyCertificate.MilestoneChecks.block09_group00_correct.2.1).1
theorem entry_296_checked : entryAt 296 = entry_296 := by
  rw [entry_chunk_14 10 (by decide)]
  decide +kernel
theorem row_296 : rowAt 296 = data_296 := by
  rw [rowAt, dif_neg (by decide : ¬ 296 < 6), entry_296_checked]
  change forkRow [placeRow ⟨107, 1, 4, 5⟩ (rowAt 107), placeRow ⟨209, 3, 3, 4⟩ (rowAt 209), placeRow ⟨65, 1, 4, 5⟩ (rowAt 65)] = data_296
  rw [row_107, row_209, row_65]
  apply row_ext <;> decide +kernel
theorem entry_good_296 : EntryGood 296 := by
  unfold EntryGood
  rw [entry_296_checked]
  decide +kernel
theorem good_296 : Good (rowAt 296) := by
  rw [row_296]
  unfold Good
  decide +kernel

theorem entry_297_checked : entryAt 297 = entry_297 := by
  rw [entry_chunk_14 11 (by decide)]
  decide +kernel
theorem row_297 : rowAt 297 = data_297 := by
  rw [rowAt, dif_neg (by decide : ¬ 297 < 6), entry_297_checked]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (rowAt 6), placeRow ⟨289, 1, 7, 4⟩ (rowAt 289)] = data_297
  rw [row_6, row_289]
  apply row_ext <;> decide +kernel
theorem entry_good_297 : EntryGood 297 := by
  unfold EntryGood
  rw [entry_297_checked]
  decide +kernel
theorem good_297 : Good (rowAt 297) := by
  rw [row_297]
  unfold Good
  decide +kernel

theorem entry_298_checked : entryAt 298 = entry_298 := by
  rw [entry_chunk_14 12 (by decide)]
  decide +kernel
theorem row_298 : rowAt 298 = data_298 := by
  rw [rowAt, dif_neg (by decide : ¬ 298 < 6), entry_298_checked]
  change forkRow [placeRow ⟨24, 2, 7, 3⟩ (rowAt 24), placeRow ⟨24, 6, 3, 3⟩ (rowAt 24), placeRow ⟨107, 4, 3, 4⟩ (rowAt 107), placeRow ⟨195, 0, 7, 4⟩ (rowAt 195)] = data_298
  rw [row_24, row_107, row_195]
  apply row_ext <;> decide +kernel
theorem entry_good_298 : EntryGood 298 := by
  unfold EntryGood
  rw [entry_298_checked]
  decide +kernel
theorem good_298 : Good (rowAt 298) := by
  rw [row_298]
  unfold Good
  decide +kernel

theorem entry_299_checked : entryAt 299 = entry_299 := by
  rw [entry_chunk_14 13 (by decide)]
  decide +kernel
theorem row_299 : rowAt 299 = data_299 := by
  rw [rowAt, dif_neg (by decide : ¬ 299 < 6), entry_299_checked]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (rowAt 6), placeRow ⟨284, 0, 4, 5⟩ (rowAt 284)] = data_299
  rw [row_6, row_284]
  apply row_ext <;> decide +kernel
theorem entry_good_299 : EntryGood 299 := by
  unfold EntryGood
  rw [entry_299_checked]
  decide +kernel
theorem good_299 : Good (rowAt 299) := by
  rw [row_299]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 296 = data_296 ∧ Good (rowAt 296) ∧ EntryGood 296) ∧ (rowAt 297 = data_297 ∧ Good (rowAt 297) ∧ EntryGood 297) ∧ (rowAt 298 = data_298 ∧ Good (rowAt 298) ∧ EntryGood 298) ∧ (rowAt 299 = data_299 ∧ Good (rowAt 299) ∧ EntryGood 299) ∧ True := by
  exact ⟨⟨row_296, good_296, entry_good_296⟩, ⟨row_297, good_297, entry_good_297⟩, ⟨row_298, good_298, entry_good_298⟩, ⟨row_299, good_299, entry_good_299⟩, trivial⟩
