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
theorem entry_300_checked : entryAt 300 = entry_300 := by
  rw [entry_chunk_14 14 (by decide)]
  decide +kernel
theorem row_300 : rowAt 300 = data_300 := by
  rw [rowAt, dif_neg (by decide : ¬ 300 < 6), entry_300_checked]
  change forkRow [placeRow ⟨64, 3, 5, 1⟩ (rowAt 64), placeRow ⟨240, 2, 5, 1⟩ (rowAt 240), placeRow ⟨55, 3, 4, 5⟩ (rowAt 55)] = data_300
  rw [row_64, row_240, row_55]
  apply row_ext <;> decide +kernel
theorem entry_good_300 : EntryGood 300 := by
  unfold EntryGood
  rw [entry_300_checked]
  decide +kernel
theorem good_300 : Good (rowAt 300) := by
  rw [row_300]
  unfold Good
  decide +kernel

theorem entry_301_checked : entryAt 301 = entry_301 := by
  rw [entry_chunk_14 15 (by decide)]
  decide +kernel
theorem row_301 : rowAt 301 = data_301 := by
  rw [rowAt, dif_neg (by decide : ¬ 301 < 6), entry_301_checked]
  change forkRow [placeRow ⟨59, 0, 5, 4⟩ (rowAt 59), placeRow ⟨57, 0, 5, 4⟩ (rowAt 57), placeRow ⟨258, 4, 4, 5⟩ (rowAt 258)] = data_301
  rw [row_59, row_57, row_258]
  apply row_ext <;> decide +kernel
theorem entry_good_301 : EntryGood 301 := by
  unfold EntryGood
  rw [entry_301_checked]
  decide +kernel
theorem good_301 : Good (rowAt 301) := by
  rw [row_301]
  unfold Good
  decide +kernel

theorem entry_302_checked : entryAt 302 = entry_302 := by
  rw [entry_chunk_14 16 (by decide)]
  decide +kernel
theorem row_302 : rowAt 302 = data_302 := by
  rw [rowAt, dif_neg (by decide : ¬ 302 < 6), entry_302_checked]
  change forkRow [placeRow ⟨125, 0, 5, 3⟩ (rowAt 125), placeRow ⟨162, 4, 3, 6⟩ (rowAt 162)] = data_302
  rw [row_125, row_162]
  apply row_ext <;> decide +kernel
theorem entry_good_302 : EntryGood 302 := by
  unfold EntryGood
  rw [entry_302_checked]
  decide +kernel
theorem good_302 : Good (rowAt 302) := by
  rw [row_302]
  unfold Good
  decide +kernel

theorem entry_303_checked : entryAt 303 = entry_303 := by
  rw [entry_chunk_14 17 (by decide)]
  decide +kernel
theorem row_303 : rowAt 303 = data_303 := by
  rw [rowAt, dif_neg (by decide : ¬ 303 < 6), entry_303_checked]
  change forkRow [placeRow ⟨49, 4, 4, 5⟩ (rowAt 49), placeRow ⟨44, 1, 4, 5⟩ (rowAt 44), placeRow ⟨63, 0, 3, 5⟩ (rowAt 63), placeRow ⟨261, 0, 3, 4⟩ (rowAt 261)] = data_303
  rw [row_49, row_44, row_63, row_261]
  apply row_ext <;> decide +kernel
theorem entry_good_303 : EntryGood 303 := by
  unfold EntryGood
  rw [entry_303_checked]
  decide +kernel
theorem good_303 : Good (rowAt 303) := by
  rw [row_303]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 300 = data_300 ∧ Good (rowAt 300) ∧ EntryGood 300) ∧ (rowAt 301 = data_301 ∧ Good (rowAt 301) ∧ EntryGood 301) ∧ (rowAt 302 = data_302 ∧ Good (rowAt 302) ∧ EntryGood 302) ∧ (rowAt 303 = data_303 ∧ Good (rowAt 303) ∧ EntryGood 303) ∧ True := by
  exact ⟨⟨row_300, good_300, entry_good_300⟩, ⟨row_301, good_301, entry_good_301⟩, ⟨row_302, good_302, entry_good_302⟩, ⟨row_303, good_303, entry_good_303⟩, trivial⟩
