import Definitions.Def_Snaky35Cache10
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block10_group00_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_16 (j : ℕ) (hj : j < 20) : entryAt (326 + j) = tableChunk_16[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_0 : rowAt 0 = data_0 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.1).1
theorem row_4 : rowAt 4 = data_4 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.1).1
theorem row_24 : rowAt 24 = data_24 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_25 : rowAt 25 = data_25 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_65 : rowAt 65 = data_65 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.2.1).1
theorem row_88 : rowAt 88 = data_88 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_107 : rowAt 107 = data_107 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_143 : rowAt 143 = data_143 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_162 : rowAt 162 = data_162 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.1).1
theorem row_199 : rowAt 199 = data_199 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.1).1
theorem row_208 : rowAt 208 = data_208 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_210 : rowAt 210 = data_210 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_230 : rowAt 230 = data_230 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.1).1
theorem row_241 : rowAt 241 = data_241 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_250 : rowAt 250 = data_250 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_259 : rowAt 259 = data_259 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.1).1
theorem row_260 : rowAt 260 = data_260 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.1).1
theorem row_275 : rowAt 275 = data_275 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_290 : rowAt 290 = data_290 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.1).1
theorem row_300 : rowAt 300 = data_300 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_304 : rowAt 304 = data_304 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_322 : rowAt 322 = data_322 := (OAI.SnakyCertificate.MilestoneChecks.block10_group00_correct.2.2.1).1
theorem entry_336_checked : entryAt 336 = entry_336 := by
  rw [entry_chunk_16 10 (by decide)]
  decide +kernel
theorem row_336 : rowAt 336 = data_336 := by
  rw [rowAt, dif_neg (by decide : ¬ 336 < 6), entry_336_checked]
  change forkRow [placeRow ⟨25, 6, 2, 3⟩ (rowAt 25), placeRow ⟨199, 3, 2, 4⟩ (rowAt 199), placeRow ⟨65, 0, 6, 4⟩ (rowAt 65), placeRow ⟨304, 0, 2, 4⟩ (rowAt 304)] = data_336
  rw [row_25, row_199, row_65, row_304]
  apply row_ext <;> decide +kernel
theorem entry_good_336 : EntryGood 336 := by
  unfold EntryGood
  rw [entry_336_checked]
  decide +kernel
theorem good_336 : Good (rowAt 336) := by
  rw [row_336]
  unfold Good
  decide +kernel

theorem entry_337_checked : entryAt 337 = entry_337 := by
  rw [entry_chunk_16 11 (by decide)]
  decide +kernel
theorem row_337 : rowAt 337 = data_337 := by
  rw [rowAt, dif_neg (by decide : ¬ 337 < 6), entry_337_checked]
  change forkRow [placeRow ⟨107, 3, 3, 7⟩ (rowAt 107), placeRow ⟨230, 2, 1, 5⟩ (rowAt 230)] = data_337
  rw [row_107, row_230]
  apply row_ext <;> decide +kernel
theorem entry_good_337 : EntryGood 337 := by
  unfold EntryGood
  rw [entry_337_checked]
  decide +kernel
theorem good_337 : Good (rowAt 337) := by
  rw [row_337]
  unfold Good
  decide +kernel

theorem entry_338_checked : entryAt 338 = entry_338 := by
  rw [entry_chunk_16 12 (by decide)]
  decide +kernel
theorem row_338 : rowAt 338 = data_338 := by
  rw [rowAt, dif_neg (by decide : ¬ 338 < 6), entry_338_checked]
  change forkRow [placeRow ⟨241, 0, 6, 4⟩ (rowAt 241), placeRow ⟨275, 4, 2, 4⟩ (rowAt 275), placeRow ⟨107, 4, 2, 4⟩ (rowAt 107)] = data_338
  rw [row_241, row_275, row_107]
  apply row_ext <;> decide +kernel
theorem entry_good_338 : EntryGood 338 := by
  unfold EntryGood
  rw [entry_338_checked]
  decide +kernel
theorem good_338 : Good (rowAt 338) := by
  rw [row_338]
  unfold Good
  decide +kernel

theorem entry_339_checked : entryAt 339 = entry_339 := by
  rw [entry_chunk_16 13 (by decide)]
  decide +kernel
theorem row_339 : rowAt 339 = data_339 := by
  rw [rowAt, dif_neg (by decide : ¬ 339 < 6), entry_339_checked]
  change forkRow [placeRow ⟨4, 1, 4, 3⟩ (rowAt 4), placeRow ⟨322, 0, 6, 4⟩ (rowAt 322)] = data_339
  rw [row_4, row_322]
  apply row_ext <;> decide +kernel
theorem entry_good_339 : EntryGood 339 := by
  unfold EntryGood
  rw [entry_339_checked]
  decide +kernel
theorem good_339 : Good (rowAt 339) := by
  rw [row_339]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 336 = data_336 ∧ Good (rowAt 336) ∧ EntryGood 336) ∧ (rowAt 337 = data_337 ∧ Good (rowAt 337) ∧ EntryGood 337) ∧ (rowAt 338 = data_338 ∧ Good (rowAt 338) ∧ EntryGood 338) ∧ (rowAt 339 = data_339 ∧ Good (rowAt 339) ∧ EntryGood 339) ∧ True := by
  exact ⟨⟨row_336, good_336, entry_good_336⟩, ⟨row_337, good_337, entry_good_337⟩, ⟨row_338, good_338, entry_good_338⟩, ⟨row_339, good_339, entry_good_339⟩, trivial⟩
