import Definitions.Def_Snaky35Cache05
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_8 (j : ℕ) (hj : j < 20) : entryAt (166 + j) = tableChunk_8[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.1) j hj
theorem entry_chunk_9 (j : ℕ) (hj : j < 20) : entryAt (186 + j) = tableChunk_9[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_7 : rowAt 7 = data_7 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.1).1
theorem row_12 : rowAt 12 = data_12 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_34 : rowAt 34 = data_34 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.1).1
theorem row_35 : rowAt 35 = data_35 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.1).1
theorem row_44 : rowAt 44 = data_44 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_46 : rowAt 46 = data_46 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_49 : rowAt 49 = data_49 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_84 : rowAt 84 = data_84 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_85 : rowAt 85 = data_85 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_86 : rowAt 86 = data_86 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_108 : rowAt 108 = data_108 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_111 : rowAt 111 = data_111 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_112 : rowAt 112 = data_112 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_141 : rowAt 141 = data_141 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_145 : rowAt 145 = data_145 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem entry_188_checked : entryAt 188 = entry_188 := by
  rw [entry_chunk_9 2 (by decide)]
  decide +kernel
theorem row_188 : rowAt 188 = data_188 := by
  rw [rowAt, dif_neg (by decide : ¬ 188 < 6), entry_188_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨112, 5, 7, 4⟩ (rowAt 112)] = data_188
  rw [row_6, row_112]
  apply row_ext <;> decide +kernel
theorem entry_good_188 : EntryGood 188 := by
  unfold EntryGood
  rw [entry_188_checked]
  decide +kernel
theorem good_188 : Good (rowAt 188) := by
  rw [row_188]
  unfold Good
  decide +kernel

theorem entry_189_checked : entryAt 189 = entry_189 := by
  rw [entry_chunk_9 3 (by decide)]
  decide +kernel
theorem row_189 : rowAt 189 = data_189 := by
  rw [rowAt, dif_neg (by decide : ¬ 189 < 6), entry_189_checked]
  change forkRow [placeRow ⟨12, 0, 5, 4⟩ (rowAt 12), placeRow ⟨86, 4, 1, 4⟩ (rowAt 86)] = data_189
  rw [row_12, row_86]
  apply row_ext <;> decide +kernel
theorem entry_good_189 : EntryGood 189 := by
  unfold EntryGood
  rw [entry_189_checked]
  decide +kernel
theorem good_189 : Good (rowAt 189) := by
  rw [row_189]
  unfold Good
  decide +kernel

theorem entry_190_checked : entryAt 190 = entry_190 := by
  rw [entry_chunk_9 4 (by decide)]
  decide +kernel
theorem row_190 : rowAt 190 = data_190 := by
  rw [rowAt, dif_neg (by decide : ¬ 190 < 6), entry_190_checked]
  change forkRow [placeRow ⟨46, 0, 5, 4⟩ (rowAt 46), placeRow ⟨85, 2, 3, 3⟩ (rowAt 85), placeRow ⟨111, 3, 4, 3⟩ (rowAt 111)] = data_190
  rw [row_46, row_85, row_111]
  apply row_ext <;> decide +kernel
theorem entry_good_190 : EntryGood 190 := by
  unfold EntryGood
  rw [entry_190_checked]
  decide +kernel
theorem good_190 : Good (rowAt 190) := by
  rw [row_190]
  unfold Good
  decide +kernel

theorem entry_191_checked : entryAt 191 = entry_191 := by
  rw [entry_chunk_9 5 (by decide)]
  decide +kernel
theorem row_191 : rowAt 191 = data_191 := by
  rw [rowAt, dif_neg (by decide : ¬ 191 < 6), entry_191_checked]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (rowAt 6), placeRow ⟨145, 0, 4, 5⟩ (rowAt 145)] = data_191
  rw [row_6, row_145]
  apply row_ext <;> decide +kernel
theorem entry_good_191 : EntryGood 191 := by
  unfold EntryGood
  rw [entry_191_checked]
  decide +kernel
theorem good_191 : Good (rowAt 191) := by
  rw [row_191]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 188 = data_188 ∧ Good (rowAt 188) ∧ EntryGood 188) ∧ (rowAt 189 = data_189 ∧ Good (rowAt 189) ∧ EntryGood 189) ∧ (rowAt 190 = data_190 ∧ Good (rowAt 190) ∧ EntryGood 190) ∧ (rowAt 191 = data_191 ∧ Good (rowAt 191) ∧ EntryGood 191) ∧ True := by
  exact ⟨⟨row_188, good_188, entry_good_188⟩, ⟨row_189, good_189, entry_good_189⟩, ⟨row_190, good_190, entry_good_190⟩, ⟨row_191, good_191, entry_good_191⟩, trivial⟩
