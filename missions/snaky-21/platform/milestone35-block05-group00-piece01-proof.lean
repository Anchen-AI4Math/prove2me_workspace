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
theorem entry_chunk_7 (j : ℕ) (hj : j < 20) : entryAt (146 + j) = tableChunk_7[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.1) j hj
theorem entry_chunk_8 (j : ℕ) (hj : j < 20) : entryAt (166 + j) = tableChunk_8[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.1) j hj
theorem row_0 : rowAt 0 = data_0 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.1).1
theorem row_2 : rowAt 2 = data_2 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_7 : rowAt 7 = data_7 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.1).1
theorem row_15 : rowAt 15 = data_15 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_32 : rowAt 32 = data_32 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.1).1
theorem row_44 : rowAt 44 = data_44 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_49 : rowAt 49 = data_49 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_56 : rowAt 56 = data_56 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_57 : rowAt 57 = data_57 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_63 : rowAt 63 = data_63 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_86 : rowAt 86 = data_86 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_107 : rowAt 107 = data_107 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_110 : rowAt 110 = data_110 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_127 : rowAt 127 = data_127 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_157 : rowAt 157 = data_157 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem entry_164_checked : entryAt 164 = entry_164 := by
  rw [entry_chunk_7 18 (by decide)]
  decide +kernel
theorem row_164 : rowAt 164 = data_164 := by
  rw [rowAt, dif_neg (by decide : ¬ 164 < 6), entry_164_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨110, 0, 5, 4⟩ (rowAt 110)] = data_164
  rw [row_6, row_110]
  apply row_ext <;> decide +kernel
theorem entry_good_164 : EntryGood 164 := by
  unfold EntryGood
  rw [entry_164_checked]
  decide +kernel
theorem good_164 : Good (rowAt 164) := by
  rw [row_164]
  unfold Good
  decide +kernel

theorem entry_165_checked : entryAt 165 = entry_165 := by
  rw [entry_chunk_7 19 (by decide)]
  decide +kernel
theorem row_165 : rowAt 165 = data_165 := by
  rw [rowAt, dif_neg (by decide : ¬ 165 < 6), entry_165_checked]
  change forkRow [placeRow ⟨0, 7, 5, 8⟩ (rowAt 0), placeRow ⟨107, 0, 7, 5⟩ (rowAt 107)] = data_165
  rw [row_0, row_107]
  apply row_ext <;> decide +kernel
theorem entry_good_165 : EntryGood 165 := by
  unfold EntryGood
  rw [entry_165_checked]
  decide +kernel
theorem good_165 : Good (rowAt 165) := by
  rw [row_165]
  unfold Good
  decide +kernel

theorem entry_166_checked : entryAt 166 = entry_166 := by
  rw [entry_chunk_8 0 (by decide)]
  decide +kernel
theorem row_166 : rowAt 166 = data_166 := by
  rw [rowAt, dif_neg (by decide : ¬ 166 < 6), entry_166_checked]
  change forkRow [placeRow ⟨2, 7, 4, 5⟩ (rowAt 2), placeRow ⟨107, 0, 6, 4⟩ (rowAt 107)] = data_166
  rw [row_2, row_107]
  apply row_ext <;> decide +kernel
theorem entry_good_166 : EntryGood 166 := by
  unfold EntryGood
  rw [entry_166_checked]
  decide +kernel
theorem good_166 : Good (rowAt 166) := by
  rw [row_166]
  unfold Good
  decide +kernel

theorem entry_167_checked : entryAt 167 = entry_167 := by
  rw [entry_chunk_8 1 (by decide)]
  decide +kernel
theorem row_167 : rowAt 167 = data_167 := by
  rw [rowAt, dif_neg (by decide : ¬ 167 < 6), entry_167_checked]
  change forkRow [placeRow ⟨57, 0, 5, 4⟩ (rowAt 57), placeRow ⟨57, 4, 0, 4⟩ (rowAt 57)] = data_167
  rw [row_57]
  apply row_ext <;> decide +kernel
theorem entry_good_167 : EntryGood 167 := by
  unfold EntryGood
  rw [entry_167_checked]
  decide +kernel
theorem good_167 : Good (rowAt 167) := by
  rw [row_167]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 164 = data_164 ∧ Good (rowAt 164) ∧ EntryGood 164) ∧ (rowAt 165 = data_165 ∧ Good (rowAt 165) ∧ EntryGood 165) ∧ (rowAt 166 = data_166 ∧ Good (rowAt 166) ∧ EntryGood 166) ∧ (rowAt 167 = data_167 ∧ Good (rowAt 167) ∧ EntryGood 167) ∧ True := by
  exact ⟨⟨row_164, good_164, entry_good_164⟩, ⟨row_165, good_165, entry_good_165⟩, ⟨row_166, good_166, entry_good_166⟩, ⟨row_167, good_167, entry_good_167⟩, trivial⟩
