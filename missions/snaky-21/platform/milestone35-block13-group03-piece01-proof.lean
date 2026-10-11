import Definitions.Def_Snaky35Cache13
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block11_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block12_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block13_group02_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_21 (j : ℕ) (hj : j < 20) : entryAt (426 + j) = tableChunk_21[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem entry_chunk_22 (j : ℕ) (hj : j < 20) : entryAt (446 + j) = tableChunk_22[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_0 : rowAt 0 = data_0 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.1).1
theorem row_4 : rowAt 4 = data_4 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_7 : rowAt 7 = data_7 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.1).1
theorem row_9 : rowAt 9 = data_9 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.1).1
theorem row_63 : rowAt 63 = data_63 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_142 : rowAt 142 = data_142 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_160 : rowAt 160 = data_160 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.1).1
theorem row_194 : rowAt 194 = data_194 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.1).1
theorem row_201 : rowAt 201 = data_201 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.1).1
theorem row_236 : rowAt 236 = data_236 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_353 : rowAt 353 = data_353 := (OAI.SnakyCertificate.MilestoneChecks.block11_correct.2.1).1
theorem row_412 : rowAt 412 = data_412 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_432 : rowAt 432 = data_432 := (OAI.SnakyCertificate.MilestoneChecks.block13_group02_correct.1).1
theorem row_433 : rowAt 433 = data_433 := (OAI.SnakyCertificate.MilestoneChecks.block13_group02_correct.2.1).1
theorem row_435 : rowAt 435 = data_435 := (OAI.SnakyCertificate.MilestoneChecks.block13_group02_correct.2.2.2.1).1
theorem row_436 : rowAt 436 = data_436 := (OAI.SnakyCertificate.MilestoneChecks.block13_group02_correct.2.2.2.2.1).1
theorem row_438 : rowAt 438 = data_438 := (OAI.SnakyCertificate.MilestoneChecks.block13_group02_correct.2.2.2.2.2.2.1).1
theorem entry_444_checked : entryAt 444 = entry_444 := by
  rw [entry_chunk_21 18 (by decide)]
  decide +kernel
theorem row_444 : rowAt 444 = data_444 := by
  rw [rowAt, dif_neg (by decide : ¬ 444 < 6), entry_444_checked]
  change forkRow [placeRow ⟨194, 0, 5, 3⟩ (rowAt 194), placeRow ⟨160, 3, 4, 1⟩ (rowAt 160), placeRow ⟨142, 7, 4, 1⟩ (rowAt 142), placeRow ⟨236, 0, 5, 5⟩ (rowAt 236), placeRow ⟨353, 4, 1, 2⟩ (rowAt 353), placeRow ⟨412, 0, 5, 3⟩ (rowAt 412)] = data_444
  rw [row_194, row_160, row_142, row_236, row_353, row_412]
  apply row_ext <;> decide +kernel
theorem entry_good_444 : EntryGood 444 := by
  unfold EntryGood
  rw [entry_444_checked]
  decide +kernel
theorem good_444 : Good (rowAt 444) := by
  rw [row_444]
  unfold Good
  decide +kernel

theorem entry_445_checked : entryAt 445 = entry_445 := by
  rw [entry_chunk_21 19 (by decide)]
  decide +kernel
theorem row_445 : rowAt 445 = data_445 := by
  rw [rowAt, dif_neg (by decide : ¬ 445 < 6), entry_445_checked]
  change forkRow [placeRow ⟨9, 4, 3, 4⟩ (rowAt 9), placeRow ⟨432, 0, 5, 7⟩ (rowAt 432)] = data_445
  rw [row_9, row_432]
  apply row_ext <;> decide +kernel
theorem entry_good_445 : EntryGood 445 := by
  unfold EntryGood
  rw [entry_445_checked]
  decide +kernel
theorem good_445 : Good (rowAt 445) := by
  rw [row_445]
  unfold Good
  decide +kernel

theorem entry_446_checked : entryAt 446 = entry_446 := by
  rw [entry_chunk_22 0 (by decide)]
  decide +kernel
theorem row_446 : rowAt 446 = data_446 := by
  rw [rowAt, dif_neg (by decide : ¬ 446 < 6), entry_446_checked]
  change forkRow [placeRow ⟨4, 6, 4, 3⟩ (rowAt 4), placeRow ⟨438, 0, 6, 5⟩ (rowAt 438)] = data_446
  rw [row_4, row_438]
  apply row_ext <;> decide +kernel
theorem entry_good_446 : EntryGood 446 := by
  unfold EntryGood
  rw [entry_446_checked]
  decide +kernel
theorem good_446 : Good (rowAt 446) := by
  rw [row_446]
  unfold Good
  decide +kernel

theorem entry_447_checked : entryAt 447 = entry_447 := by
  rw [entry_chunk_22 1 (by decide)]
  decide +kernel
theorem row_447 : rowAt 447 = data_447 := by
  rw [rowAt, dif_neg (by decide : ¬ 447 < 6), entry_447_checked]
  change forkRow [placeRow ⟨0, 0, 0, 3⟩ (rowAt 0), placeRow ⟨436, 4, 4, 6⟩ (rowAt 436)] = data_447
  rw [row_0, row_436]
  apply row_ext <;> decide +kernel
theorem entry_good_447 : EntryGood 447 := by
  unfold EntryGood
  rw [entry_447_checked]
  decide +kernel
theorem good_447 : Good (rowAt 447) := by
  rw [row_447]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 444 = data_444 ∧ Good (rowAt 444) ∧ EntryGood 444) ∧ (rowAt 445 = data_445 ∧ Good (rowAt 445) ∧ EntryGood 445) ∧ (rowAt 446 = data_446 ∧ Good (rowAt 446) ∧ EntryGood 446) ∧ (rowAt 447 = data_447 ∧ Good (rowAt 447) ∧ EntryGood 447) ∧ True := by
  exact ⟨⟨row_444, good_444, entry_good_444⟩, ⟨row_445, good_445, entry_good_445⟩, ⟨row_446, good_446, entry_good_446⟩, ⟨row_447, good_447, entry_good_447⟩, trivial⟩
