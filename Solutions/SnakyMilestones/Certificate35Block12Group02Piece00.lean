import Definitions.Def_Snaky35Cache12
import Solutions.SnakyMilestones.Certificate35Block12Group01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_400_checked : entryAt 400 = entry_400 := by
  rw [entry_chunk_19 14 (by decide)]
  decide +kernel
theorem row_400 : rowAt 400 = data_400 := by
  rw [rowAt, dif_neg (by decide : ¬ 400 < 6), entry_400_checked]
  change forkRow [placeRow ⟨283, 4, 2, 4⟩ (rowAt 283), placeRow ⟨252, 4, 2, 4⟩ (rowAt 252), placeRow ⟨176, 4, 2, 4⟩ (rowAt 176), placeRow ⟨197, 0, 6, 4⟩ (rowAt 197), placeRow ⟨283, 0, 6, 4⟩ (rowAt 283), placeRow ⟨245, 4, 2, 4⟩ (rowAt 245)] = data_400
  rw [row_283, row_252, row_176, row_197, row_245]
  apply row_ext <;> decide +kernel
theorem entry_good_400 : EntryGood 400 := by
  unfold EntryGood
  rw [entry_400_checked]
  decide +kernel
theorem good_400 : Good (rowAt 400) := by
  rw [row_400]
  unfold Good
  decide +kernel

theorem entry_401_checked : entryAt 401 = entry_401 := by
  rw [entry_chunk_19 15 (by decide)]
  decide +kernel
theorem row_401 : rowAt 401 = data_401 := by
  rw [rowAt, dif_neg (by decide : ¬ 401 < 6), entry_401_checked]
  change forkRow [placeRow ⟨24, 7, 3, 2⟩ (rowAt 24), placeRow ⟨286, 0, 4, 6⟩ (rowAt 286), placeRow ⟨364, 2, 4, 2⟩ (rowAt 364), placeRow ⟨319, 1, 3, 6⟩ (rowAt 319)] = data_401
  rw [row_24, row_286, row_364, row_319]
  apply row_ext <;> decide +kernel
theorem entry_good_401 : EntryGood 401 := by
  unfold EntryGood
  rw [entry_401_checked]
  decide +kernel
theorem good_401 : Good (rowAt 401) := by
  rw [row_401]
  unfold Good
  decide +kernel

theorem entry_402_checked : entryAt 402 = entry_402 := by
  rw [entry_chunk_19 16 (by decide)]
  decide +kernel
theorem row_402 : rowAt 402 = data_402 := by
  rw [rowAt, dif_neg (by decide : ¬ 402 < 6), entry_402_checked]
  change forkRow [placeRow ⟨29, 3, 3, 0⟩ (rowAt 29), placeRow ⟨384, 0, 5, 4⟩ (rowAt 384)] = data_402
  rw [row_29, row_384]
  apply row_ext <;> decide +kernel
theorem entry_good_402 : EntryGood 402 := by
  unfold EntryGood
  rw [entry_402_checked]
  decide +kernel
theorem good_402 : Good (rowAt 402) := by
  rw [row_402]
  unfold Good
  decide +kernel

theorem entry_403_checked : entryAt 403 = entry_403 := by
  rw [entry_chunk_19 17 (by decide)]
  decide +kernel
theorem row_403 : rowAt 403 = data_403 := by
  rw [rowAt, dif_neg (by decide : ¬ 403 < 6), entry_403_checked]
  change forkRow [placeRow ⟨202, 1, 4, 5⟩ (rowAt 202), placeRow ⟨180, 0, 4, 5⟩ (rowAt 180), placeRow ⟨314, 4, 5, 4⟩ (rowAt 314), placeRow ⟨63, 0, 3, 5⟩ (rowAt 63), placeRow ⟨388, 0, 3, 4⟩ (rowAt 388)] = data_403
  rw [row_202, row_180, row_314, row_63, row_388]
  apply row_ext <;> decide +kernel
theorem entry_good_403 : EntryGood 403 := by
  unfold EntryGood
  rw [entry_403_checked]
  decide +kernel
theorem good_403 : Good (rowAt 403) := by
  rw [row_403]
  unfold Good
  decide +kernel


theorem block12_group02_piece00_correct : (rowAt 400 = data_400 ∧ Good (rowAt 400) ∧ EntryGood 400) ∧ (rowAt 401 = data_401 ∧ Good (rowAt 401) ∧ EntryGood 401) ∧ (rowAt 402 = data_402 ∧ Good (rowAt 402) ∧ EntryGood 402) ∧ (rowAt 403 = data_403 ∧ Good (rowAt 403) ∧ EntryGood 403) ∧ True := by
  exact ⟨⟨row_400, good_400, entry_good_400⟩, ⟨row_401, good_401, entry_good_401⟩, ⟨row_402, good_402, entry_good_402⟩, ⟨row_403, good_403, entry_good_403⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
