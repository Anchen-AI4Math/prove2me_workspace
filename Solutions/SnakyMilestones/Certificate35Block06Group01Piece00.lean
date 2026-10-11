import Definitions.Def_Snaky35Cache06
import Solutions.SnakyMilestones.Certificate35Block06Group00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_200_checked : entryAt 200 = entry_200 := by
  rw [entry_chunk_9 14 (by decide)]
  decide +kernel
theorem row_200 : rowAt 200 = data_200 := by
  rw [rowAt, dif_neg (by decide : ¬ 200 < 6), entry_200_checked]
  change forkRow [placeRow ⟨103, 0, 3, 4⟩ (rowAt 103), placeRow ⟨64, 3, 5, 1⟩ (rowAt 64), placeRow ⟨55, 1, 4, 5⟩ (rowAt 55)] = data_200
  rw [row_103, row_64, row_55]
  apply row_ext <;> decide +kernel
theorem entry_good_200 : EntryGood 200 := by
  unfold EntryGood
  rw [entry_200_checked]
  decide +kernel
theorem good_200 : Good (rowAt 200) := by
  rw [row_200]
  unfold Good
  decide +kernel

theorem entry_201_checked : entryAt 201 = entry_201 := by
  rw [entry_chunk_9 15 (by decide)]
  decide +kernel
theorem row_201 : rowAt 201 = data_201 := by
  rw [rowAt, dif_neg (by decide : ¬ 201 < 6), entry_201_checked]
  change forkRow [placeRow ⟨45, 3, 5, 7⟩ (rowAt 45), placeRow ⟨82, 0, 6, 5⟩ (rowAt 82)] = data_201
  rw [row_45, row_82]
  apply row_ext <;> decide +kernel
theorem entry_good_201 : EntryGood 201 := by
  unfold EntryGood
  rw [entry_201_checked]
  decide +kernel
theorem good_201 : Good (rowAt 201) := by
  rw [row_201]
  unfold Good
  decide +kernel

theorem entry_202_checked : entryAt 202 = entry_202 := by
  rw [entry_chunk_9 16 (by decide)]
  decide +kernel
theorem row_202 : rowAt 202 = data_202 := by
  rw [rowAt, dif_neg (by decide : ¬ 202 < 6), entry_202_checked]
  change forkRow [placeRow ⟨150, 0, 5, 4⟩ (rowAt 150), placeRow ⟨7, 0, 4, 5⟩ (rowAt 7), placeRow ⟨108, 0, 5, 4⟩ (rowAt 108)] = data_202
  rw [row_150, row_7, row_108]
  apply row_ext <;> decide +kernel
theorem entry_good_202 : EntryGood 202 := by
  unfold EntryGood
  rw [entry_202_checked]
  decide +kernel
theorem good_202 : Good (rowAt 202) := by
  rw [row_202]
  unfold Good
  decide +kernel

theorem entry_203_checked : entryAt 203 = entry_203 := by
  rw [entry_chunk_9 17 (by decide)]
  decide +kernel
theorem row_203 : rowAt 203 = data_203 := by
  rw [rowAt, dif_neg (by decide : ¬ 203 < 6), entry_203_checked]
  change forkRow [placeRow ⟨18, 6, 1, 3⟩ (rowAt 18), placeRow ⟨107, 0, 5, 4⟩ (rowAt 107), placeRow ⟨163, 0, 5, 4⟩ (rowAt 163)] = data_203
  rw [row_18, row_107, row_163]
  apply row_ext <;> decide +kernel
theorem entry_good_203 : EntryGood 203 := by
  unfold EntryGood
  rw [entry_203_checked]
  decide +kernel
theorem good_203 : Good (rowAt 203) := by
  rw [row_203]
  unfold Good
  decide +kernel


theorem block06_group01_piece00_correct : (rowAt 200 = data_200 ∧ Good (rowAt 200) ∧ EntryGood 200) ∧ (rowAt 201 = data_201 ∧ Good (rowAt 201) ∧ EntryGood 201) ∧ (rowAt 202 = data_202 ∧ Good (rowAt 202) ∧ EntryGood 202) ∧ (rowAt 203 = data_203 ∧ Good (rowAt 203) ∧ EntryGood 203) ∧ True := by
  exact ⟨⟨row_200, good_200, entry_good_200⟩, ⟨row_201, good_201, entry_good_201⟩, ⟨row_202, good_202, entry_good_202⟩, ⟨row_203, good_203, entry_good_203⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
