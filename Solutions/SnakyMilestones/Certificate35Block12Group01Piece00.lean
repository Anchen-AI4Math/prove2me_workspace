import Definitions.Def_Snaky35Cache12
import Solutions.SnakyMilestones.Certificate35Block12Group00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_392_checked : entryAt 392 = entry_392 := by
  rw [entry_chunk_19 6 (by decide)]
  decide +kernel
theorem row_392 : rowAt 392 = data_392 := by
  rw [rowAt, dif_neg (by decide : ¬ 392 < 6), entry_392_checked]
  change forkRow [placeRow ⟨24, 7, 3, 1⟩ (rowAt 24), placeRow ⟨107, 1, 4, 5⟩ (rowAt 107), placeRow ⟨236, 0, 5, 5⟩ (rowAt 236), placeRow ⟨364, 2, 4, 1⟩ (rowAt 364)] = data_392
  rw [row_24, row_107, row_236, row_364]
  apply row_ext <;> decide +kernel
theorem entry_good_392 : EntryGood 392 := by
  unfold EntryGood
  rw [entry_392_checked]
  decide +kernel
theorem good_392 : Good (rowAt 392) := by
  rw [row_392]
  unfold Good
  decide +kernel

theorem entry_393_checked : entryAt 393 = entry_393 := by
  rw [entry_chunk_19 7 (by decide)]
  decide +kernel
theorem row_393 : rowAt 393 = data_393 := by
  rw [rowAt, dif_neg (by decide : ¬ 393 < 6), entry_393_checked]
  change forkRow [placeRow ⟨107, 3, 4, 5⟩ (rowAt 107), placeRow ⟨348, 0, 6, 3⟩ (rowAt 348), placeRow ⟨65, 3, 4, 5⟩ (rowAt 65), placeRow ⟨303, 0, 4, 5⟩ (rowAt 303)] = data_393
  rw [row_107, row_348, row_65, row_303]
  apply row_ext <;> decide +kernel
theorem entry_good_393 : EntryGood 393 := by
  unfold EntryGood
  rw [entry_393_checked]
  decide +kernel
theorem good_393 : Good (rowAt 393) := by
  rw [row_393]
  unfold Good
  decide +kernel

theorem entry_394_checked : entryAt 394 = entry_394 := by
  rw [entry_chunk_19 8 (by decide)]
  decide +kernel
theorem row_394 : rowAt 394 = data_394 := by
  rw [rowAt, dif_neg (by decide : ¬ 394 < 6), entry_394_checked]
  change forkRow [placeRow ⟨226, 4, 1, 4⟩ (rowAt 226), placeRow ⟨226, 0, 5, 4⟩ (rowAt 226), placeRow ⟨327, 4, 3, 4⟩ (rowAt 327), placeRow ⟨327, 6, 3, 3⟩ (rowAt 327), placeRow ⟨226, 6, 1, 3⟩ (rowAt 226), placeRow ⟨226, 2, 5, 3⟩ (rowAt 226)] = data_394
  rw [row_226, row_327]
  apply row_ext <;> decide +kernel
theorem entry_good_394 : EntryGood 394 := by
  unfold EntryGood
  rw [entry_394_checked]
  decide +kernel
theorem good_394 : Good (rowAt 394) := by
  rw [row_394]
  unfold Good
  decide +kernel

theorem entry_395_checked : entryAt 395 = entry_395 := by
  rw [entry_chunk_19 9 (by decide)]
  decide +kernel
theorem row_395 : rowAt 395 = data_395 := by
  rw [rowAt, dif_neg (by decide : ¬ 395 < 6), entry_395_checked]
  change forkRow [placeRow ⟨211, 4, 2, 4⟩ (rowAt 211), placeRow ⟨376, 0, 6, 4⟩ (rowAt 376), placeRow ⟨24, 2, 6, 3⟩ (rowAt 24), placeRow ⟨236, 3, 2, 5⟩ (rowAt 236)] = data_395
  rw [row_211, row_376, row_24, row_236]
  apply row_ext <;> decide +kernel
theorem entry_good_395 : EntryGood 395 := by
  unfold EntryGood
  rw [entry_395_checked]
  decide +kernel
theorem good_395 : Good (rowAt 395) := by
  rw [row_395]
  unfold Good
  decide +kernel


theorem block12_group01_piece00_correct : (rowAt 392 = data_392 ∧ Good (rowAt 392) ∧ EntryGood 392) ∧ (rowAt 393 = data_393 ∧ Good (rowAt 393) ∧ EntryGood 393) ∧ (rowAt 394 = data_394 ∧ Good (rowAt 394) ∧ EntryGood 394) ∧ (rowAt 395 = data_395 ∧ Good (rowAt 395) ∧ EntryGood 395) ∧ True := by
  exact ⟨⟨row_392, good_392, entry_good_392⟩, ⟨row_393, good_393, entry_good_393⟩, ⟨row_394, good_394, entry_good_394⟩, ⟨row_395, good_395, entry_good_395⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
