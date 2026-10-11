import Definitions.Def_Snaky35Cache10
import Solutions.SnakyMilestones.Certificate35Block10Group01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
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


theorem block10_group02_piece00_correct : (rowAt 336 = data_336 ∧ Good (rowAt 336) ∧ EntryGood 336) ∧ (rowAt 337 = data_337 ∧ Good (rowAt 337) ∧ EntryGood 337) ∧ (rowAt 338 = data_338 ∧ Good (rowAt 338) ∧ EntryGood 338) ∧ (rowAt 339 = data_339 ∧ Good (rowAt 339) ∧ EntryGood 339) ∧ True := by
  exact ⟨⟨row_336, good_336, entry_good_336⟩, ⟨row_337, good_337, entry_good_337⟩, ⟨row_338, good_338, entry_good_338⟩, ⟨row_339, good_339, entry_good_339⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
