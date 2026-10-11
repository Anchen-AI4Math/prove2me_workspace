import Definitions.Def_Snaky35Cache07
import Solutions.SnakyMilestones.Certificate35Part06
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_224_checked : entryAt 224 = entry_224 := by
  rw [entry_chunk_10 18 (by decide)]
  decide +kernel
theorem row_224 : rowAt 224 = data_224 := by
  rw [rowAt, dif_neg (by decide : ¬ 224 < 6), entry_224_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨212, 0, 6, 3⟩ (rowAt 212)] = data_224
  rw [row_6, row_212]
  apply row_ext <;> decide +kernel
theorem entry_good_224 : EntryGood 224 := by
  unfold EntryGood
  rw [entry_224_checked]
  decide +kernel
theorem good_224 : Good (rowAt 224) := by
  rw [row_224]
  unfold Good
  decide +kernel

theorem entry_225_checked : entryAt 225 = entry_225 := by
  rw [entry_chunk_10 19 (by decide)]
  decide +kernel
theorem row_225 : rowAt 225 = data_225 := by
  rw [rowAt, dif_neg (by decide : ¬ 225 < 6), entry_225_checked]
  change forkRow [placeRow ⟨111, 7, 7, 5⟩ (rowAt 111), placeRow ⟨61, 4, 4, 5⟩ (rowAt 61)] = data_225
  rw [row_111, row_61]
  apply row_ext <;> decide +kernel
theorem entry_good_225 : EntryGood 225 := by
  unfold EntryGood
  rw [entry_225_checked]
  decide +kernel
theorem good_225 : Good (rowAt 225) := by
  rw [row_225]
  unfold Good
  decide +kernel

theorem entry_226_checked : entryAt 226 = entry_226 := by
  rw [entry_chunk_11 0 (by decide)]
  decide +kernel
theorem row_226 : rowAt 226 = data_226 := by
  rw [rowAt, dif_neg (by decide : ¬ 226 < 6), entry_226_checked]
  change forkRow [placeRow ⟨10, 6, 0, 3⟩ (rowAt 10), placeRow ⟨203, 0, 5, 4⟩ (rowAt 203), placeRow ⟨33, 0, 2, 3⟩ (rowAt 33), placeRow ⟨193, 0, 2, 4⟩ (rowAt 193)] = data_226
  rw [row_10, row_203, row_33, row_193]
  apply row_ext <;> decide +kernel
theorem entry_good_226 : EntryGood 226 := by
  unfold EntryGood
  rw [entry_226_checked]
  decide +kernel
theorem good_226 : Good (rowAt 226) := by
  rw [row_226]
  unfold Good
  decide +kernel

theorem entry_227_checked : entryAt 227 = entry_227 := by
  rw [entry_chunk_11 1 (by decide)]
  decide +kernel
theorem row_227 : rowAt 227 = data_227 := by
  rw [rowAt, dif_neg (by decide : ¬ 227 < 6), entry_227_checked]
  change forkRow [placeRow ⟨6, 1, 5, 5⟩ (rowAt 6), placeRow ⟨212, 0, 7, 3⟩ (rowAt 212)] = data_227
  rw [row_6, row_212]
  apply row_ext <;> decide +kernel
theorem entry_good_227 : EntryGood 227 := by
  unfold EntryGood
  rw [entry_227_checked]
  decide +kernel
theorem good_227 : Good (rowAt 227) := by
  rw [row_227]
  unfold Good
  decide +kernel


theorem block07_group00_piece00_correct : (rowAt 224 = data_224 ∧ Good (rowAt 224) ∧ EntryGood 224) ∧ (rowAt 225 = data_225 ∧ Good (rowAt 225) ∧ EntryGood 225) ∧ (rowAt 226 = data_226 ∧ Good (rowAt 226) ∧ EntryGood 226) ∧ (rowAt 227 = data_227 ∧ Good (rowAt 227) ∧ EntryGood 227) ∧ True := by
  exact ⟨⟨row_224, good_224, entry_good_224⟩, ⟨row_225, good_225, entry_good_225⟩, ⟨row_226, good_226, entry_good_226⟩, ⟨row_227, good_227, entry_good_227⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
