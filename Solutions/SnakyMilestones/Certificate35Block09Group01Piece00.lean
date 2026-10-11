import Definitions.Def_Snaky35Cache09
import Solutions.SnakyMilestones.Certificate35Block09Group00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_296_checked : entryAt 296 = entry_296 := by
  rw [entry_chunk_14 10 (by decide)]
  decide +kernel
theorem row_296 : rowAt 296 = data_296 := by
  rw [rowAt, dif_neg (by decide : ¬ 296 < 6), entry_296_checked]
  change forkRow [placeRow ⟨107, 1, 4, 5⟩ (rowAt 107), placeRow ⟨209, 3, 3, 4⟩ (rowAt 209), placeRow ⟨65, 1, 4, 5⟩ (rowAt 65)] = data_296
  rw [row_107, row_209, row_65]
  apply row_ext <;> decide +kernel
theorem entry_good_296 : EntryGood 296 := by
  unfold EntryGood
  rw [entry_296_checked]
  decide +kernel
theorem good_296 : Good (rowAt 296) := by
  rw [row_296]
  unfold Good
  decide +kernel

theorem entry_297_checked : entryAt 297 = entry_297 := by
  rw [entry_chunk_14 11 (by decide)]
  decide +kernel
theorem row_297 : rowAt 297 = data_297 := by
  rw [rowAt, dif_neg (by decide : ¬ 297 < 6), entry_297_checked]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (rowAt 6), placeRow ⟨289, 1, 7, 4⟩ (rowAt 289)] = data_297
  rw [row_6, row_289]
  apply row_ext <;> decide +kernel
theorem entry_good_297 : EntryGood 297 := by
  unfold EntryGood
  rw [entry_297_checked]
  decide +kernel
theorem good_297 : Good (rowAt 297) := by
  rw [row_297]
  unfold Good
  decide +kernel

theorem entry_298_checked : entryAt 298 = entry_298 := by
  rw [entry_chunk_14 12 (by decide)]
  decide +kernel
theorem row_298 : rowAt 298 = data_298 := by
  rw [rowAt, dif_neg (by decide : ¬ 298 < 6), entry_298_checked]
  change forkRow [placeRow ⟨24, 2, 7, 3⟩ (rowAt 24), placeRow ⟨24, 6, 3, 3⟩ (rowAt 24), placeRow ⟨107, 4, 3, 4⟩ (rowAt 107), placeRow ⟨195, 0, 7, 4⟩ (rowAt 195)] = data_298
  rw [row_24, row_107, row_195]
  apply row_ext <;> decide +kernel
theorem entry_good_298 : EntryGood 298 := by
  unfold EntryGood
  rw [entry_298_checked]
  decide +kernel
theorem good_298 : Good (rowAt 298) := by
  rw [row_298]
  unfold Good
  decide +kernel

theorem entry_299_checked : entryAt 299 = entry_299 := by
  rw [entry_chunk_14 13 (by decide)]
  decide +kernel
theorem row_299 : rowAt 299 = data_299 := by
  rw [rowAt, dif_neg (by decide : ¬ 299 < 6), entry_299_checked]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (rowAt 6), placeRow ⟨284, 0, 4, 5⟩ (rowAt 284)] = data_299
  rw [row_6, row_284]
  apply row_ext <;> decide +kernel
theorem entry_good_299 : EntryGood 299 := by
  unfold EntryGood
  rw [entry_299_checked]
  decide +kernel
theorem good_299 : Good (rowAt 299) := by
  rw [row_299]
  unfold Good
  decide +kernel


theorem block09_group01_piece00_correct : (rowAt 296 = data_296 ∧ Good (rowAt 296) ∧ EntryGood 296) ∧ (rowAt 297 = data_297 ∧ Good (rowAt 297) ∧ EntryGood 297) ∧ (rowAt 298 = data_298 ∧ Good (rowAt 298) ∧ EntryGood 298) ∧ (rowAt 299 = data_299 ∧ Good (rowAt 299) ∧ EntryGood 299) ∧ True := by
  exact ⟨⟨row_296, good_296, entry_good_296⟩, ⟨row_297, good_297, entry_good_297⟩, ⟨row_298, good_298, entry_good_298⟩, ⟨row_299, good_299, entry_good_299⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
