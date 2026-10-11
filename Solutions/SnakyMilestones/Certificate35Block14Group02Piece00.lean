import Definitions.Def_Snaky35Cache14
import Solutions.SnakyMilestones.Certificate35Block14Group01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_464_checked : entryAt 464 = entry_464 := by
  rw [entry_chunk_22 18 (by decide)]
  decide +kernel
theorem row_464 : rowAt 464 = data_464 := by
  rw [rowAt, dif_neg (by decide : ¬ 464 < 6), entry_464_checked]
  change forkRow [placeRow ⟨63, 0, 3, 5⟩ (rowAt 63), placeRow ⟨224, 0, 5, 4⟩ (rowAt 224), placeRow ⟨315, 0, 7, 3⟩ (rowAt 315), placeRow ⟨306, 0, 5, 5⟩ (rowAt 306), placeRow ⟨358, 0, 7, 3⟩ (rowAt 358), placeRow ⟨461, 0, 5, 5⟩ (rowAt 461)] = data_464
  rw [row_63, row_224, row_315, row_306, row_358, row_461]
  apply row_ext <;> decide +kernel
theorem entry_good_464 : EntryGood 464 := by
  unfold EntryGood
  rw [entry_464_checked]
  decide +kernel
theorem good_464 : Good (rowAt 464) := by
  rw [row_464]
  unfold Good
  decide +kernel

theorem entry_465_checked : entryAt 465 = entry_465 := by
  rw [entry_chunk_22 19 (by decide)]
  decide +kernel
theorem row_465 : rowAt 465 = data_465 := by
  rw [rowAt, dif_neg (by decide : ¬ 465 < 6), entry_465_checked]
  change forkRow [placeRow ⟨55, 3, 4, 5⟩ (rowAt 55), placeRow ⟨285, 0, 3, 4⟩ (rowAt 285), placeRow ⟨64, 1, 3, 1⟩ (rowAt 64)] = data_465
  rw [row_55, row_285, row_64]
  apply row_ext <;> decide +kernel
theorem entry_good_465 : EntryGood 465 := by
  unfold EntryGood
  rw [entry_465_checked]
  decide +kernel
theorem good_465 : Good (rowAt 465) := by
  rw [row_465]
  unfold Good
  decide +kernel

theorem entry_466_checked : entryAt 466 = entry_466 := by
  rw [entry_chunk_23 0 (by decide)]
  decide +kernel
theorem row_466 : rowAt 466 = data_466 := by
  rw [rowAt, dif_neg (by decide : ¬ 466 < 6), entry_466_checked]
  change forkRow [placeRow ⟨395, 4, 3, 4⟩ (rowAt 395), placeRow ⟨360, 4, 2, 6⟩ (rowAt 360), placeRow ⟨417, 1, 5, 4⟩ (rowAt 417), placeRow ⟨325, 4, 3, 4⟩ (rowAt 325), placeRow ⟨324, 4, 3, 5⟩ (rowAt 324)] = data_466
  rw [row_395, row_360, row_417, row_325, row_324]
  apply row_ext <;> decide +kernel
theorem entry_good_466 : EntryGood 466 := by
  unfold EntryGood
  rw [entry_466_checked]
  decide +kernel
theorem good_466 : Good (rowAt 466) := by
  rw [row_466]
  unfold Good
  decide +kernel

theorem entry_467_checked : entryAt 467 = entry_467 := by
  rw [entry_chunk_23 1 (by decide)]
  decide +kernel
theorem row_467 : rowAt 467 = data_467 := by
  rw [rowAt, dif_neg (by decide : ¬ 467 < 6), entry_467_checked]
  change forkRow [placeRow ⟨64, 7, 5, 7⟩ (rowAt 64), placeRow ⟨314, 6, 5, 4⟩ (rowAt 314), placeRow ⟨443, 1, 5, 7⟩ (rowAt 443)] = data_467
  rw [row_64, row_314, row_443]
  apply row_ext <;> decide +kernel
theorem entry_good_467 : EntryGood 467 := by
  unfold EntryGood
  rw [entry_467_checked]
  decide +kernel
theorem good_467 : Good (rowAt 467) := by
  rw [row_467]
  unfold Good
  decide +kernel


theorem block14_group02_piece00_correct : (rowAt 464 = data_464 ∧ Good (rowAt 464) ∧ EntryGood 464) ∧ (rowAt 465 = data_465 ∧ Good (rowAt 465) ∧ EntryGood 465) ∧ (rowAt 466 = data_466 ∧ Good (rowAt 466) ∧ EntryGood 466) ∧ (rowAt 467 = data_467 ∧ Good (rowAt 467) ∧ EntryGood 467) ∧ True := by
  exact ⟨⟨row_464, good_464, entry_good_464⟩, ⟨row_465, good_465, entry_good_465⟩, ⟨row_466, good_466, entry_good_466⟩, ⟨row_467, good_467, entry_good_467⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
