import Definitions.Def_Snaky21Data10
import Solutions.Snaky21.Geometry
import Solutions.Snaky21.Certificate09

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace OAI.Snaky21.Certificate
open OAI.Snaky21 OAI.SnakyPrototype

theorem eq_inline_588 : inline_588 = combine (5, 6) [placed 1 (4, 3) card_5, placed 0 (2, 5) card_90] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_588 : Valid inline_588 := by
  rw [eq_inline_588]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (4, 3) valid_5
  subst c
  exact placed_valid 0 (2, 5) valid_90

theorem eq_inline_589 : inline_589 = combine (2, 6) [placed 5 (1, 6) card_44, placed 3 (5, 3) card_260, inline_588] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_589 : Valid inline_589 := by
  rw [eq_inline_589]
  apply combination_rule (2, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 6) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 3) valid_260
  subst c
  exact valid_inline_588

theorem eq_inline_590 : inline_590 = combine (4, 6) [placed 3 (4, 3) card_5, inline_589] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_590 : Valid inline_590 := by
  rw [eq_inline_590]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (4, 3) valid_5
  subst c
  exact valid_inline_589

theorem eq_inline_591 : inline_591 = combine (3, 6) [placed 4 (4, 2) card_61, placed 2 (3, 6) card_89, placed 3 (6, 2) card_183, inline_590] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_591 : Valid inline_591 := by
  rw [eq_inline_591]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_61
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 6) valid_89
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 2) valid_183
  subst c
  exact valid_inline_590

theorem eq_card_640 : card_640 = combine (4, 5) [placed 0 (3, 2) card_10, placed 5 (2, 6) card_47, placed 6 (4, 6) card_52, inline_591] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_640 : Valid card_640 := by
  rw [eq_card_640]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 6) valid_47
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 6) valid_52
  subst c
  exact valid_inline_591

theorem eq_inline_592 : inline_592 = combine (3, 4) [placed 0 (2, 0) card_14, placed 1 (0, 3) card_44, placed 4 (4, 1) card_60] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_592 : Valid inline_592 := by
  rw [eq_inline_592]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 0) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_44
  subst c
  exact placed_valid 4 (4, 1) valid_60

theorem eq_card_641 : card_641 = combine (2, 3) [placed 5 (0, 3) card_52, placed 0 (1, 1) card_144, inline_592] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_641 : Valid card_641 := by
  rw [eq_card_641]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_144
  subst c
  exact valid_inline_592

theorem eq_card_642 : card_642 = combine (3, 5) [placed 0 (0, 1) card_299, placed 0 (0, 1) card_349, placed 0 (0, 1) card_476, placed 0 (1, 1) card_587, placed 2 (1, 8) card_587, placed 5 (0, 5) card_612, placed 0 (0, 2) card_641] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_642 : Valid card_642 := by
  rw [eq_card_642]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_299
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_349
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_476
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_587
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 8) valid_587
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_612
  subst c
  exact placed_valid 0 (0, 2) valid_641

theorem eq_card_643 : card_643 = combine (3, 5) [placed 2 (0, 8) card_299, placed 2 (0, 8) card_349, placed 2 (0, 8) card_476, placed 0 (1, 1) card_587, placed 2 (1, 8) card_587, placed 1 (0, 4) card_612, placed 2 (0, 7) card_641] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_643 : Valid card_643 := by
  rw [eq_card_643]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 8) valid_299
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 8) valid_349
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 8) valid_476
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_587
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 8) valid_587
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 4) valid_612
  subst c
  exact placed_valid 2 (0, 7) valid_641

theorem eq_inline_593 : inline_593 = combine (5, 5) [placed 3 (7, 4) card_10, placed 0 (3, 1) card_317, placed 2 (2, 8) card_640] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_593 : Valid inline_593 := by
  rw [eq_inline_593]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 4) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_317
  subst c
  exact placed_valid 2 (2, 8) valid_640

theorem eq_inline_594 : inline_594 = combine (6, 5) [placed 1 (1, 4) card_104, placed 1 (1, 4) card_359, placed 0 (1, 1) card_452, placed 2 (3, 8) card_476, placed 0 (3, 1) card_479, inline_593] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_594 : Valid inline_594 := by
  rw [eq_inline_594]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 4) valid_104
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 4) valid_359
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_452
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 8) valid_476
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_479
  subst c
  exact valid_inline_593

theorem eq_card_644 : card_644 = combine (6, 4) [placed 6 (7, 7) card_120, placed 5 (1, 6) card_338, placed 5 (1, 7) card_437, placed 5 (0, 6) card_611, placed 1 (1, 3) card_613, placed 0 (1, 0) card_634, inline_594, placed 0 (3, 0) card_642, placed 0 (3, 0) card_643] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_644 : Valid card_644 := by
  rw [eq_card_644]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 7) valid_120
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 6) valid_338
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 7) valid_437
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 6) valid_611
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 3) valid_613
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_634
  rcases hc with rfl | hc
  · exact valid_inline_594
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 0) valid_642
  subst c
  exact placed_valid 0 (3, 0) valid_643

theorem eq_inline_595 : inline_595 = combine (5, 4) [placed 3 (7, 4) card_44, placed 3 (7, 4) card_52, placed 5 (2, 5) card_128, placed 6 (6, 6) card_144] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_595 : Valid inline_595 := by
  rw [eq_inline_595]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 4) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 4) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 5) valid_128
  subst c
  exact placed_valid 6 (6, 6) valid_144

theorem eq_inline_596 : inline_596 = combine (6, 5) [placed 1 (1, 4) card_104, placed 1 (1, 4) card_359, placed 2 (1, 8) card_438, placed 0 (1, 1) card_452, placed 2 (3, 8) card_476, placed 0 (3, 1) card_479] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_596 : Valid inline_596 := by
  rw [eq_inline_596]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 4) valid_104
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 4) valid_359
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 8) valid_438
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_452
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 8) valid_476
  subst c
  exact placed_valid 0 (3, 1) valid_479

theorem eq_card_645 : card_645 = combine (6, 4) [placed 6 (7, 7) card_120, placed 5 (1, 6) card_276, placed 5 (1, 6) card_338, placed 5 (1, 7) card_437, placed 5 (0, 6) card_611, placed 0 (1, 0) card_634, placed 0 (3, 0) card_642, placed 0 (3, 0) card_643, inline_595, inline_596] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_645 : Valid card_645 := by
  rw [eq_card_645]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 7) valid_120
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 6) valid_276
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 6) valid_338
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 7) valid_437
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 6) valid_611
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_634
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 0) valid_642
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 0) valid_643
  rcases hc with rfl | hc
  · exact valid_inline_595
  subst c
  exact valid_inline_596

theorem eq_inline_597 : inline_597 = combine (4, 2) [placed 4 (4, 1) card_15, placed 1 (2, 2) card_72, placed 7 (6, 5) card_262] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_597 : Valid inline_597 := by
  rw [eq_inline_597]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_15
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 2) valid_72
  subst c
  exact placed_valid 7 (6, 5) valid_262

theorem eq_card_646 : card_646 = combine (4, 4) [placed 0 (1, 1) card_361, placed 3 (6, 1) card_361, placed 1 (0, 3) card_411, placed 3 (7, 1) card_600, placed 5 (0, 7) card_621, inline_597] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_646 : Valid card_646 := by
  rw [eq_card_646]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_361
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 1) valid_361
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_411
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 1) valid_600
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 7) valid_621
  subst c
  exact valid_inline_597

theorem eq_inline_598 : inline_598 = combine (6, 5) [placed 7 (7, 5) card_15, placed 3 (8, 4) card_65, placed 6 (6, 7) card_282] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_598 : Valid inline_598 := by
  rw [eq_inline_598]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 5) valid_15
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 4) valid_65
  subst c
  exact placed_valid 6 (6, 7) valid_282

theorem eq_inline_599 : inline_599 = combine (5, 5) [placed 3 (8, 2) card_600, placed 2 (2, 8) card_600, placed 1 (1, 1) card_621, inline_598] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_599 : Valid inline_599 := by
  rw [eq_inline_599]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 2) valid_600
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 8) valid_600
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_621
  subst c
  exact valid_inline_598

theorem eq_card_647 : card_647 = combine (5, 4) [placed 7 (8, 6) card_399, placed 5 (1, 5) card_408, placed 5 (1, 5) card_410, placed 3 (9, 1) card_480, placed 1 (0, 3) card_546, placed 5 (1, 6) card_587, placed 7 (9, 6) card_635, placed 1 (1, 1) card_646, inline_599] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_647 : Valid card_647 := by
  rw [eq_card_647]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 6) valid_399
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 5) valid_408
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 5) valid_410
  rcases hc with rfl | hc
  · exact placed_valid 3 (9, 1) valid_480
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_546
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 6) valid_587
  rcases hc with rfl | hc
  · exact placed_valid 7 (9, 6) valid_635
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_646
  subst c
  exact valid_inline_599

theorem eq_card_648 : card_648 = combine (4, 4) [placed 0 (1, 1) card_174, placed 0 (2, 1) card_475, placed 0 (1, 0) card_480, placed 4 (7, 0) card_480, placed 2 (2, 8) card_483, placed 0 (1, 1) card_566, placed 0 (2, 1) card_587, placed 2 (2, 8) card_587, placed 1 (1, 2) card_605, placed 0 (2, 0) card_635, placed 0 (0, 0) card_644, placed 0 (0, 0) card_647] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_648 : Valid card_648 := by
  rw [eq_card_648]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_174
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_475
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_480
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 0) valid_480
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 8) valid_483
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_566
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_587
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 8) valid_587
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_605
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 0) valid_635
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_644
  subst c
  exact placed_valid 0 (0, 0) valid_647

theorem eq_inline_600 : inline_600 = combine (1, 3) [placed 0 (0, 3) card_0, placed 4 (4, 2) card_78] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_600 : Valid inline_600 := by
  rw [eq_inline_600]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 3) valid_0
  subst c
  exact placed_valid 4 (4, 2) valid_78

theorem eq_inline_601 : inline_601 = combine (2, 3) [placed 7 (3, 6) card_5, inline_600] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_601 : Valid inline_601 := by
  rw [eq_inline_601]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (3, 6) valid_5
  subst c
  exact valid_inline_600

theorem eq_inline_602 : inline_602 = combine (3, 4) [placed 3 (3, 3) card_5, inline_601] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_602 : Valid inline_602 := by
  rw [eq_inline_602]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (3, 3) valid_5
  subst c
  exact valid_inline_601

theorem eq_inline_603 : inline_603 = combine (2, 6) [placed 3 (5, 5) card_15, inline_602] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_603 : Valid inline_603 := by
  rw [eq_inline_603]
  apply combination_rule (2, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 5) valid_15
  subst c
  exact valid_inline_602

theorem eq_inline_604 : inline_604 = combine (3, 3) [placed 7 (4, 6) card_5, inline_603] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_604 : Valid inline_604 := by
  rw [eq_inline_604]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 6) valid_5
  subst c
  exact valid_inline_603

theorem eq_inline_605 : inline_605 = combine (3, 6) [placed 3 (4, 3) card_5, inline_604] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_605 : Valid inline_605 := by
  rw [eq_inline_605]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (4, 3) valid_5
  subst c
  exact valid_inline_604

theorem eq_inline_606 : inline_606 = combine (4, 6) [placed 0 (3, 2) card_19, placed 0 (3, 2) card_84, placed 1 (3, 3) card_314, inline_605] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_606 : Valid inline_606 := by
  rw [eq_inline_606]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_19
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_84
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 3) valid_314
  subst c
  exact valid_inline_605

theorem eq_inline_607 : inline_607 = combine (4, 3) [placed 2 (3, 6) card_10, placed 4 (4, 2) card_44, placed 2 (3, 6) card_63, inline_606] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_607 : Valid inline_607 := by
  rw [eq_inline_607]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 6) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 6) valid_63
  subst c
  exact valid_inline_606

theorem eq_card_649 : card_649 = combine (4, 4) [placed 5 (1, 5) card_52, placed 0 (1, 1) card_523, inline_607] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_649 : Valid card_649 := by
  rw [eq_card_649]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 5) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_523
  subst c
  exact valid_inline_607

theorem eq_inline_608 : inline_608 = combine (5, 4) [placed 5 (2, 5) card_52, placed 4 (6, 0) card_545] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_608 : Valid inline_608 := by
  rw [eq_inline_608]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 5) valid_52
  subst c
  exact placed_valid 4 (6, 0) valid_545

theorem eq_card_650 : card_650 = combine (5, 5) [placed 1 (1, 4) card_13, placed 1 (1, 4) card_14, placed 2 (2, 8) card_257, placed 2 (2, 8) card_435, placed 0 (2, 2) card_507, placed 2 (1, 10) card_649, inline_608] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_650 : Valid card_650 := by
  rw [eq_card_650]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 4) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 4) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 8) valid_257
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 8) valid_435
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_507
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 10) valid_649
  subst c
  exact valid_inline_608

theorem eq_inline_609 : inline_609 = combine (3, 5) [placed 3 (6, 3) card_55, placed 7 (6, 6) card_56] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_609 : Valid inline_609 := by
  rw [eq_inline_609]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 3) valid_55
  subst c
  exact placed_valid 7 (6, 6) valid_56

theorem eq_inline_610 : inline_610 = combine (3, 5) [placed 4 (4, 3) card_20, placed 0 (3, 3) card_29, placed 3 (5, 3) card_46] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_610 : Valid inline_610 := by
  rw [eq_inline_610]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 3) valid_20
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 3) valid_29
  subst c
  exact placed_valid 3 (5, 3) valid_46

theorem eq_inline_611 : inline_611 = combine (4, 3) [placed 7 (7, 5) card_85, placed 4 (4, 3) card_94] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_611 : Valid inline_611 := by
  rw [eq_inline_611]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 5) valid_85
  subst c
  exact placed_valid 4 (4, 3) valid_94

theorem eq_card_651 : card_651 = combine (3, 6) [inline_609, inline_610, inline_611] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_651 : Valid card_651 := by
  rw [eq_card_651]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact valid_inline_609
  rcases hc with rfl | hc
  · exact valid_inline_610
  subst c
  exact valid_inline_611

theorem eq_inline_612 : inline_612 = combine (3, 5) [placed 6 (5, 5) card_0, placed 4 (5, 2) card_245] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_612 : Valid inline_612 := by
  rw [eq_inline_612]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 5) valid_0
  subst c
  exact placed_valid 4 (5, 2) valid_245

theorem eq_inline_613 : inline_613 = combine (4, 5) [placed 1 (1, 4) card_36, placed 6 (4, 6) card_44, inline_612] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_613 : Valid inline_613 := by
  rw [eq_inline_613]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 4) valid_36
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 6) valid_44
  subst c
  exact valid_inline_612

theorem eq_inline_614 : inline_614 = combine (4, 4) [placed 5 (0, 5) card_222, inline_613] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_614 : Valid inline_614 := by
  rw [eq_inline_614]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_222
  subst c
  exact valid_inline_613

theorem eq_inline_615 : inline_615 = combine (2, 5) [placed 4 (3, 2) card_10, placed 1 (0, 3) card_558, inline_614] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_615 : Valid inline_615 := by
  rw [eq_inline_615]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 2) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_558
  subst c
  exact valid_inline_614

theorem eq_card_652 : card_652 = combine (4, 3) [placed 4 (5, 3) card_0, inline_615] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_652 : Valid card_652 := by
  rw [eq_card_652]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 3) valid_0
  subst c
  exact valid_inline_615

theorem eq_inline_616 : inline_616 = combine (4, 4) [placed 1 (0, 3) card_206, placed 0 (2, 1) card_301, placed 3 (5, 3) card_405] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_616 : Valid inline_616 := by
  rw [eq_inline_616]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_206
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_301
  subst c
  exact placed_valid 3 (5, 3) valid_405

theorem eq_card_653 : card_653 = combine (2, 4) [placed 5 (0, 4) card_53, placed 3 (6, 3) card_53, placed 0 (1, 0) card_652, inline_616] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_653 : Valid card_653 := by
  rw [eq_card_653]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_53
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 3) valid_53
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_652
  subst c
  exact valid_inline_616

theorem eq_inline_617 : inline_617 = combine (4, 6) [placed 7 (4, 7) card_0, placed 5 (1, 7) card_502] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_617 : Valid inline_617 := by
  rw [eq_inline_617]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 7) valid_0
  subst c
  exact placed_valid 5 (1, 7) valid_502

theorem eq_inline_618 : inline_618 = combine (4, 5) [placed 0 (3, 1) card_53, placed 6 (4, 7) card_53, placed 6 (7, 8) card_651, inline_617] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_618 : Valid inline_618 := by
  rw [eq_inline_618]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_53
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 7) valid_53
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 8) valid_651
  subst c
  exact valid_inline_617

theorem eq_card_654 : card_654 = combine (4, 4) [placed 1 (0, 2) card_248, placed 1 (0, 2) card_300, placed 1 (0, 1) card_436, placed 2 (1, 7) card_449, placed 0 (1, 1) card_509, placed 2 (1, 7) card_510, placed 5 (0, 7) card_653, inline_618] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_654 : Valid card_654 := by
  rw [eq_card_654]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_248
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_300
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_436
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 7) valid_449
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_509
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 7) valid_510
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 7) valid_653
  subst c
  exact valid_inline_618

theorem eq_inline_619 : inline_619 = combine (3, 6) [placed 3 (5, 2) card_179, placed 1 (2, 3) card_314, placed 7 (5, 7) card_344] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_619 : Valid inline_619 := by
  rw [eq_inline_619]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 2) valid_179
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 3) valid_314
  subst c
  exact placed_valid 7 (5, 7) valid_344

theorem eq_card_655 : card_655 = combine (3, 3) [placed 2 (2, 6) card_10, placed 4 (3, 2) card_52, placed 7 (6, 6) card_435, inline_619] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_655 : Valid card_655 := by
  rw [eq_card_655]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 6) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 2) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 6) valid_435
  subst c
  exact valid_inline_619

theorem eq_inline_620 : inline_620 = combine (5, 4) [placed 1 (2, 3) card_117, placed 5 (3, 7) card_134, placed 5 (3, 7) card_180, placed 6 (6, 9) card_337, placed 6 (8, 9) card_341, placed 5 (2, 7) card_435, placed 5 (3, 6) card_558] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_620 : Valid inline_620 := by
  rw [eq_inline_620]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 3) valid_117
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 7) valid_134
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 7) valid_180
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 9) valid_337
  rcases hc with rfl | hc
  · exact placed_valid 6 (8, 9) valid_341
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 7) valid_435
  subst c
  exact placed_valid 5 (3, 6) valid_558

theorem eq_inline_621 : inline_621 = combine (4, 5) [placed 0 (2, 5) card_1, placed 1 (1, 2) card_651] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_621 : Valid inline_621 := by
  rw [eq_inline_621]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 5) valid_1
  subst c
  exact placed_valid 1 (1, 2) valid_651

theorem eq_inline_622 : inline_622 = combine (4, 5) [placed 0 (2, 5) card_1, placed 2 (3, 9) card_652] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_622 : Valid inline_622 := by
  rw [eq_inline_622]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 5) valid_1
  subst c
  exact placed_valid 2 (3, 9) valid_652

theorem eq_inline_623 : inline_623 = combine (5, 5) [placed 6 (7, 9) card_248, placed 6 (7, 9) card_300, placed 6 (8, 9) card_436, placed 5 (2, 8) card_449, placed 5 (2, 8) card_510, inline_620, inline_621, inline_622] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_623 : Valid inline_623 := by
  rw [eq_inline_623]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 9) valid_248
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 9) valid_300
  rcases hc with rfl | hc
  · exact placed_valid 6 (8, 9) valid_436
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 8) valid_449
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 8) valid_510
  rcases hc with rfl | hc
  · exact valid_inline_620
  rcases hc with rfl | hc
  · exact valid_inline_621
  subst c
  exact valid_inline_622

theorem eq_card_656 : card_656 = combine (6, 6) [placed 0 (3, 3) card_508, placed 2 (3, 9) card_508, placed 0 (3, 3) card_605, placed 2 (3, 9) card_605, placed 3 (10, 2) card_644, placed 3 (10, 2) card_645, placed 3 (10, 2) card_647, placed 0 (2, 1) card_650, placed 2 (2, 11) card_650, inline_623, placed 3 (9, 3) card_654] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_656 : Valid card_656 := by
  rw [eq_card_656]
  apply combination_rule (6, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 3) valid_508
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 9) valid_508
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 3) valid_605
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 9) valid_605
  rcases hc with rfl | hc
  · exact placed_valid 3 (10, 2) valid_644
  rcases hc with rfl | hc
  · exact placed_valid 3 (10, 2) valid_645
  rcases hc with rfl | hc
  · exact placed_valid 3 (10, 2) valid_647
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_650
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 11) valid_650
  rcases hc with rfl | hc
  · exact valid_inline_623
  subst c
  exact placed_valid 3 (9, 3) valid_654

theorem eq_inline_624 : inline_624 = combine (2, 4) [placed 5 (1, 4) card_54, placed 4 (5, 1) card_79] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_624 : Valid inline_624 := by
  rw [eq_inline_624]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_54
  subst c
  exact placed_valid 4 (5, 1) valid_79

theorem eq_inline_625 : inline_625 = combine (4, 2) [placed 1 (1, 2) card_54, placed 4 (5, 1) card_71, placed 1 (2, 1) card_345] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_625 : Valid inline_625 := by
  rw [eq_inline_625]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_54
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 1) valid_71
  subst c
  exact placed_valid 1 (2, 1) valid_345

theorem eq_inline_626 : inline_626 = combine (6, 3) [placed 2 (3, 4) card_5, placed 2 (3, 5) card_445] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_626 : Valid inline_626 := by
  rw [eq_inline_626]
  apply combination_rule (6, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 4) valid_5
  subst c
  exact placed_valid 2 (3, 5) valid_445

theorem eq_inline_627 : inline_627 = combine (6, 4) [placed 1 (3, 3) card_20, placed 5 (3, 4) card_29, inline_626] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_627 : Valid inline_627 := by
  rw [eq_inline_627]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 3) valid_20
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 4) valid_29
  subst c
  exact valid_inline_626

theorem eq_inline_628 : inline_628 = combine (3, 4) [placed 5 (2, 4) card_15, placed 1 (1, 3) card_65, inline_627] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_628 : Valid inline_628 := by
  rw [eq_inline_628]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 4) valid_15
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 3) valid_65
  subst c
  exact valid_inline_627

theorem eq_inline_629 : inline_629 = combine (5, 4) [placed 3 (8, 2) card_85, placed 2 (3, 7) card_85, placed 2 (4, 7) card_411, placed 3 (8, 2) card_537, inline_628] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_629 : Valid inline_629 := by
  rw [eq_inline_629]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 2) valid_85
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_85
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 7) valid_411
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 2) valid_537
  subst c
  exact valid_inline_628

theorem eq_inline_630 : inline_630 = combine (4, 4) [placed 1 (1, 1) card_510, placed 0 (1, 0) card_631, placed 1 (1, 0) card_653, inline_624, inline_625, inline_629] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_630 : Valid inline_630 := by
  rw [eq_inline_630]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_510
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_631
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 0) valid_653
  rcases hc with rfl | hc
  · exact valid_inline_624
  rcases hc with rfl | hc
  · exact valid_inline_625
  subst c
  exact valid_inline_629

theorem eq_card_657 : card_657 = combine (4, 3) [placed 1 (1, 2) card_50, placed 1 (1, 2) card_125, placed 0 (1, 1) card_478, placed 0 (1, 1) card_482, inline_630] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_657 : Valid card_657 := by
  rw [eq_card_657]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_50
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_125
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_478
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_482
  subst c
  exact valid_inline_630

theorem eq_inline_631 : inline_631 = combine (2, 6) [placed 1 (1, 3) card_314, placed 5 (0, 6) card_378] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_631 : Valid inline_631 := by
  rw [eq_inline_631]
  apply combination_rule (2, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 3) valid_314
  subst c
  exact placed_valid 5 (0, 6) valid_378

theorem eq_card_658 : card_658 = combine (2, 3) [placed 6 (2, 6) card_27, placed 4 (2, 2) card_52, placed 2 (1, 9) card_284, inline_631] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_658 : Valid card_658 := by
  rw [eq_card_658]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (2, 6) valid_27
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 2) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 9) valid_284
  subst c
  exact valid_inline_631

theorem eq_card_659 : card_659 = combine (3, 4) [placed 2 (0, 5) card_5, placed 0 (1, 0) card_658] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_659 : Valid card_659 := by
  rw [eq_card_659]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 5) valid_5
  subst c
  exact placed_valid 0 (1, 0) valid_658

theorem eq_inline_632 : inline_632 = combine (7, 5) [placed 3 (7, 5) card_6, placed 1 (4, 4) card_18] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_632 : Valid inline_632 := by
  rw [eq_inline_632]
  apply combination_rule (7, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 5) valid_6
  subst c
  exact placed_valid 1 (4, 4) valid_18

theorem eq_inline_633 : inline_633 = combine (7, 5) [placed 3 (7, 5) card_6, placed 0 (3, 2) card_252] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_633 : Valid inline_633 := by
  rw [eq_inline_633]
  apply combination_rule (7, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 5) valid_6
  subst c
  exact placed_valid 0 (3, 2) valid_252

theorem eq_inline_634 : inline_634 = combine (6, 5) [placed 5 (2, 6) card_9, inline_632, placed 0 (3, 0) card_659, inline_633] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_634 : Valid inline_634 := by
  rw [eq_inline_634]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 6) valid_9
  rcases hc with rfl | hc
  · exact valid_inline_632
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 0) valid_659
  subst c
  exact valid_inline_633

theorem eq_card_660 : card_660 = combine (3, 5) [placed 3 (7, 4) card_13, placed 4 (6, 3) card_137, placed 6 (6, 8) card_332, inline_634] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_660 : Valid card_660 := by
  rw [eq_card_660]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 4) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 3) valid_137
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 8) valid_332
  subst c
  exact valid_inline_634

theorem eq_inline_635 : inline_635 = combine (4, 3) [placed 6 (5, 7) card_9, placed 7 (7, 6) card_115, placed 7 (7, 7) card_302, placed 7 (7, 7) card_303] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_635 : Valid inline_635 := by
  rw [eq_inline_635]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 7) valid_9
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 6) valid_115
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 7) valid_302
  subst c
  exact placed_valid 7 (7, 7) valid_303

theorem eq_card_661 : card_661 = combine (4, 6) [placed 0 (3, 2) card_13, placed 4 (5, 2) card_14, placed 0 (3, 2) card_33, placed 1 (1, 3) card_116, inline_635] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_661 : Valid card_661 := by
  rw [eq_card_661]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 2) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_33
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 3) valid_116
  subst c
  exact valid_inline_635

theorem eq_inline_636 : inline_636 = combine (1, 5) [placed 2 (1, 5) card_5, placed 4 (4, 2) card_141] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_636 : Valid inline_636 := by
  rw [eq_inline_636]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 5) valid_5
  subst c
  exact placed_valid 4 (4, 2) valid_141

theorem eq_card_662 : card_662 = combine (4, 4) [placed 5 (1, 5) card_52, placed 0 (2, 0) card_658, inline_636] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_662 : Valid card_662 := by
  rw [eq_card_662]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 5) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 0) valid_658
  subst c
  exact valid_inline_636

theorem eq_card_663 : card_663 = combine (4, 5) [placed 2 (1, 7) card_134, placed 2 (1, 7) card_180, placed 2 (1, 8) card_435, placed 0 (1, 2) card_507, placed 2 (2, 7) card_558, placed 2 (1, 9) card_562, placed 0 (1, 3) card_580, placed 0 (0, 0) card_662] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_663 : Valid card_663 := by
  rw [eq_card_663]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 7) valid_134
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 7) valid_180
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 8) valid_435
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_507
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_558
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 9) valid_562
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 3) valid_580
  subst c
  exact placed_valid 0 (0, 0) valid_662

theorem eq_card_664 : card_664 = combine (6, 5) [placed 2 (3, 7) card_134, placed 2 (3, 7) card_180, placed 4 (7, 2) card_309, placed 2 (3, 8) card_435, placed 2 (4, 7) card_558, placed 0 (3, 3) card_580, placed 0 (2, 0) card_662] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_664 : Valid card_664 := by
  rw [eq_card_664]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_134
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_180
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 2) valid_309
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 8) valid_435
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 7) valid_558
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 3) valid_580
  subst c
  exact placed_valid 0 (2, 0) valid_662

theorem eq_inline_637 : inline_637 = combine (4, 7) [placed 6 (4, 7) card_70, placed 0 (3, 3) card_106, placed 0 (3, 3) card_269, placed 1 (0, 4) card_322] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_637 : Valid inline_637 := by
  rw [eq_inline_637]
  apply combination_rule (4, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 7) valid_70
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 3) valid_106
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 3) valid_269
  subst c
  exact placed_valid 1 (0, 4) valid_322

theorem eq_inline_638 : inline_638 = combine (4, 7) [placed 6 (4, 7) card_70, placed 3 (7, 4) card_257, placed 3 (7, 4) card_435] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_638 : Valid inline_638 := by
  rw [eq_inline_638]
  apply combination_rule (4, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 7) valid_70
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 4) valid_257
  subst c
  exact placed_valid 3 (7, 4) valid_435

theorem eq_inline_639 : inline_639 = combine (3, 7) [placed 7 (3, 7) card_4, placed 3 (4, 4) card_93] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_639 : Valid inline_639 := by
  rw [eq_inline_639]
  apply combination_rule (3, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (3, 7) valid_4
  subst c
  exact placed_valid 3 (4, 4) valid_93

theorem eq_inline_640 : inline_640 = combine (3, 4) [placed 7 (3, 6) card_5, inline_639] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_640 : Valid inline_640 := by
  rw [eq_inline_640]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (3, 6) valid_5
  subst c
  exact valid_inline_639

theorem eq_inline_641 : inline_641 = combine (3, 5) [placed 6 (4, 7) card_40, placed 1 (0, 4) card_517, inline_640] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_641 : Valid inline_641 := by
  rw [eq_inline_641]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 7) valid_40
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 4) valid_517
  subst c
  exact valid_inline_640

theorem eq_card_665 : card_665 = combine (4, 5) [placed 0 (3, 1) card_459, placed 5 (1, 7) card_588, inline_637, inline_638, inline_641] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_665 : Valid card_665 := by
  rw [eq_card_665]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_459
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 7) valid_588
  rcases hc with rfl | hc
  · exact valid_inline_637
  rcases hc with rfl | hc
  · exact valid_inline_638
  subst c
  exact valid_inline_641

theorem eq_inline_642 : inline_642 = combine (1, 3) [placed 6 (4, 3) card_4, placed 0 (1, 2) card_314] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_642 : Valid inline_642 := by
  rw [eq_inline_642]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 3) valid_4
  subst c
  exact placed_valid 0 (1, 2) valid_314

theorem eq_inline_643 : inline_643 = combine (4, 3) [placed 1 (3, 0) card_5, inline_642] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_643 : Valid inline_643 := by
  rw [eq_inline_643]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 0) valid_5
  subst c
  exact valid_inline_642

theorem eq_card_666 : card_666 = combine (2, 3) [placed 3 (3, 0) card_5, inline_643] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_666 : Valid card_666 := by
  rw [eq_card_666]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (3, 0) valid_5
  subst c
  exact valid_inline_643

theorem eq_card_667 : card_667 = combine (3, 4) [placed 0 (3, 0) card_7, placed 4 (4, 0) card_9, placed 0 (0, 1) card_666] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_667 : Valid card_667 := by
  rw [eq_card_667]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 0) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 0) valid_9
  subst c
  exact placed_valid 0 (0, 1) valid_666

theorem eq_card_668 : card_668 = combine (3, 4) [placed 4 (3, 0) card_7, placed 0 (2, 0) card_9, placed 0 (0, 1) card_666] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_668 : Valid card_668 := by
  rw [eq_card_668]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 0) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 0) valid_9
  subst c
  exact placed_valid 0 (0, 1) valid_666

theorem eq_inline_644 : inline_644 = combine (5, 6) [placed 6 (7, 6) card_0, placed 7 (7, 7) card_66] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_644 : Valid inline_644 := by
  rw [eq_inline_644]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 6) valid_0
  subst c
  exact placed_valid 7 (7, 7) valid_66

theorem eq_inline_645 : inline_645 = combine (4, 6) [placed 7 (4, 8) card_0, inline_644] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_645 : Valid inline_645 := by
  rw [eq_inline_645]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 8) valid_0
  subst c
  exact valid_inline_644

theorem eq_inline_646 : inline_646 = combine (3, 7) [placed 2 (3, 7) card_5, placed 0 (3, 4) card_36] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_646 : Valid inline_646 := by
  rw [eq_inline_646]
  apply combination_rule (3, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_5
  subst c
  exact placed_valid 0 (3, 4) valid_36

theorem eq_inline_647 : inline_647 = combine (3, 7) [placed 4 (6, 6) card_24, placed 0 (3, 4) card_36] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_647 : Valid inline_647 := by
  rw [eq_inline_647]
  apply combination_rule (3, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 6) valid_24
  subst c
  exact placed_valid 0 (3, 4) valid_36

theorem eq_inline_648 : inline_648 = combine (4, 7) [placed 3 (7, 6) card_48, inline_645, inline_646, inline_647] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_648 : Valid inline_648 := by
  rw [eq_inline_648]
  apply combination_rule (4, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 6) valid_48
  rcases hc with rfl | hc
  · exact valid_inline_645
  rcases hc with rfl | hc
  · exact valid_inline_646
  subst c
  exact valid_inline_647

theorem eq_inline_649 : inline_649 = combine (5, 7) [placed 3 (6, 4) card_5, inline_648] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_649 : Valid inline_649 := by
  rw [eq_inline_649]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 4) valid_5
  subst c
  exact valid_inline_648

theorem eq_inline_650 : inline_650 = combine (4, 5) [placed 7 (7, 7) card_25, inline_649] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_650 : Valid inline_650 := by
  rw [eq_inline_650]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 7) valid_25
  subst c
  exact valid_inline_649

theorem eq_inline_651 : inline_651 = combine (6, 7) [placed 4 (7, 3) card_19, placed 1 (5, 4) card_197, placed 4 (7, 3) card_225, inline_650] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_651 : Valid inline_651 := by
  rw [eq_inline_651]
  apply combination_rule (6, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 3) valid_19
  rcases hc with rfl | hc
  · exact placed_valid 1 (5, 4) valid_197
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 3) valid_225
  subst c
  exact valid_inline_650

theorem eq_card_669 : card_669 = combine (6, 4) [placed 2 (4, 8) card_188, placed 4 (7, 3) card_590, placed 2 (3, 7) card_668, inline_651] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_669 : Valid card_669 := by
  rw [eq_card_669]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 8) valid_188
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 3) valid_590
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_668
  subst c
  exact valid_inline_651

theorem eq_inline_652 : inline_652 = combine (5, 5) [placed 7 (7, 6) card_40, placed 1 (2, 4) card_125, placed 1 (1, 1) card_660] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_652 : Valid inline_652 := by
  rw [eq_inline_652]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 6) valid_40
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_125
  subst c
  exact placed_valid 1 (1, 1) valid_660

theorem eq_inline_653 : inline_653 = combine (5, 5) [placed 7 (7, 6) card_40, placed 1 (2, 4) card_125, placed 1 (1, 3) card_663] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_653 : Valid inline_653 := by
  rw [eq_inline_653]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 6) valid_40
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_125
  subst c
  exact placed_valid 1 (1, 3) valid_663

theorem eq_inline_654 : inline_654 = combine (7, 6) [placed 1 (3, 5) card_106, placed 1 (3, 5) card_219, placed 2 (5, 9) card_530] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_654 : Valid inline_654 := by
  rw [eq_inline_654]
  apply combination_rule (7, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 5) valid_106
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 5) valid_219
  subst c
  exact placed_valid 2 (5, 9) valid_530

theorem eq_inline_655 : inline_655 = combine (5, 5) [placed 7 (7, 6) card_40, placed 5 (2, 5) card_98, placed 2 (4, 9) card_512] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_655 : Valid inline_655 := by
  rw [eq_inline_655]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 6) valid_40
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 5) valid_98
  subst c
  exact placed_valid 2 (4, 9) valid_512

theorem eq_inline_656 : inline_656 = combine (5, 6) [placed 0 (3, 4) card_270, placed 4 (7, 3) card_588, placed 2 (4, 9) card_638, inline_654, inline_655] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_656 : Valid inline_656 := by
  rw [eq_inline_656]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 4) valid_270
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 3) valid_588
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 9) valid_638
  rcases hc with rfl | hc
  · exact valid_inline_654
  subst c
  exact valid_inline_655

theorem eq_inline_657 : inline_657 = combine (5, 5) [placed 7 (7, 6) card_40, placed 1 (2, 4) card_125, placed 0 (2, 1) card_617] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_657 : Valid inline_657 := by
  rw [eq_inline_657]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 6) valid_40
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_125
  subst c
  exact placed_valid 0 (2, 1) valid_617

theorem eq_inline_658 : inline_658 = combine (6, 4) [placed 2 (5, 8) card_13, placed 2 (5, 8) card_31, placed 2 (3, 7) card_355, placed 2 (3, 8) card_356, placed 0 (2, 3) card_434, placed 1 (3, 3) card_435, placed 6 (7, 8) card_441] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_658 : Valid inline_658 := by
  rw [eq_inline_658]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (5, 8) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 2 (5, 8) valid_31
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_355
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 8) valid_356
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 3) valid_434
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 3) valid_435
  subst c
  exact placed_valid 6 (7, 8) valid_441

theorem eq_inline_659 : inline_659 = combine (5, 5) [placed 7 (7, 6) card_40, placed 1 (2, 4) card_125, placed 2 (4, 10) card_535] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_659 : Valid inline_659 := by
  rw [eq_inline_659]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 6) valid_40
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_125
  subst c
  exact placed_valid 2 (4, 10) valid_535

theorem eq_inline_660 : inline_660 = combine (6, 4) [placed 0 (4, 2) card_188, placed 2 (4, 8) card_188, placed 6 (7, 8) card_441, placed 6 (7, 8) card_442, placed 4 (7, 3) card_514, placed 2 (3, 7) card_667] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_660 : Valid inline_660 := by
  rw [eq_inline_660]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 2) valid_188
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 8) valid_188
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 8) valid_441
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 8) valid_442
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 3) valid_514
  subst c
  exact placed_valid 2 (3, 7) valid_667

theorem eq_inline_661 : inline_661 = combine (5, 5) [placed 1 (2, 4) card_125, placed 2 (4, 7) card_136] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_661 : Valid inline_661 := by
  rw [eq_inline_661]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_125
  subst c
  exact placed_valid 2 (4, 7) valid_136

theorem eq_inline_662 : inline_662 = combine (6, 4) [placed 4 (7, 2) card_13, placed 4 (7, 3) card_514, placed 4 (7, 3) card_590, placed 2 (3, 7) card_668, inline_661] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_662 : Valid inline_662 := by
  rw [eq_inline_662]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 2) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 3) valid_514
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 3) valid_590
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_668
  subst c
  exact valid_inline_661

theorem eq_card_670 : card_670 = combine (6, 6) [placed 0 (5, 1) card_459, inline_652, placed 2 (2, 10) card_661, inline_653, inline_656, inline_657, inline_658, inline_659, placed 1 (0, 2) card_665, inline_660, inline_662, placed 0 (0, 0) card_669] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_670 : Valid card_670 := by
  rw [eq_card_670]
  apply combination_rule (6, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 1) valid_459
  rcases hc with rfl | hc
  · exact valid_inline_652
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 10) valid_661
  rcases hc with rfl | hc
  · exact valid_inline_653
  rcases hc with rfl | hc
  · exact valid_inline_656
  rcases hc with rfl | hc
  · exact valid_inline_657
  rcases hc with rfl | hc
  · exact valid_inline_658
  rcases hc with rfl | hc
  · exact valid_inline_659
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_665
  rcases hc with rfl | hc
  · exact valid_inline_660
  rcases hc with rfl | hc
  · exact valid_inline_662
  subst c
  exact placed_valid 0 (0, 0) valid_669

theorem eq_inline_663 : inline_663 = combine (3, 4) [placed 7 (5, 4) card_22, placed 4 (4, 0) card_464] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_663 : Valid inline_663 := by
  rw [eq_inline_663]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 4) valid_22
  subst c
  exact placed_valid 4 (4, 0) valid_464

theorem eq_card_671 : card_671 = combine (3, 3) [placed 1 (0, 2) card_28, placed 1 (0, 2) card_126, placed 5 (0, 4) card_126, inline_663] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_671 : Valid card_671 := by
  rw [eq_card_671]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_28
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_126
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_126
  subst c
  exact valid_inline_663

theorem eq_inline_664 : inline_664 = combine (2, 1) [placed 0 (1, 0) card_22, placed 1 (0, 1) card_22] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_664 : Valid inline_664 := by
  rw [eq_inline_664]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_22
  subst c
  exact placed_valid 1 (0, 1) valid_22

theorem eq_card_672 : card_672 = combine (2, 2) [placed 5 (0, 2) card_34, placed 1 (0, 1) card_305, inline_664] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_672 : Valid card_672 := by
  rw [eq_card_672]
  apply combination_rule (2, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 2) valid_34
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_305
  subst c
  exact valid_inline_664

theorem eq_inline_665 : inline_665 = combine (1, 4) [placed 0 (1, 3) card_30, placed 5 (1, 4) card_74] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_665 : Valid inline_665 := by
  rw [eq_inline_665]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 3) valid_30
  subst c
  exact placed_valid 5 (1, 4) valid_74

theorem eq_inline_666 : inline_666 = combine (4, 5) [placed 0 (1, 4) card_5, placed 0 (1, 3) card_260] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_666 : Valid inline_666 := by
  rw [eq_inline_666]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 4) valid_5
  subst c
  exact placed_valid 0 (1, 3) valid_260

theorem eq_inline_667 : inline_667 = combine (1, 4) [placed 4 (4, 3) card_38, inline_666] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_667 : Valid inline_667 := by
  rw [eq_inline_667]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 3) valid_38
  subst c
  exact valid_inline_666

theorem eq_inline_668 : inline_668 = combine (3, 4) [placed 6 (5, 4) card_0, inline_667] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_668 : Valid inline_668 := by
  rw [eq_inline_668]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 4) valid_0
  subst c
  exact valid_inline_667

theorem eq_inline_669 : inline_669 = combine (4, 5) [placed 0 (2, 2) card_188, placed 6 (6, 8) card_190, placed 7 (6, 7) card_230, placed 0 (1, 3) card_263, placed 2 (1, 8) card_306] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_669 : Valid inline_669 := by
  rw [eq_inline_669]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_188
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 8) valid_190
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 7) valid_230
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 3) valid_263
  subst c
  exact placed_valid 2 (1, 8) valid_306

theorem eq_inline_670 : inline_670 = combine (1, 4) [placed 4 (4, 3) card_38, placed 0 (1, 3) card_145] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_670 : Valid inline_670 := by
  rw [eq_inline_670]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 3) valid_38
  subst c
  exact placed_valid 0 (1, 3) valid_145

theorem eq_inline_671 : inline_671 = combine (3, 4) [placed 6 (5, 4) card_0, inline_670] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_671 : Valid inline_671 := by
  rw [eq_inline_671]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 4) valid_0
  subst c
  exact valid_inline_670

theorem eq_inline_672 : inline_672 = combine (4, 3) [placed 5 (3, 6) card_8, placed 0 (3, 2) card_19, placed 7 (5, 6) card_25] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_672 : Valid inline_672 := by
  rw [eq_inline_672]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 6) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_19
  subst c
  exact placed_valid 7 (5, 6) valid_25

theorem eq_inline_673 : inline_673 = combine (3, 4) [placed 0 (1, 4) card_5, placed 0 (3, 3) card_10] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_673 : Valid inline_673 := by
  rw [eq_inline_673]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 4) valid_5
  subst c
  exact placed_valid 0 (3, 3) valid_10

theorem eq_inline_674 : inline_674 = combine (4, 5) [placed 2 (1, 7) card_263, placed 2 (1, 7) card_271, placed 2 (1, 7) card_424, inline_672, inline_673] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_674 : Valid inline_674 := by
  rw [eq_inline_674]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 7) valid_263
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 7) valid_271
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 7) valid_424
  rcases hc with rfl | hc
  · exact valid_inline_672
  subst c
  exact valid_inline_673

theorem eq_inline_675 : inline_675 = combine (1, 4) [placed 0 (1, 3) card_30, inline_674] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_675 : Valid inline_675 := by
  rw [eq_inline_675]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 3) valid_30
  subst c
  exact valid_inline_674

theorem eq_card_673 : card_673 = combine (4, 4) [inline_665, inline_668, inline_669, inline_671, inline_675] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_673 : Valid card_673 := by
  rw [eq_card_673]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact valid_inline_665
  rcases hc with rfl | hc
  · exact valid_inline_668
  rcases hc with rfl | hc
  · exact valid_inline_669
  rcases hc with rfl | hc
  · exact valid_inline_671
  subst c
  exact valid_inline_675

theorem eq_card_674 : card_674 = combine (2, 4) [placed 4 (2, 2) card_34, placed 0 (1, 2) card_149, placed 0 (0, 0) card_673] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_674 : Valid card_674 := by
  rw [eq_card_674]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 2) valid_34
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_149
  subst c
  exact placed_valid 0 (0, 0) valid_673

theorem eq_inline_676 : inline_676 = combine (7, 7) [placed 4 (8, 3) card_12, placed 0 (4, 3) card_356, placed 0 (4, 3) card_364, placed 4 (8, 3) card_367, placed 6 (8, 9) card_671] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_676 : Valid inline_676 := by
  rw [eq_inline_676]
  apply combination_rule (7, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (8, 3) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 3) valid_356
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 3) valid_364
  rcases hc with rfl | hc
  · exact placed_valid 4 (8, 3) valid_367
  subst c
  exact placed_valid 6 (8, 9) valid_671

theorem eq_inline_677 : inline_677 = combine (7, 4) [placed 0 (5, 2) card_188, placed 6 (9, 8) card_190, placed 4 (8, 2) card_441, placed 4 (8, 2) card_442, placed 6 (8, 7) card_514, placed 0 (4, 3) card_667] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_677 : Valid inline_677 := by
  rw [eq_inline_677]
  apply combination_rule (7, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 2) valid_188
  rcases hc with rfl | hc
  · exact placed_valid 6 (9, 8) valid_190
  rcases hc with rfl | hc
  · exact placed_valid 4 (8, 2) valid_441
  rcases hc with rfl | hc
  · exact placed_valid 4 (8, 2) valid_442
  rcases hc with rfl | hc
  · exact placed_valid 6 (8, 7) valid_514
  subst c
  exact placed_valid 0 (4, 3) valid_667

theorem eq_inline_678 : inline_678 = combine (7, 4) [placed 5 (6, 6) card_8, placed 7 (8, 6) card_26, placed 1 (5, 2) card_133, placed 0 (6, 1) card_186, placed 2 (7, 8) card_187] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_678 : Valid inline_678 := by
  rw [eq_inline_678]
  apply combination_rule (7, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (6, 6) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 6) valid_26
  rcases hc with rfl | hc
  · exact placed_valid 1 (5, 2) valid_133
  rcases hc with rfl | hc
  · exact placed_valid 0 (6, 1) valid_186
  subst c
  exact placed_valid 2 (7, 8) valid_187

theorem eq_inline_679 : inline_679 = combine (7, 4) [placed 3 (7, 3) card_5, placed 3 (9, 2) card_179] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_679 : Valid inline_679 := by
  rw [eq_inline_679]
  apply combination_rule (7, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 3) valid_5
  subst c
  exact placed_valid 3 (9, 2) valid_179

theorem eq_inline_680 : inline_680 = combine (6, 5) [placed 7 (8, 6) card_22, placed 3 (8, 5) card_34, placed 7 (8, 6) card_305] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_680 : Valid inline_680 := by
  rw [eq_inline_680]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 6) valid_22
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 5) valid_34
  subst c
  exact placed_valid 7 (8, 6) valid_305

theorem eq_inline_681 : inline_681 = combine (6, 6) [inline_679, inline_680] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_681 : Valid inline_681 := by
  rw [eq_inline_681]
  apply combination_rule (6, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact valid_inline_679
  subst c
  exact valid_inline_680

theorem eq_inline_682 : inline_682 = combine (7, 3) [placed 2 (6, 8) card_304, placed 6 (8, 7) card_672, inline_678, placed 5 (1, 7) card_674, inline_681] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_682 : Valid inline_682 := by
  rw [eq_inline_682]
  apply combination_rule (7, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (6, 8) valid_304
  rcases hc with rfl | hc
  · exact placed_valid 6 (8, 7) valid_672
  rcases hc with rfl | hc
  · exact valid_inline_678
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 7) valid_674
  subst c
  exact valid_inline_681

theorem eq_inline_683 : inline_683 = combine (7, 7) [placed 0 (5, 3) card_190, placed 4 (9, 3) card_190, placed 0 (4, 3) card_363, placed 6 (8, 9) card_671] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_683 : Valid inline_683 := by
  rw [eq_inline_683]
  apply combination_rule (7, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 3) valid_190
  rcases hc with rfl | hc
  · exact placed_valid 4 (9, 3) valid_190
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 3) valid_363
  subst c
  exact placed_valid 6 (8, 9) valid_671

theorem eq_inline_684 : inline_684 = combine (6, 5) [placed 3 (8, 5) card_34, placed 5 (3, 6) card_97, placed 2 (5, 10) card_535] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_684 : Valid inline_684 := by
  rw [eq_inline_684]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 5) valid_34
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 6) valid_97
  subst c
  exact placed_valid 2 (5, 10) valid_535

theorem eq_inline_685 : inline_685 = combine (7, 4) [placed 5 (3, 6) card_321, placed 3 (8, 3) card_354] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_685 : Valid inline_685 := by
  rw [eq_inline_685]
  apply combination_rule (7, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 6) valid_321
  subst c
  exact placed_valid 3 (8, 3) valid_354

theorem eq_inline_686 : inline_686 = combine (7, 3) [placed 5 (3, 7) card_328, placed 5 (3, 7) card_330, placed 2 (4, 7) card_384, placed 6 (8, 7) card_672, placed 5 (1, 7) card_674, inline_685] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_686 : Valid inline_686 := by
  rw [eq_inline_686]
  apply combination_rule (7, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 7) valid_328
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 7) valid_330
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 7) valid_384
  rcases hc with rfl | hc
  · exact placed_valid 6 (8, 7) valid_672
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 7) valid_674
  subst c
  exact valid_inline_685

theorem eq_card_675 : card_675 = combine (7, 6) [placed 0 (6, 1) card_459, placed 0 (2, 2) card_618, placed 4 (10, 2) card_629, inline_676, inline_677, inline_682, inline_683, inline_684, inline_686] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_675 : Valid card_675 := by
  rw [eq_card_675]
  apply combination_rule (7, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (6, 1) valid_459
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_618
  rcases hc with rfl | hc
  · exact placed_valid 4 (10, 2) valid_629
  rcases hc with rfl | hc
  · exact valid_inline_676
  rcases hc with rfl | hc
  · exact valid_inline_677
  rcases hc with rfl | hc
  · exact valid_inline_682
  rcases hc with rfl | hc
  · exact valid_inline_683
  rcases hc with rfl | hc
  · exact valid_inline_684
  subst c
  exact valid_inline_686

theorem eq_inline_687 : inline_687 = combine (2, 4) [placed 6 (4, 6) card_55, placed 0 (1, 2) card_380] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_687 : Valid inline_687 := by
  rw [eq_inline_687]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 6) valid_55
  subst c
  exact placed_valid 0 (1, 2) valid_380

theorem eq_card_676 : card_676 = combine (4, 3) [placed 5 (0, 3) card_7, placed 0 (1, 2) card_8, placed 1 (0, 2) card_9, inline_687] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_676 : Valid card_676 := by
  rw [eq_card_676]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_9
  subst c
  exact valid_inline_687

theorem eq_card_677 : card_677 = combine (3, 3) [placed 6 (4, 7) card_13, placed 2 (2, 7) card_14, placed 6 (4, 7) card_33, placed 5 (1, 6) card_589, placed 1 (0, 2) card_676] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_677 : Valid card_677 := by
  rw [eq_card_677]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 7) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 7) valid_33
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 6) valid_589
  subst c
  exact placed_valid 1 (0, 2) valid_676

theorem eq_inline_688 : inline_688 = combine (4, 3) [placed 7 (5, 4) card_22, placed 4 (4, 2) card_382] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_688 : Valid inline_688 := by
  rw [eq_inline_688]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 4) valid_22
  subst c
  exact placed_valid 4 (4, 2) valid_382

theorem eq_inline_689 : inline_689 = combine (2, 6) [placed 6 (2, 6) card_18, inline_688] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_689 : Valid inline_689 := by
  rw [eq_inline_689]
  apply combination_rule (2, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (2, 6) valid_18
  subst c
  exact valid_inline_688

theorem eq_card_678 : card_678 = combine (1, 5) [placed 2 (0, 7) card_31, placed 5 (0, 5) card_160, inline_689] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_678 : Valid card_678 := by
  rw [eq_card_678]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 7) valid_31
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_160
  subst c
  exact valid_inline_689

theorem eq_inline_690 : inline_690 = combine (3, 3) [placed 2 (0, 3) card_0, placed 3 (5, 1) card_222] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_690 : Valid inline_690 := by
  rw [eq_inline_690]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 3) valid_0
  subst c
  exact placed_valid 3 (5, 1) valid_222

theorem eq_card_679 : card_679 = combine (2, 3) [placed 0 (1, 0) card_52, inline_690] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_679 : Valid card_679 := by
  rw [eq_card_679]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_52
  subst c
  exact valid_inline_690

theorem eq_inline_691 : inline_691 = combine (1, 3) [placed 4 (4, 0) card_56, placed 6 (5, 5) card_179] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_691 : Valid inline_691 := by
  rw [eq_inline_691]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 0) valid_56
  subst c
  exact placed_valid 6 (5, 5) valid_179

theorem eq_card_680 : card_680 = combine (3, 3) [placed 6 (5, 3) card_0, inline_691] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_680 : Valid card_680 := by
  rw [eq_card_680]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 3) valid_0
  subst c
  exact valid_inline_691

theorem eq_inline_692 : inline_692 = combine (4, 3) [placed 7 (5, 6) card_32, placed 5 (1, 4) card_44, placed 5 (3, 6) card_90] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_692 : Valid inline_692 := by
  rw [eq_inline_692]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 6) valid_32
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_44
  subst c
  exact placed_valid 5 (3, 6) valid_90

theorem eq_inline_693 : inline_693 = combine (4, 3) [placed 0 (3, 3) card_17, placed 7 (5, 6) card_32] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_693 : Valid inline_693 := by
  rw [eq_inline_693]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 3) valid_17
  subst c
  exact placed_valid 7 (5, 6) valid_32

theorem eq_inline_694 : inline_694 = combine (4, 6) [placed 6 (4, 7) card_44, placed 6 (4, 7) card_52, inline_692, inline_693] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_694 : Valid inline_694 := by
  rw [eq_inline_694]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 7) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 7) valid_52
  rcases hc with rfl | hc
  · exact valid_inline_692
  subst c
  exact valid_inline_693

theorem eq_card_681 : card_681 = combine (3, 4) [placed 1 (0, 4) card_11, inline_694] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_681 : Valid card_681 := by
  rw [eq_card_681]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 4) valid_11
  subst c
  exact valid_inline_694

theorem eq_inline_695 : inline_695 = combine (4, 3) [placed 4 (4, 2) card_44, placed 4 (4, 2) card_52, placed 2 (3, 7) card_128, placed 1 (1, 2) card_676] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_695 : Valid inline_695 := by
  rw [eq_inline_695]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_128
  subst c
  exact placed_valid 1 (1, 2) valid_676

theorem eq_inline_696 : inline_696 = combine (6, 7) [placed 0 (6, 3) card_7, placed 4 (7, 3) card_9, placed 3 (8, 4) card_386] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_696 : Valid inline_696 := by
  rw [eq_inline_696]
  apply combination_rule (6, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (6, 3) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 3) valid_9
  subst c
  exact placed_valid 3 (8, 4) valid_386

theorem eq_inline_697 : inline_697 = combine (5, 6) [placed 6 (7, 6) card_0, placed 1 (2, 4) card_222] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_697 : Valid inline_697 := by
  rw [eq_inline_697]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 6) valid_0
  subst c
  exact placed_valid 1 (2, 4) valid_222

theorem eq_inline_698 : inline_698 = combine (4, 6) [placed 4 (7, 3) card_377, inline_696, placed 0 (2, 3) card_426, inline_697] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_698 : Valid inline_698 := by
  rw [eq_inline_698]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 3) valid_377
  rcases hc with rfl | hc
  · exact valid_inline_696
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 3) valid_426
  subst c
  exact valid_inline_697

theorem eq_inline_699 : inline_699 = combine (6, 6) [placed 4 (7, 2) card_13, placed 6 (7, 8) card_14, placed 2 (3, 7) card_79, placed 4 (7, 3) card_679, inline_698] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_699 : Valid inline_699 := by
  rw [eq_inline_699]
  apply combination_rule (6, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 2) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 8) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_79
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 3) valid_679
  subst c
  exact valid_inline_698

theorem eq_inline_700 : inline_700 = combine (6, 5) [placed 2 (3, 8) card_59, placed 5 (2, 5) card_105, placed 4 (7, 1) card_678, inline_699] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_700 : Valid inline_700 := by
  rw [eq_inline_700]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 8) valid_59
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 5) valid_105
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 1) valid_678
  subst c
  exact valid_inline_699

theorem eq_inline_701 : inline_701 = combine (6, 6) [placed 6 (7, 8) card_13, placed 2 (3, 7) card_79, placed 4 (7, 2) card_243, placed 4 (7, 3) card_679] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_701 : Valid inline_701 := by
  rw [eq_inline_701]
  apply combination_rule (6, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 8) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_79
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 2) valid_243
  subst c
  exact placed_valid 4 (7, 3) valid_679

theorem eq_inline_702 : inline_702 = combine (6, 5) [placed 0 (3, 1) card_430, placed 0 (2, 2) card_431, placed 7 (7, 5) card_592, placed 4 (7, 1) card_678, inline_701, placed 2 (2, 9) card_681] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_702 : Valid inline_702 := by
  rw [eq_inline_702]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_430
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_431
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 5) valid_592
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 1) valid_678
  rcases hc with rfl | hc
  · exact valid_inline_701
  subst c
  exact placed_valid 2 (2, 9) valid_681

theorem eq_inline_703 : inline_703 = combine (6, 4) [placed 4 (7, 2) card_422, placed 2 (2, 8) card_450, placed 6 (7, 7) card_503, placed 0 (3, 0) card_642, inline_700, placed 2 (2, 7) card_680, inline_702] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_703 : Valid inline_703 := by
  rw [eq_inline_703]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 2) valid_422
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 8) valid_450
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 7) valid_503
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 0) valid_642
  rcases hc with rfl | hc
  · exact valid_inline_700
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_680
  subst c
  exact valid_inline_702

theorem eq_card_682 : card_682 = combine (4, 4) [placed 2 (3, 8) card_408, placed 2 (3, 8) card_410, placed 6 (6, 8) card_475, placed 5 (1, 7) card_509, placed 7 (7, 7) card_510, placed 2 (2, 8) card_587, placed 6 (7, 8) card_646, inline_695, inline_703] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_682 : Valid card_682 := by
  rw [eq_card_682]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 8) valid_408
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 8) valid_410
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 8) valid_475
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 7) valid_509
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 7) valid_510
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 8) valid_587
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 8) valid_646
  rcases hc with rfl | hc
  · exact valid_inline_695
  subst c
  exact valid_inline_703

theorem eq_inline_704 : inline_704 = combine (2, 5) [placed 6 (4, 5) card_5, placed 5 (0, 6) card_9] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_704 : Valid inline_704 := by
  rw [eq_inline_704]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 5) valid_5
  subst c
  exact placed_valid 5 (0, 6) valid_9

theorem eq_inline_705 : inline_705 = combine (2, 5) [placed 6 (4, 5) card_5, placed 0 (1, 2) card_604] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_705 : Valid inline_705 := by
  rw [eq_inline_705]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 5) valid_5
  subst c
  exact placed_valid 0 (1, 2) valid_604

theorem eq_card_683 : card_683 = combine (3, 5) [placed 1 (0, 4) card_50, placed 1 (0, 4) card_150, inline_704, inline_705, placed 2 (0, 10) card_682] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_683 : Valid card_683 := by
  rw [eq_card_683]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 4) valid_50
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 4) valid_150
  rcases hc with rfl | hc
  · exact valid_inline_704
  rcases hc with rfl | hc
  · exact valid_inline_705
  subst c
  exact placed_valid 2 (0, 10) valid_682

theorem eq_inline_706 : inline_706 = combine (9, 7) [placed 2 (6, 8) card_8, placed 2 (6, 10) card_115, placed 1 (5, 6) card_469, placed 2 (5, 12) card_470, placed 5 (4, 8) card_485, placed 2 (4, 12) card_489] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_706 : Valid inline_706 := by
  rw [eq_inline_706]
  apply combination_rule (9, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (6, 8) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 2 (6, 10) valid_115
  rcases hc with rfl | hc
  · exact placed_valid 1 (5, 6) valid_469
  rcases hc with rfl | hc
  · exact placed_valid 2 (5, 12) valid_470
  rcases hc with rfl | hc
  · exact placed_valid 5 (4, 8) valid_485
  subst c
  exact placed_valid 2 (4, 12) valid_489

theorem eq_inline_707 : inline_707 = combine (8, 7) [placed 2 (5, 10) card_118, placed 5 (5, 10) card_355, placed 5 (5, 11) card_434, placed 1 (3, 6) card_468, inline_706, placed 7 (9, 11) card_491] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_707 : Valid inline_707 := by
  rw [eq_inline_707]
  apply combination_rule (8, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (5, 10) valid_118
  rcases hc with rfl | hc
  · exact placed_valid 5 (5, 10) valid_355
  rcases hc with rfl | hc
  · exact placed_valid 5 (5, 11) valid_434
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 6) valid_468
  rcases hc with rfl | hc
  · exact valid_inline_706
  subst c
  exact placed_valid 7 (9, 11) valid_491

theorem eq_inline_708 : inline_708 = combine (7, 9) [placed 0 (6, 6) card_50, placed 0 (6, 6) card_97, placed 4 (7, 6) card_98, placed 6 (8, 11) card_454, placed 3 (8, 7) card_455, placed 1 (2, 6) card_624] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_708 : Valid inline_708 := by
  rw [eq_inline_708]
  apply combination_rule (7, 9) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (6, 6) valid_50
  rcases hc with rfl | hc
  · exact placed_valid 0 (6, 6) valid_97
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 6) valid_98
  rcases hc with rfl | hc
  · exact placed_valid 6 (8, 11) valid_454
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 7) valid_455
  subst c
  exact placed_valid 1 (2, 6) valid_624

theorem eq_inline_709 : inline_709 = combine (7, 11) [placed 2 (4, 14) card_174, placed 0 (5, 7) card_475, placed 4 (9, 7) card_475, placed 0 (5, 7) card_483, placed 1 (4, 8) card_508, placed 3 (10, 8) card_508, placed 2 (4, 14) card_566, placed 0 (5, 7) card_587, placed 4 (9, 7) card_587, placed 2 (5, 15) card_635, placed 2 (3, 15) card_644, placed 2 (3, 15) card_645, placed 2 (3, 15) card_647] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_709 : Valid inline_709 := by
  rw [eq_inline_709]
  apply combination_rule (7, 11) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 14) valid_174
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 7) valid_475
  rcases hc with rfl | hc
  · exact placed_valid 4 (9, 7) valid_475
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 7) valid_483
  rcases hc with rfl | hc
  · exact placed_valid 1 (4, 8) valid_508
  rcases hc with rfl | hc
  · exact placed_valid 3 (10, 8) valid_508
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 14) valid_566
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 7) valid_587
  rcases hc with rfl | hc
  · exact placed_valid 4 (9, 7) valid_587
  rcases hc with rfl | hc
  · exact placed_valid 2 (5, 15) valid_635
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 15) valid_644
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 15) valid_645
  subst c
  exact placed_valid 2 (3, 15) valid_647

theorem eq_inline_710 : inline_710 = combine (9, 7) [placed 0 (6, 6) card_8, placed 4 (9, 6) card_313] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_710 : Valid inline_710 := by
  rw [eq_inline_710]
  apply combination_rule (9, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (6, 6) valid_8
  subst c
  exact placed_valid 4 (9, 6) valid_313

theorem eq_inline_711 : inline_711 = combine (8, 7) [placed 0 (5, 4) card_257, inline_710, placed 5 (5, 11) card_434, placed 3 (11, 6) card_468, placed 7 (9, 11) card_491] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_711 : Valid inline_711 := by
  rw [eq_inline_711]
  apply combination_rule (8, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 4) valid_257
  rcases hc with rfl | hc
  · exact valid_inline_710
  rcases hc with rfl | hc
  · exact placed_valid 5 (5, 11) valid_434
  rcases hc with rfl | hc
  · exact placed_valid 3 (11, 6) valid_468
  subst c
  exact placed_valid 7 (9, 11) valid_491

theorem eq_card_684 : card_684 = combine (7, 10) [inline_707, placed 5 (0, 15) card_623, inline_708, placed 3 (9, 6) card_625, placed 5 (0, 14) card_630, placed 3 (10, 6) card_632, placed 3 (11, 6) card_636, placed 1 (3, 6) card_639, inline_709, placed 1 (1, 5) card_656, placed 1 (4, 5) card_657, placed 1 (2, 4) card_670, placed 3 (12, 3) card_675, placed 1 (2, 6) card_683, inline_711] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_684 : Valid card_684 := by
  rw [eq_card_684]
  apply combination_rule (7, 10) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact valid_inline_707
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 15) valid_623
  rcases hc with rfl | hc
  · exact valid_inline_708
  rcases hc with rfl | hc
  · exact placed_valid 3 (9, 6) valid_625
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 14) valid_630
  rcases hc with rfl | hc
  · exact placed_valid 3 (10, 6) valid_632
  rcases hc with rfl | hc
  · exact placed_valid 3 (11, 6) valid_636
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 6) valid_639
  rcases hc with rfl | hc
  · exact valid_inline_709
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 5) valid_656
  rcases hc with rfl | hc
  · exact placed_valid 1 (4, 5) valid_657
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_670
  rcases hc with rfl | hc
  · exact placed_valid 3 (12, 3) valid_675
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 6) valid_683
  subst c
  exact valid_inline_711

theorem eq_inline_712 : inline_712 = combine (3, 1) [placed 7 (3, 4) card_5, placed 0 (2, 0) card_312] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_712 : Valid inline_712 := by
  rw [eq_inline_712]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (3, 4) valid_5
  subst c
  exact placed_valid 0 (2, 0) valid_312

theorem eq_inline_713 : inline_713 = combine (2, 1) [placed 7 (3, 5) card_4, inline_712] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_713 : Valid inline_713 := by
  rw [eq_inline_713]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (3, 5) valid_4
  subst c
  exact valid_inline_712

theorem eq_inline_714 : inline_714 = combine (6, 2) [placed 2 (3, 6) card_351, inline_713] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_714 : Valid inline_714 := by
  rw [eq_inline_714]
  apply combination_rule (6, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 6) valid_351
  subst c
  exact valid_inline_713

theorem eq_inline_715 : inline_715 = combine (6, 4) [placed 1 (2, 2) card_96, inline_714] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_715 : Valid inline_715 := by
  rw [eq_inline_715]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 2) valid_96
  subst c
  exact valid_inline_714

theorem eq_inline_716 : inline_716 = combine (3, 2) [placed 1 (3, 2) card_5, inline_715] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_716 : Valid inline_716 := by
  rw [eq_inline_716]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 2) valid_5
  subst c
  exact valid_inline_715

theorem eq_card_685 : card_685 = combine (5, 5) [placed 5 (1, 6) card_67, placed 7 (7, 6) card_175, placed 0 (2, 2) card_228, placed 2 (2, 8) card_435, placed 0 (3, 2) card_531, inline_716] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_685 : Valid card_685 := by
  rw [eq_card_685]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 6) valid_67
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 6) valid_175
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_228
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 8) valid_435
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_531
  subst c
  exact valid_inline_716

theorem eq_inline_717 : inline_717 = combine (5, 4) [placed 1 (2, 3) card_43, placed 3 (7, 2) card_57, placed 0 (3, 0) card_340] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_717 : Valid inline_717 := by
  rw [eq_inline_717]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 3) valid_43
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 2) valid_57
  subst c
  exact placed_valid 0 (3, 0) valid_340

theorem eq_inline_718 : inline_718 = combine (4, 2) [placed 2 (4, 6) card_7, placed 2 (3, 6) card_9, placed 3 (7, 2) card_256] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_718 : Valid inline_718 := by
  rw [eq_inline_718]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 6) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 6) valid_9
  subst c
  exact placed_valid 3 (7, 2) valid_256

theorem eq_card_686 : card_686 = combine (4, 5) [placed 3 (6, 2) card_134, placed 3 (6, 2) card_180, placed 0 (3, 0) card_337, placed 3 (7, 2) card_435, placed 3 (6, 3) card_558, inline_717, inline_718] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_686 : Valid card_686 := by
  rw [eq_card_686]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 2) valid_134
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 2) valid_180
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 0) valid_337
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 2) valid_435
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 3) valid_558
  rcases hc with rfl | hc
  · exact valid_inline_717
  subst c
  exact valid_inline_718

theorem eq_card_687 : card_687 = combine (5, 5) [placed 1 (2, 4) card_44, placed 4 (6, 0) card_324, placed 1 (0, 1) card_685, placed 0 (1, 1) card_686] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_687 : Valid card_687 := by
  rw [eq_card_687]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 0) valid_324
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_685
  subst c
  exact placed_valid 0 (1, 1) valid_686

theorem eq_inline_719 : inline_719 = combine (3, 4) [placed 2 (0, 5) card_8, placed 5 (0, 5) card_41, placed 2 (0, 7) card_253, placed 2 (0, 7) card_256, placed 5 (0, 5) card_336] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_719 : Valid inline_719 := by
  rw [eq_inline_719]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 5) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_41
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 7) valid_253
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 7) valid_256
  subst c
  exact placed_valid 5 (0, 5) valid_336

theorem eq_card_688 : card_688 = combine (1, 5) [placed 1 (0, 1) card_0, inline_719] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_688 : Valid card_688 := by
  rw [eq_card_688]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_0
  subst c
  exact valid_inline_719

theorem eq_inline_720 : inline_720 = combine (4, 6) [placed 4 (5, 2) card_67, placed 6 (5, 8) card_175, placed 1 (1, 3) card_228, placed 3 (5, 3) card_373, placed 3 (7, 3) card_435, placed 1 (0, 4) card_688] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_720 : Valid inline_720 := by
  rw [eq_inline_720]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 2) valid_67
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 8) valid_175
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 3) valid_228
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 3) valid_373
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 3) valid_435
  subst c
  exact placed_valid 1 (0, 4) valid_688

theorem eq_card_689 : card_689 = combine (4, 5) [placed 1 (1, 4) card_44, placed 4 (5, 0) card_324, placed 0 (0, 1) card_686, inline_720] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_689 : Valid card_689 := by
  rw [eq_card_689]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 4) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 0) valid_324
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_686
  subst c
  exact valid_inline_720

theorem eq_inline_721 : inline_721 = combine (3, 6) [placed 0 (2, 2) card_39, placed 0 (2, 2) card_80, placed 1 (0, 2) card_463] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_721 : Valid inline_721 := by
  rw [eq_inline_721]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_39
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_80
  subst c
  exact placed_valid 1 (0, 2) valid_463

theorem eq_card_690 : card_690 = combine (3, 4) [placed 1 (2, 3) card_21, placed 6 (5, 6) card_56, inline_721] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_690 : Valid card_690 := by
  rw [eq_card_690]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 3) valid_21
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 6) valid_56
  subst c
  exact valid_inline_721

theorem eq_inline_722 : inline_722 = combine (4, 5) [placed 2 (3, 6) card_27, placed 5 (1, 7) card_277, placed 1 (1, 3) card_278] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_722 : Valid inline_722 := by
  rw [eq_inline_722]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 6) valid_27
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 7) valid_277
  subst c
  exact placed_valid 1 (1, 3) valid_278

theorem eq_inline_723 : inline_723 = combine (5, 6) [placed 6 (7, 6) card_0, placed 0 (3, 2) card_317] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_723 : Valid inline_723 := by
  rw [eq_inline_723]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 6) valid_0
  subst c
  exact placed_valid 0 (3, 2) valid_317

theorem eq_inline_724 : inline_724 = combine (6, 6) [placed 5 (3, 6) card_30, placed 2 (3, 9) card_59, placed 0 (5, 2) card_462, inline_723] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_724 : Valid inline_724 := by
  rw [eq_inline_724]
  apply combination_rule (6, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 6) valid_30
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 9) valid_59
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 2) valid_462
  subst c
  exact valid_inline_723

theorem eq_inline_725 : inline_725 = combine (6, 5) [placed 5 (2, 6) card_102, placed 0 (2, 3) card_400, inline_724] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_725 : Valid inline_725 := by
  rw [eq_inline_725]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 6) valid_102
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 3) valid_400
  subst c
  exact valid_inline_724

theorem eq_inline_726 : inline_726 = combine (4, 5) [placed 1 (3, 2) card_0, inline_725] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_726 : Valid inline_726 := by
  rw [eq_inline_726]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 2) valid_0
  subst c
  exact valid_inline_725

theorem eq_inline_727 : inline_727 = combine (4, 6) [placed 1 (3, 3) card_5, inline_726] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_727 : Valid inline_727 := by
  rw [eq_inline_727]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 3) valid_5
  subst c
  exact valid_inline_726

theorem eq_inline_728 : inline_728 = combine (2, 6) [placed 3 (3, 3) card_5, placed 1 (2, 4) card_35] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_728 : Valid inline_728 := by
  rw [eq_inline_728]
  apply combination_rule (2, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (3, 3) valid_5
  subst c
  exact placed_valid 1 (2, 4) valid_35

theorem eq_inline_729 : inline_729 = combine (6, 7) [inline_728, placed 2 (5, 10) card_460, placed 0 (2, 2) card_488] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_729 : Valid inline_729 := by
  rw [eq_inline_729]
  apply combination_rule (6, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact valid_inline_728
  rcases hc with rfl | hc
  · exact placed_valid 2 (5, 10) valid_460
  subst c
  exact placed_valid 0 (2, 2) valid_488

theorem eq_inline_730 : inline_730 = combine (6, 5) [placed 1 (2, 4) card_39, placed 1 (2, 4) card_80, inline_729] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_730 : Valid inline_730 := by
  rw [eq_inline_730]
  apply combination_rule (6, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_39
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_80
  subst c
  exact valid_inline_729

theorem eq_inline_731 : inline_731 = combine (4, 5) [placed 0 (3, 4) card_21, placed 7 (6, 7) card_56, inline_730] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_731 : Valid inline_731 := by
  rw [eq_inline_731]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 4) valid_21
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 7) valid_56
  subst c
  exact valid_inline_730

theorem eq_inline_732 : inline_732 = combine (3, 7) [placed 4 (3, 3) card_6, placed 1 (2, 4) card_8, placed 1 (0, 2) card_690, inline_731] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_732 : Valid inline_732 := by
  rw [eq_inline_732]
  apply combination_rule (3, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 3) valid_6
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_690
  subst c
  exact valid_inline_731

theorem eq_card_691 : card_691 = combine (3, 6) [placed 1 (2, 3) card_8, inline_722, inline_727, inline_732] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_691 : Valid card_691 := by
  rw [eq_card_691]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 3) valid_8
  rcases hc with rfl | hc
  · exact valid_inline_722
  rcases hc with rfl | hc
  · exact valid_inline_727
  subst c
  exact valid_inline_732

theorem eq_inline_733 : inline_733 = combine (3, 3) [placed 2 (2, 7) card_13, placed 2 (2, 7) card_14, placed 5 (0, 6) card_118, placed 4 (4, 1) card_192, placed 0 (2, 1) card_193, placed 0 (1, 0) card_396, placed 7 (6, 6) card_435] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_733 : Valid inline_733 := by
  rw [eq_inline_733]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 6) valid_118
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_192
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_193
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_396
  subst c
  exact placed_valid 7 (6, 6) valid_435

theorem eq_inline_734 : inline_734 = combine (4, 4) [placed 2 (0, 5) card_2, placed 2 (1, 7) card_509] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_734 : Valid inline_734 := by
  rw [eq_inline_734]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 5) valid_2
  subst c
  exact placed_valid 2 (1, 7) valid_509

theorem eq_inline_735 : inline_735 = combine (3, 4) [placed 0 (0, 2) card_110, placed 0 (0, 2) card_119, placed 2 (1, 8) card_399, placed 0 (0, 1) card_430, placed 0 (0, 3) card_461, placed 2 (1, 8) card_475, inline_733, inline_734] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_735 : Valid inline_735 := by
  rw [eq_inline_735]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_110
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_119
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 8) valid_399
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_430
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 3) valid_461
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 8) valid_475
  rcases hc with rfl | hc
  · exact valid_inline_733
  subst c
  exact valid_inline_734

theorem eq_card_692 : card_692 = combine (1, 5) [placed 1 (0, 2) card_5, inline_735] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_692 : Valid card_692 := by
  rw [eq_card_692]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_5
  subst c
  exact valid_inline_735

theorem eq_inline_736 : inline_736 = combine (5, 8) [placed 0 (4, 4) card_28, placed 1 (2, 7) card_409] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_736 : Valid inline_736 := by
  rw [eq_inline_736]
  apply combination_rule (5, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 4) valid_28
  subst c
  exact placed_valid 1 (2, 7) valid_409

theorem eq_inline_737 : inline_737 = combine (5, 8) [placed 3 (7, 4) card_168, placed 1 (2, 7) card_409, placed 1 (1, 6) card_611] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_737 : Valid inline_737 := by
  rw [eq_inline_737]
  apply combination_rule (5, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 4) valid_168
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 7) valid_409
  subst c
  exact placed_valid 1 (1, 6) valid_611

theorem eq_inline_738 : inline_738 = combine (5, 4) [placed 3 (6, 4) card_10, placed 2 (4, 8) card_308] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_738 : Valid inline_738 := by
  rw [eq_inline_738]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 4) valid_10
  subst c
  exact placed_valid 2 (4, 8) valid_308

theorem eq_inline_739 : inline_739 = combine (3, 5) [placed 3 (7, 5) card_6, placed 4 (6, 4) card_26, placed 4 (7, 2) card_214, inline_738] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_739 : Valid inline_739 := by
  rw [eq_inline_739]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 5) valid_6
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 4) valid_26
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 2) valid_214
  subst c
  exact valid_inline_738

theorem eq_inline_740 : inline_740 = combine (5, 4) [placed 4 (7, 4) card_233, placed 7 (6, 7) card_314, placed 5 (4, 7) card_314] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_740 : Valid inline_740 := by
  rw [eq_inline_740]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 4) valid_233
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 7) valid_314
  subst c
  exact placed_valid 5 (4, 7) valid_314

theorem eq_inline_741 : inline_741 = combine (5, 6) [placed 6 (5, 8) card_44, placed 2 (5, 8) card_52, inline_740] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_741 : Valid inline_741 := by
  rw [eq_inline_741]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 8) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 2 (5, 8) valid_52
  subst c
  exact valid_inline_740

theorem eq_inline_742 : inline_742 = combine (5, 7) [placed 6 (7, 10) card_319, inline_736, inline_737, inline_739, inline_741] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_742 : Valid inline_742 := by
  rw [eq_inline_742]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 10) valid_319
  rcases hc with rfl | hc
  · exact valid_inline_736
  rcases hc with rfl | hc
  · exact valid_inline_737
  rcases hc with rfl | hc
  · exact valid_inline_739
  subst c
  exact valid_inline_741

theorem eq_card_693 : card_693 = combine (7, 8) [placed 0 (4, 4) card_147, placed 7 (8, 8) card_339, placed 1 (2, 5) card_692, inline_742] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_693 : Valid card_693 := by
  rw [eq_card_693]
  apply combination_rule (7, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 4) valid_147
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 8) valid_339
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 5) valid_692
  subst c
  exact valid_inline_742

theorem eq_inline_743 : inline_743 = combine (4, 6) [placed 2 (4, 11) card_390, placed 4 (7, 3) card_544, placed 1 (0, 5) card_545, placed 3 (9, 5) card_546, placed 1 (0, 5) card_549] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_743 : Valid inline_743 := by
  rw [eq_inline_743]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 11) valid_390
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 3) valid_544
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 5) valid_545
  rcases hc with rfl | hc
  · exact placed_valid 3 (9, 5) valid_546
  subst c
  exact placed_valid 1 (0, 5) valid_549

theorem eq_inline_744 : inline_744 = combine (5, 4) [placed 2 (5, 8) card_7, placed 5 (4, 7) card_26, placed 7 (8, 8) card_142, placed 5 (0, 11) card_693] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_744 : Valid inline_744 := by
  rw [eq_inline_744]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (5, 8) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 5 (4, 7) valid_26
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 8) valid_142
  subst c
  exact placed_valid 5 (0, 11) valid_693

theorem eq_card_694 : card_694 = combine (5, 7) [placed 5 (2, 8) card_116, placed 4 (7, 3) card_188, placed 1 (2, 5) card_397, placed 3 (8, 4) card_435, placed 0 (2, 2) card_691, inline_743, inline_744] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_694 : Valid card_694 := by
  rw [eq_card_694]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 8) valid_116
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 3) valid_188
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 5) valid_397
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 4) valid_435
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_691
  rcases hc with rfl | hc
  · exact valid_inline_743
  subst c
  exact valid_inline_744

theorem eq_inline_745 : inline_745 = combine (1, 6) [placed 0 (1, 3) card_11, placed 4 (2, 2) card_75, placed 2 (1, 7) card_103] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_745 : Valid inline_745 := by
  rw [eq_inline_745]
  apply combination_rule (1, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 3) valid_11
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 2) valid_75
  subst c
  exact placed_valid 2 (1, 7) valid_103

theorem eq_inline_746 : inline_746 = combine (1, 6) [placed 0 (1, 3) card_11, placed 4 (2, 4) card_17, placed 7 (2, 7) card_90] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_746 : Valid inline_746 := by
  rw [eq_inline_746]
  apply combination_rule (1, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 3) valid_11
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 4) valid_17
  subst c
  exact placed_valid 7 (2, 7) valid_90

theorem eq_inline_747 : inline_747 = combine (1, 7) [placed 6 (2, 8) card_308, placed 3 (5, 5) card_348, inline_745, inline_746] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_747 : Valid inline_747 := by
  rw [eq_inline_747]
  apply combination_rule (1, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (2, 8) valid_308
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 5) valid_348
  rcases hc with rfl | hc
  · exact valid_inline_745
  subst c
  exact valid_inline_746

theorem eq_inline_748 : inline_748 = combine (1, 4) [placed 6 (4, 5) card_5, inline_747] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_748 : Valid inline_748 := by
  rw [eq_inline_748]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 5) valid_5
  subst c
  exact valid_inline_747

theorem eq_inline_749 : inline_749 = combine (3, 8) [placed 0 (1, 4) card_96, inline_748] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_749 : Valid inline_749 := by
  rw [eq_inline_749]
  apply combination_rule (3, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 4) valid_96
  subst c
  exact valid_inline_748

theorem eq_inline_750 : inline_750 = combine (1, 5) [placed 0 (1, 5) card_5, inline_749] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_750 : Valid inline_750 := by
  rw [eq_inline_750]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 5) valid_5
  subst c
  exact valid_inline_749

theorem eq_inline_751 : inline_751 = combine (4, 7) [placed 4 (5, 3) card_67, placed 6 (5, 9) card_175, placed 1 (1, 4) card_228, placed 3 (7, 4) card_435, placed 1 (0, 5) card_688, inline_750] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_751 : Valid inline_751 := by
  rw [eq_inline_751]
  apply combination_rule (4, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 3) valid_67
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 9) valid_175
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 4) valid_228
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 4) valid_435
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 5) valid_688
  subst c
  exact valid_inline_750

theorem eq_inline_752 : inline_752 = combine (4, 6) [placed 1 (1, 5) card_44, placed 4 (5, 1) card_324, placed 0 (0, 2) card_686, inline_751] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_752 : Valid inline_752 := by
  rw [eq_inline_752]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 5) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 1) valid_324
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_686
  subst c
  exact valid_inline_751

theorem eq_card_695 : card_695 = combine (4, 5) [placed 1 (0, 4) card_12, placed 2 (1, 8) card_118, placed 1 (0, 3) card_135, placed 5 (0, 7) card_182, inline_752] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_695 : Valid card_695 := by
  rw [eq_card_695]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 4) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 8) valid_118
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_135
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 7) valid_182
  subst c
  exact valid_inline_752

theorem eq_inline_753 : inline_753 = combine (5, 7) [placed 7 (5, 7) card_5, placed 3 (6, 4) card_197] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_753 : Valid inline_753 := by
  rw [eq_inline_753]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 7) valid_5
  subst c
  exact placed_valid 3 (6, 4) valid_197

theorem eq_inline_754 : inline_754 = combine (4, 4) [placed 5 (1, 7) card_317, inline_753, placed 7 (8, 7) card_436, placed 6 (8, 9) card_685] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_754 : Valid inline_754 := by
  rw [eq_inline_754]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 7) valid_317
  rcases hc with rfl | hc
  · exact valid_inline_753
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 7) valid_436
  subst c
  exact placed_valid 6 (8, 9) valid_685

theorem eq_card_696 : card_696 = combine (5, 4) [placed 6 (6, 8) card_12, placed 7 (9, 7) card_322, placed 4 (6, 1) card_369, placed 7 (8, 7) card_435, placed 0 (2, 1) card_622, inline_754] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_696 : Valid card_696 := by
  rw [eq_card_696]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 8) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 7 (9, 7) valid_322
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 1) valid_369
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 7) valid_435
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_622
  subst c
  exact valid_inline_754

theorem eq_inline_755 : inline_755 = combine (5, 2) [placed 7 (5, 3) card_16, placed 0 (2, 2) card_374] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_755 : Valid inline_755 := by
  rw [eq_inline_755]
  apply combination_rule (5, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 3) valid_16
  subst c
  exact placed_valid 0 (2, 2) valid_374

theorem eq_inline_756 : inline_756 = combine (6, 6) [placed 7 (9, 7) card_95, inline_755] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_756 : Valid inline_756 := by
  rw [eq_inline_756]
  apply combination_rule (6, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (9, 7) valid_95
  subst c
  exact valid_inline_755

theorem eq_inline_757 : inline_757 = combine (5, 6) [placed 7 (6, 6) card_151, placed 3 (8, 5) card_460, inline_756] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_757 : Valid inline_757 := by
  rw [eq_inline_757]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 6) valid_151
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 5) valid_460
  subst c
  exact valid_inline_756

theorem eq_inline_758 : inline_758 = combine (3, 6) [placed 4 (4, 2) card_39, placed 4 (5, 2) card_121, inline_757] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_758 : Valid inline_758 := by
  rw [eq_inline_758]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_39
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 2) valid_121
  subst c
  exact valid_inline_757

theorem eq_inline_759 : inline_759 = combine (3, 4) [placed 1 (2, 3) card_21, placed 6 (5, 6) card_56, inline_758] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_759 : Valid inline_759 := by
  rw [eq_inline_759]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 3) valid_21
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 6) valid_56
  subst c
  exact valid_inline_758

theorem eq_card_697 : card_697 = combine (5, 3) [placed 7 (6, 3) card_7, placed 0 (2, 2) card_8, placed 0 (0, 0) card_690, inline_759] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_697 : Valid card_697 := by
  rw [eq_card_697]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 3) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_690
  subst c
  exact valid_inline_759

theorem eq_card_698 : card_698 = combine (4, 6) [placed 0 (3, 2) card_12, placed 6 (6, 8) card_182, placed 0 (2, 2) card_188, placed 3 (7, 3) card_619, placed 0 (1, 0) card_620, placed 0 (1, 1) card_622, placed 1 (0, 1) card_687, placed 1 (1, 2) card_697] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_698 : Valid card_698 := by
  rw [eq_card_698]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 8) valid_182
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_188
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 3) valid_619
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_620
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_622
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_687
  subst c
  exact placed_valid 1 (1, 2) valid_697

theorem eq_inline_760 : inline_760 = combine (7, 6) [placed 0 (6, 4) card_42, placed 1 (4, 5) card_52] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_760 : Valid inline_760 := by
  rw [eq_inline_760]
  apply combination_rule (7, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (6, 4) valid_42
  subst c
  exact placed_valid 1 (4, 5) valid_52

theorem eq_inline_761 : inline_761 = combine (7, 8) [placed 7 (10, 9) card_95, placed 1 (4, 4) card_112, inline_760] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_761 : Valid inline_761 := by
  rw [eq_inline_761]
  apply combination_rule (7, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (10, 9) valid_95
  rcases hc with rfl | hc
  · exact placed_valid 1 (4, 4) valid_112
  subst c
  exact valid_inline_760

theorem eq_inline_762 : inline_762 = combine (6, 8) [placed 0 (4, 4) card_371, placed 3 (9, 7) card_460, inline_761] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_762 : Valid inline_762 := by
  rw [eq_inline_762]
  apply combination_rule (6, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 4) valid_371
  rcases hc with rfl | hc
  · exact placed_valid 3 (9, 7) valid_460
  subst c
  exact valid_inline_761

theorem eq_inline_763 : inline_763 = combine (4, 8) [placed 4 (7, 4) card_147, placed 5 (3, 8) card_249, placed 3 (9, 5) card_692, inline_762] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_763 : Valid inline_763 := by
  rw [eq_inline_763]
  apply combination_rule (4, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 4) valid_147
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 8) valid_249
  rcases hc with rfl | hc
  · exact placed_valid 3 (9, 5) valid_692
  subst c
  exact valid_inline_762

theorem eq_inline_764 : inline_764 = combine (7, 4) [placed 2 (4, 5) card_5, placed 2 (5, 7) card_259] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_764 : Valid inline_764 := by
  rw [eq_inline_764]
  apply combination_rule (7, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 5) valid_5
  subst c
  exact placed_valid 2 (5, 7) valid_259

theorem eq_inline_765 : inline_765 = combine (6, 3) [placed 6 (7, 6) card_10, placed 6 (7, 6) card_48, placed 5 (4, 6) card_134, inline_764] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_765 : Valid inline_765 := by
  rw [eq_inline_765]
  apply combination_rule (6, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 6) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 6 (7, 6) valid_48
  rcases hc with rfl | hc
  · exact placed_valid 5 (4, 6) valid_134
  subst c
  exact valid_inline_764

theorem eq_inline_766 : inline_766 = combine (6, 4) [placed 5 (4, 5) card_389, placed 0 (5, 0) card_545, placed 2 (5, 9) card_546, placed 0 (5, 0) card_549, inline_765] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_766 : Valid inline_766 := by
  rw [eq_inline_766]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (4, 5) valid_389
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 0) valid_545
  rcases hc with rfl | hc
  · exact placed_valid 2 (5, 9) valid_546
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 0) valid_549
  subst c
  exact valid_inline_765

theorem eq_card_699 : card_699 = combine (7, 5) [placed 0 (4, 4) card_197, placed 0 (4, 1) card_321, placed 4 (11, 0) card_693, inline_763, inline_766] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_699 : Valid card_699 := by
  rw [eq_card_699]
  apply combination_rule (7, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 4) valid_197
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 1) valid_321
  rcases hc with rfl | hc
  · exact placed_valid 4 (11, 0) valid_693
  rcases hc with rfl | hc
  · exact valid_inline_763
  subst c
  exact valid_inline_766

theorem eq_inline_767 : inline_767 = combine (2, 5) [placed 1 (0, 4) card_39, placed 0 (1, 2) card_52] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_767 : Valid inline_767 := by
  rw [eq_inline_767]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 4) valid_39
  subst c
  exact placed_valid 0 (1, 2) valid_52

theorem eq_inline_768 : inline_768 = combine (3, 5) [placed 6 (4, 5) card_5, placed 2 (1, 6) card_197] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_768 : Valid inline_768 := by
  rw [eq_inline_768]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 5) valid_5
  subst c
  exact placed_valid 2 (1, 6) valid_197

theorem eq_inline_769 : inline_769 = combine (2, 5) [placed 1 (1, 2) card_0, inline_768] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_769 : Valid inline_769 := by
  rw [eq_inline_769]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_0
  subst c
  exact valid_inline_768

theorem eq_inline_770 : inline_770 = combine (2, 6) [placed 0 (1, 2) card_61, placed 1 (0, 3) card_348, inline_769] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_770 : Valid inline_770 := by
  rw [eq_inline_770]
  apply combination_rule (2, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_61
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_348
  subst c
  exact valid_inline_769

theorem eq_inline_771 : inline_771 = combine (4, 4) [placed 4 (4, 2) card_7, placed 5 (3, 6) card_8, placed 2 (3, 7) card_9] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_771 : Valid inline_771 := by
  rw [eq_inline_771]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 6) valid_8
  subst c
  exact placed_valid 2 (3, 7) valid_9

theorem eq_inline_772 : inline_772 = combine (2, 5) [placed 1 (0, 4) card_40, placed 0 (1, 2) card_52] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_772 : Valid inline_772 := by
  rw [eq_inline_772]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 4) valid_40
  subst c
  exact placed_valid 0 (1, 2) valid_52

theorem eq_inline_773 : inline_773 = combine (4, 6) [placed 6 (5, 8) card_304, inline_771, inline_772] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_773 : Valid inline_773 := by
  rw [eq_inline_773]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 8) valid_304
  rcases hc with rfl | hc
  · exact valid_inline_771
  subst c
  exact valid_inline_772

theorem eq_card_700 : card_700 = combine (4, 5) [placed 2 (0, 8) card_204, inline_767, placed 0 (3, 0) card_460, inline_770, inline_773] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_700 : Valid card_700 := by
  rw [eq_card_700]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 8) valid_204
  rcases hc with rfl | hc
  · exact valid_inline_767
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 0) valid_460
  rcases hc with rfl | hc
  · exact valid_inline_770
  subst c
  exact valid_inline_773

theorem eq_inline_774 : inline_774 = combine (5, 8) [placed 5 (4, 8) card_10, placed 4 (6, 6) card_39] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_774 : Valid inline_774 := by
  rw [eq_inline_774]
  apply combination_rule (5, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (4, 8) valid_10
  subst c
  exact placed_valid 4 (6, 6) valid_39

theorem eq_inline_775 : inline_775 = combine (5, 8) [placed 3 (8, 7) card_52, placed 1 (1, 6) card_325] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_775 : Valid inline_775 := by
  rw [eq_inline_775]
  apply combination_rule (5, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 7) valid_52
  subst c
  exact placed_valid 1 (1, 6) valid_325

theorem eq_inline_776 : inline_776 = combine (4, 7) [placed 4 (7, 6) card_8, placed 1 (2, 6) card_463] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_776 : Valid inline_776 := by
  rw [eq_inline_776]
  apply combination_rule (4, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 6) valid_8
  subst c
  exact placed_valid 1 (2, 6) valid_463

theorem eq_inline_777 : inline_777 = combine (4, 8) [placed 5 (4, 8) card_18, placed 4 (7, 6) card_348] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_777 : Valid inline_777 := by
  rw [eq_inline_777]
  apply combination_rule (4, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (4, 8) valid_18
  subst c
  exact placed_valid 4 (7, 6) valid_348

theorem eq_inline_778 : inline_778 = combine (5, 9) [placed 5 (5, 10) card_5, placed 0 (4, 6) card_9] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_778 : Valid inline_778 := by
  rw [eq_inline_778]
  apply combination_rule (5, 9) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (5, 10) valid_5
  subst c
  exact placed_valid 0 (4, 6) valid_9

theorem eq_inline_779 : inline_779 = combine (5, 9) [placed 5 (5, 10) card_5, placed 0 (4, 6) card_372] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_779 : Valid inline_779 := by
  rw [eq_inline_779]
  apply combination_rule (5, 9) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (5, 10) valid_5
  subst c
  exact placed_valid 0 (4, 6) valid_372

theorem eq_inline_780 : inline_780 = combine (5, 8) [placed 5 (4, 8) card_10, inline_778, inline_779] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_780 : Valid inline_780 := by
  rw [eq_inline_780]
  apply combination_rule (5, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (4, 8) valid_10
  rcases hc with rfl | hc
  · exact valid_inline_778
  subst c
  exact valid_inline_779

theorem eq_inline_781 : inline_781 = combine (5, 10) [inline_774, placed 3 (10, 6) card_683, inline_775, inline_776, inline_777, placed 1 (2, 6) card_700, inline_780] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_781 : Valid inline_781 := by
  rw [eq_inline_781]
  apply combination_rule (5, 10) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact valid_inline_774
  rcases hc with rfl | hc
  · exact placed_valid 3 (10, 6) valid_683
  rcases hc with rfl | hc
  · exact valid_inline_775
  rcases hc with rfl | hc
  · exact valid_inline_776
  rcases hc with rfl | hc
  · exact valid_inline_777
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 6) valid_700
  subst c
  exact valid_inline_780

theorem eq_card_701 : card_701 = combine (7, 7) [placed 5 (3, 8) card_12, placed 4 (8, 3) card_322, placed 0 (4, 4) card_435, placed 6 (9, 10) card_697, placed 0 (1, 2) card_699, inline_781] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_701 : Valid card_701 := by
  rw [eq_card_701]
  apply combination_rule (7, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 8) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 4 (8, 3) valid_322
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 4) valid_435
  rcases hc with rfl | hc
  · exact placed_valid 6 (9, 10) valid_697
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_699
  subst c
  exact valid_inline_781

theorem eq_inline_782 : inline_782 = combine (1, 1) [placed 0 (1, 0) card_15, placed 1 (0, 1) card_40] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_782 : Valid inline_782 := by
  rw [eq_inline_782]
  apply combination_rule (1, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_15
  subst c
  exact placed_valid 1 (0, 1) valid_40

theorem eq_inline_783 : inline_783 = combine (4, 2) [placed 1 (1, 2) card_30, placed 0 (0, 0) card_108, inline_782, placed 0 (1, 0) card_511] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_783 : Valid inline_783 := by
  rw [eq_inline_783]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_30
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_108
  rcases hc with rfl | hc
  · exact valid_inline_782
  subst c
  exact placed_valid 0 (1, 0) valid_511

theorem eq_card_702 : card_702 = combine (4, 3) [placed 5 (0, 3) card_22, placed 0 (0, 1) card_400, inline_783] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_702 : Valid card_702 := by
  rw [eq_card_702]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_22
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_400
  subst c
  exact valid_inline_783

theorem eq_inline_784 : inline_784 = combine (5, 3) [placed 4 (5, 3) card_3, placed 0 (4, 2) card_27] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_784 : Valid inline_784 := by
  rw [eq_inline_784]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 3) valid_3
  subst c
  exact placed_valid 0 (4, 2) valid_27

theorem eq_inline_785 : inline_785 = combine (2, 3) [placed 4 (5, 3) card_0, placed 2 (2, 6) card_52] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_785 : Valid inline_785 := by
  rw [eq_inline_785]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 3) valid_0
  subst c
  exact placed_valid 2 (2, 6) valid_52

theorem eq_inline_786 : inline_786 = combine (3, 2) [placed 7 (4, 6) card_0, placed 2 (2, 6) card_101] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_786 : Valid inline_786 := by
  rw [eq_inline_786]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 6) valid_0
  subst c
  exact placed_valid 2 (2, 6) valid_101

theorem eq_inline_787 : inline_787 = combine (3, 3) [placed 0 (3, 2) card_195, inline_784, inline_785, inline_786] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_787 : Valid inline_787 := by
  rw [eq_inline_787]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_195
  rcases hc with rfl | hc
  · exact valid_inline_784
  rcases hc with rfl | hc
  · exact valid_inline_785
  subst c
  exact valid_inline_786

theorem eq_inline_788 : inline_788 = combine (2, 2) [placed 3 (6, 2) card_11, placed 1 (2, 2) card_103, placed 4 (5, 1) card_157] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_788 : Valid inline_788 := by
  rw [eq_inline_788]
  apply combination_rule (2, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 2) valid_11
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 2) valid_103
  subst c
  exact placed_valid 4 (5, 1) valid_157

theorem eq_inline_789 : inline_789 = combine (5, 2) [placed 5 (4, 5) card_5, inline_788] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_789 : Valid inline_789 := by
  rw [eq_inline_789]
  apply combination_rule (5, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (4, 5) valid_5
  subst c
  exact valid_inline_788

theorem eq_inline_790 : inline_790 = combine (3, 2) [placed 7 (4, 5) card_5, inline_789] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_790 : Valid inline_790 := by
  rw [eq_inline_790]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 5) valid_5
  subst c
  exact valid_inline_789

theorem eq_inline_791 : inline_791 = combine (4, 2) [placed 2 (4, 6) card_7, placed 6 (5, 6) card_9, inline_790] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_791 : Valid inline_791 := by
  rw [eq_inline_791]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 6) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 6) valid_9
  subst c
  exact valid_inline_790

theorem eq_inline_792 : inline_792 = combine (5, 3) [placed 4 (5, 3) card_18, placed 4 (5, 2) card_77] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_792 : Valid inline_792 := by
  rw [eq_inline_792]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 3) valid_18
  subst c
  exact placed_valid 4 (5, 2) valid_77

theorem eq_inline_793 : inline_793 = combine (4, 6) [placed 6 (5, 7) card_9, placed 3 (5, 3) card_49, placed 0 (3, 1) card_186, inline_792] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_793 : Valid inline_793 := by
  rw [eq_inline_793]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 7) valid_9
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 3) valid_49
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_186
  subst c
  exact valid_inline_792

theorem eq_card_703 : card_703 = combine (4, 3) [placed 6 (5, 7) card_13, placed 4 (5, 0) card_369, inline_787, placed 2 (1, 6) card_516, inline_791, inline_793] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_703 : Valid card_703 := by
  rw [eq_card_703]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 7) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 0) valid_369
  rcases hc with rfl | hc
  · exact valid_inline_787
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_516
  rcases hc with rfl | hc
  · exact valid_inline_791
  subst c
  exact valid_inline_793

theorem block10_valid : Valid card_640 ∧ Valid card_641 ∧ Valid card_642 ∧ Valid card_643 ∧ Valid card_644 ∧ Valid card_645 ∧ Valid card_646 ∧ Valid card_647 ∧ Valid card_648 ∧ Valid card_649 ∧ Valid card_650 ∧ Valid card_651 ∧ Valid card_652 ∧ Valid card_653 ∧ Valid card_654 ∧ Valid card_655 ∧ Valid card_656 ∧ Valid card_657 ∧ Valid card_658 ∧ Valid card_659 ∧ Valid card_660 ∧ Valid card_661 ∧ Valid card_662 ∧ Valid card_663 ∧ Valid card_664 ∧ Valid card_665 ∧ Valid card_666 ∧ Valid card_667 ∧ Valid card_668 ∧ Valid card_669 ∧ Valid card_670 ∧ Valid card_671 ∧ Valid card_672 ∧ Valid card_673 ∧ Valid card_674 ∧ Valid card_675 ∧ Valid card_676 ∧ Valid card_677 ∧ Valid card_678 ∧ Valid card_679 ∧ Valid card_680 ∧ Valid card_681 ∧ Valid card_682 ∧ Valid card_683 ∧ Valid card_684 ∧ Valid card_685 ∧ Valid card_686 ∧ Valid card_687 ∧ Valid card_688 ∧ Valid card_689 ∧ Valid card_690 ∧ Valid card_691 ∧ Valid card_692 ∧ Valid card_693 ∧ Valid card_694 ∧ Valid card_695 ∧ Valid card_696 ∧ Valid card_697 ∧ Valid card_698 ∧ Valid card_699 ∧ Valid card_700 ∧ Valid card_701 ∧ Valid card_702 ∧ Valid card_703 ∧ True :=
  ⟨valid_640, valid_641, valid_642, valid_643, valid_644, valid_645, valid_646, valid_647, valid_648, valid_649, valid_650, valid_651, valid_652, valid_653, valid_654, valid_655, valid_656, valid_657, valid_658, valid_659, valid_660, valid_661, valid_662, valid_663, valid_664, valid_665, valid_666, valid_667, valid_668, valid_669, valid_670, valid_671, valid_672, valid_673, valid_674, valid_675, valid_676, valid_677, valid_678, valid_679, valid_680, valid_681, valid_682, valid_683, valid_684, valid_685, valid_686, valid_687, valid_688, valid_689, valid_690, valid_691, valid_692, valid_693, valid_694, valid_695, valid_696, valid_697, valid_698, valid_699, valid_700, valid_701, valid_702, valid_703, True.intro⟩

end OAI.Snaky21.Certificate
