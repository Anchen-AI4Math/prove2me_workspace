import Definitions.Def_Snaky21Data07
import Solutions.Snaky21.Geometry
import Solutions.Snaky21.Certificate06

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace OAI.Snaky21.Certificate
open OAI.Snaky21 OAI.SnakyPrototype

theorem eq_card_448 : card_448 = combine (1, 3) [placed 6 (4, 6) card_56, placed 1 (0, 2) card_447] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_448 : Valid card_448 := by
  rw [eq_card_448]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 6) valid_56
  subst c
  exact placed_valid 1 (0, 2) valid_447

theorem eq_card_449 : card_449 = combine (4, 3) [placed 5 (1, 4) card_10, placed 1 (1, 3) card_27, placed 5 (1, 4) card_48, placed 5 (1, 4) card_63, placed 0 (0, 0) card_448] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_449 : Valid card_449 := by
  rw [eq_card_449]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 3) valid_27
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_48
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_63
  subst c
  exact placed_valid 0 (0, 0) valid_448

theorem eq_card_450 : card_450 = combine (3, 4) [placed 6 (5, 4) card_0, placed 2 (0, 7) card_448] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_450 : Valid card_450 := by
  rw [eq_card_450]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 4) valid_0
  subst c
  exact placed_valid 2 (0, 7) valid_448

theorem eq_inline_93 : inline_93 = combine (2, 3) [placed 6 (4, 3) card_0, placed 0 (0, 0) card_402] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_93 : Valid inline_93 := by
  rw [eq_inline_93]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 3) valid_0
  subst c
  exact placed_valid 0 (0, 0) valid_402

theorem eq_card_451 : card_451 = combine (1, 4) [placed 4 (1, 0) card_11, inline_93] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_451 : Valid card_451 := by
  rw [eq_card_451]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (1, 0) valid_11
  subst c
  exact valid_inline_93

theorem eq_inline_94 : inline_94 = combine (6, 4) [placed 6 (6, 4) card_5, placed 0 (3, 1) card_55] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_94 : Valid inline_94 := by
  rw [eq_inline_94]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 4) valid_5
  subst c
  exact placed_valid 0 (3, 1) valid_55

theorem eq_card_452 : card_452 = combine (4, 4) [placed 7 (6, 4) card_52, placed 0 (2, 0) card_317, inline_94] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_452 : Valid card_452 := by
  rw [eq_card_452]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 4) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 0) valid_317
  subst c
  exact valid_inline_94

theorem eq_inline_95 : inline_95 = combine (3, 3) [placed 4 (3, 0) card_21, placed 0 (2, 0) card_37, placed 3 (4, 0) card_354] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_95 : Valid inline_95 := by
  rw [eq_inline_95]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 0) valid_21
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 0) valid_37
  subst c
  exact placed_valid 3 (4, 0) valid_354

theorem eq_inline_96 : inline_96 = combine (3, 0) [placed 2 (0, 1) card_5, inline_95] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_96 : Valid inline_96 := by
  rw [eq_inline_96]
  apply combination_rule (3, 0) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 1) valid_5
  subst c
  exact valid_inline_95

theorem eq_card_453 : card_453 = combine (3, 2) [placed 0 (0, 1) card_5, inline_96] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_453 : Valid card_453 := by
  rw [eq_card_453]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_5
  subst c
  exact valid_inline_96

theorem eq_card_454 : card_454 = combine (1, 3) [placed 1 (1, 1) card_5, placed 5 (0, 4) card_453] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_454 : Valid card_454 := by
  rw [eq_card_454]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_5
  subst c
  exact placed_valid 5 (0, 4) valid_453

theorem eq_card_455 : card_455 = combine (1, 1) [placed 0 (0, 0) card_8, placed 1 (0, 1) card_16, placed 2 (0, 2) card_24, placed 0 (0, 0) card_453] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_455 : Valid card_455 := by
  rw [eq_card_455]
  apply combination_rule (1, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_16
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 2) valid_24
  subst c
  exact placed_valid 0 (0, 0) valid_453

theorem eq_card_456 : card_456 = combine (2, 4) [placed 1 (1, 1) card_5, placed 5 (0, 4) card_453] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_456 : Valid card_456 := by
  rw [eq_card_456]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_5
  subst c
  exact placed_valid 5 (0, 4) valid_453

theorem eq_card_457 : card_457 = combine (1, 4) [placed 0 (1, 0) card_7, placed 1 (0, 1) card_8, placed 4 (2, 0) card_9, placed 2 (0, 5) card_456] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_457 : Valid card_457 := by
  rw [eq_card_457]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 0) valid_9
  subst c
  exact placed_valid 2 (0, 5) valid_456

theorem eq_card_458 : card_458 = combine (1, 4) [placed 0 (1, 0) card_7, placed 0 (0, 0) card_9, placed 0 (0, 0) card_62, placed 0 (0, 0) card_456] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_458 : Valid card_458 := by
  rw [eq_card_458]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_9
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_62
  subst c
  exact placed_valid 0 (0, 0) valid_456

theorem eq_card_459 : card_459 = combine (1, 6) [placed 4 (2, 2) card_12, placed 4 (2, 2) card_13, placed 6 (2, 8) card_33, placed 4 (2, 2) card_189, placed 2 (0, 8) card_192, placed 4 (2, 1) card_369, placed 0 (0, 3) card_457, placed 2 (0, 7) card_458] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_459 : Valid card_459 := by
  rw [eq_card_459]
  apply combination_rule (1, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 2) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 2) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 6 (2, 8) valid_33
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 2) valid_189
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 8) valid_192
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 1) valid_369
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 3) valid_457
  subst c
  exact placed_valid 2 (0, 7) valid_458

theorem eq_card_460 : card_460 = combine (1, 4) [placed 0 (0, 1) card_13, placed 4 (2, 1) card_14, placed 0 (0, 1) card_33, placed 2 (0, 6) card_457, placed 0 (0, 2) card_458] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_460 : Valid card_460 := by
  rw [eq_card_460]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 1) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_33
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 6) valid_457
  subst c
  exact placed_valid 0 (0, 2) valid_458

theorem eq_card_461 : card_461 = combine (3, 3) [placed 3 (4, 1) card_28, placed 0 (0, 0) card_100, placed 0 (0, 0) card_429, placed 0 (2, 0) card_457] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_461 : Valid card_461 := by
  rw [eq_card_461]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (4, 1) valid_28
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_100
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_429
  subst c
  exact placed_valid 0 (2, 0) valid_457

theorem eq_card_462 : card_462 = combine (1, 5) [placed 4 (2, 1) card_13, placed 6 (2, 7) card_14, placed 2 (0, 7) card_31, placed 4 (2, 1) card_189, placed 2 (0, 7) card_367, placed 2 (0, 6) card_428, placed 0 (0, 2) card_457] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_462 : Valid card_462 := by
  rw [eq_card_462]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 1) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 6 (2, 7) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 7) valid_31
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 1) valid_189
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 7) valid_367
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 6) valid_428
  subst c
  exact placed_valid 0 (0, 2) valid_457

theorem eq_inline_97 : inline_97 = combine (2, 6) [placed 1 (1, 2) card_4, placed 1 (0, 3) card_348] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_97 : Valid inline_97 := by
  rw [eq_inline_97]
  apply combination_rule (2, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_4
  subst c
  exact placed_valid 1 (0, 3) valid_348

theorem eq_card_463 : card_463 = combine (4, 5) [placed 1 (0, 2) card_147, placed 1 (0, 2) card_167, inline_97, placed 0 (0, 0) card_353, placed 2 (3, 8) card_460] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_463 : Valid card_463 := by
  rw [eq_card_463]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_147
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_167
  rcases hc with rfl | hc
  · exact valid_inline_97
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_353
  subst c
  exact placed_valid 2 (3, 8) valid_460

theorem eq_inline_98 : inline_98 = combine (1, 1) [placed 3 (1, 0) card_0, placed 0 (1, 0) card_11] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_98 : Valid inline_98 := by
  rw [eq_inline_98]
  apply combination_rule (1, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (1, 0) valid_0
  subst c
  exact placed_valid 0 (1, 0) valid_11

theorem eq_inline_99 : inline_99 = combine (2, 2) [placed 4 (4, 2) card_0, inline_98] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_99 : Valid inline_99 := by
  rw [eq_inline_99]
  apply combination_rule (2, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_0
  subst c
  exact valid_inline_98

theorem eq_inline_100 : inline_100 = combine (1, 5) [placed 4 (1, 2) card_29, placed 5 (0, 5) card_38] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_100 : Valid inline_100 := by
  rw [eq_inline_100]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (1, 2) valid_29
  subst c
  exact placed_valid 5 (0, 5) valid_38

theorem eq_card_464 : card_464 = combine (1, 2) [placed 4 (1, 1) card_15, inline_99, inline_100] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_464 : Valid card_464 := by
  rw [eq_card_464]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (1, 1) valid_15
  rcases hc with rfl | hc
  · exact valid_inline_99
  subst c
  exact valid_inline_100

theorem eq_inline_101 : inline_101 = combine (3, 4) [placed 2 (0, 4) card_4, placed 0 (0, 4) card_4] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_101 : Valid inline_101 := by
  rw [eq_inline_101]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 4) valid_4
  subst c
  exact placed_valid 0 (0, 4) valid_4

theorem eq_inline_102 : inline_102 = combine (2, 4) [placed 1 (1, 1) card_5, inline_101] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_102 : Valid inline_102 := by
  rw [eq_inline_102]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_5
  subst c
  exact valid_inline_101

theorem eq_inline_103 : inline_103 = combine (0, 4) [placed 3 (1, 1) card_5, inline_102] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_103 : Valid inline_103 := by
  rw [eq_inline_103]
  apply combination_rule (0, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (1, 1) valid_5
  subst c
  exact valid_inline_102

theorem eq_inline_104 : inline_104 = combine (4, 5) [placed 0 (3, 1) card_39, placed 0 (3, 1) card_42, inline_103] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_104 : Valid inline_104 := by
  rw [eq_inline_104]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_39
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_42
  subst c
  exact valid_inline_103

theorem eq_card_465 : card_465 = combine (3, 2) [placed 5 (0, 4) card_25, inline_104] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_465 : Valid card_465 := by
  rw [eq_card_465]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_25
  subst c
  exact valid_inline_104

theorem eq_card_466 : card_466 = combine (1, 4) [placed 4 (1, 0) card_7, placed 1 (0, 1) card_8, placed 0 (0, 0) card_9, placed 0 (0, 0) card_465] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_466 : Valid card_466 := by
  rw [eq_card_466]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (1, 0) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_9
  subst c
  exact placed_valid 0 (0, 0) valid_465

theorem eq_card_467 : card_467 = combine (4, 6) [placed 6 (5, 8) card_31, placed 1 (1, 4) card_398, placed 6 (5, 7) card_444, placed 6 (5, 7) card_466] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_467 : Valid card_467 := by
  rw [eq_card_467]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 8) valid_31
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 4) valid_398
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 7) valid_444
  subst c
  exact placed_valid 6 (5, 7) valid_466

theorem eq_inline_105 : inline_105 = combine (3, 3) [placed 6 (4, 6) card_71, placed 4 (4, 2) card_71, placed 6 (4, 6) card_73, placed 4 (4, 2) card_73] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_105 : Valid inline_105 := by
  rw [eq_inline_105]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 6) valid_71
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_71
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 6) valid_73
  subst c
  exact placed_valid 4 (4, 2) valid_73

theorem eq_inline_106 : inline_106 = combine (3, 6) [placed 1 (2, 3) card_8, placed 4 (4, 3) card_17, placed 4 (4, 1) card_75, placed 0 (3, 1) card_266, placed 0 (2, 2) card_447] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_106 : Valid inline_106 := by
  rw [eq_inline_106]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 3) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 3) valid_17
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_75
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_266
  subst c
  exact placed_valid 0 (2, 2) valid_447

theorem eq_inline_107 : inline_107 = combine (3, 3) [placed 4 (4, 2) card_71, placed 6 (4, 6) card_73, placed 6 (5, 6) card_426, inline_106] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_107 : Valid inline_107 := by
  rw [eq_inline_107]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_71
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 6) valid_73
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 6) valid_426
  subst c
  exact valid_inline_106

theorem eq_inline_108 : inline_108 = combine (3, 5) [placed 5 (0, 5) card_54, inline_105, inline_107] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_108 : Valid inline_108 := by
  rw [eq_inline_108]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_54
  rcases hc with rfl | hc
  · exact valid_inline_105
  subst c
  exact valid_inline_107

theorem eq_card_468 : card_468 = combine (3, 4) [placed 1 (0, 3) card_28, placed 1 (0, 3) card_126, placed 5 (0, 5) card_126, inline_108] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_468 : Valid card_468 := by
  rw [eq_card_468]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_28
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_126
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_126
  subst c
  exact valid_inline_108

theorem eq_inline_109 : inline_109 = combine (2, 3) [placed 5 (0, 3) card_101, placed 3 (2, 1) card_314] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_109 : Valid inline_109 := by
  rw [eq_inline_109]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_101
  subst c
  exact placed_valid 3 (2, 1) valid_314

theorem eq_card_469 : card_469 = combine (3, 2) [placed 5 (0, 4) card_78, inline_109] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_469 : Valid card_469 := by
  rw [eq_card_469]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_78
  subst c
  exact valid_inline_109

theorem eq_inline_110 : inline_110 = combine (2, 3) [placed 6 (3, 6) card_54, placed 6 (4, 6) card_78] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_110 : Valid inline_110 := by
  rw [eq_inline_110]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (3, 6) valid_54
  subst c
  exact placed_valid 6 (4, 6) valid_78

theorem eq_inline_111 : inline_111 = combine (2, 3) [placed 7 (3, 6) card_2, placed 6 (4, 6) card_78] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_111 : Valid inline_111 := by
  rw [eq_inline_111]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (3, 6) valid_2
  subst c
  exact placed_valid 6 (4, 6) valid_78

theorem eq_inline_112 : inline_112 = combine (3, 6) [placed 2 (1, 8) card_56, inline_111] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_112 : Valid inline_112 := by
  rw [eq_inline_112]
  apply combination_rule (3, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 8) valid_56
  subst c
  exact valid_inline_111

theorem eq_card_470 : card_470 = combine (3, 3) [placed 0 (1, 0) card_319, placed 2 (1, 7) card_335, inline_110, inline_112] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_470 : Valid card_470 := by
  rw [eq_card_470]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_319
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 7) valid_335
  rcases hc with rfl | hc
  · exact valid_inline_110
  subst c
  exact valid_inline_112

theorem eq_inline_113 : inline_113 = combine (3, 4) [placed 4 (3, 0) card_11, placed 3 (4, 1) card_354] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_113 : Valid inline_113 := by
  rw [eq_inline_113]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 0) valid_11
  subst c
  exact placed_valid 3 (4, 1) valid_354

theorem eq_card_471 : card_471 = combine (3, 3) [placed 0 (0, 2) card_5, inline_113] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_471 : Valid card_471 := by
  rw [eq_card_471]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_5
  subst c
  exact valid_inline_113

theorem eq_card_472 : card_472 = combine (4, 3) [placed 0 (1, 2) card_5, placed 4 (4, 0) card_471] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_472 : Valid card_472 := by
  rw [eq_card_472]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_5
  subst c
  exact placed_valid 4 (4, 0) valid_471

theorem eq_card_473 : card_473 = combine (1, 1) [placed 6 (4, 2) card_5, placed 0 (0, 0) card_472] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_473 : Valid card_473 := by
  rw [eq_card_473]
  apply combination_rule (1, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 2) valid_5
  subst c
  exact placed_valid 0 (0, 0) valid_472

theorem eq_card_474 : card_474 = combine (4, 2) [placed 1 (0, 2) card_7, placed 0 (1, 1) card_8, placed 5 (0, 3) card_9, placed 4 (5, 0) card_473] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_474 : Valid card_474 := by
  rw [eq_card_474]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_9
  subst c
  exact placed_valid 4 (5, 0) valid_473

theorem eq_card_475 : card_475 = combine (2, 5) [placed 2 (1, 7) card_13, placed 6 (3, 7) card_14, placed 2 (1, 7) card_31, placed 2 (0, 8) card_396, placed 1 (0, 2) card_474] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_475 : Valid card_475 := by
  rw [eq_card_475]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 7) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 6 (3, 7) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 7) valid_31
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 8) valid_396
  subst c
  exact placed_valid 1 (0, 2) valid_474

theorem eq_card_476 : card_476 = combine (3, 5) [placed 0 (2, 1) card_12, placed 4 (4, 1) card_12, placed 2 (2, 7) card_12, placed 4 (4, 2) card_264, placed 5 (1, 6) card_474] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_476 : Valid card_476 := by
  rw [eq_card_476]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 1) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_264
  subst c
  exact placed_valid 5 (1, 6) valid_474

theorem eq_card_477 : card_477 = combine (4, 2) [placed 1 (0, 2) card_7, placed 1 (0, 1) card_9, placed 1 (0, 1) card_62, placed 0 (0, 0) card_473] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_477 : Valid card_477 := by
  rw [eq_card_477]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_9
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_62
  subst c
  exact placed_valid 0 (0, 0) valid_473

theorem eq_card_478 : card_478 = combine (2, 2) [placed 6 (4, 2) card_5, placed 0 (0, 0) card_472] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_478 : Valid card_478 := by
  rw [eq_card_478]
  apply combination_rule (2, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 2) valid_5
  subst c
  exact placed_valid 0 (0, 0) valid_472

theorem eq_inline_114 : inline_114 = combine (3, 2) [placed 7 (4, 5) card_8, placed 3 (5, 2) card_386] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_114 : Valid inline_114 := by
  rw [eq_inline_114]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 5) valid_8
  subst c
  exact placed_valid 3 (5, 2) valid_386

theorem eq_card_479 : card_479 = combine (3, 5) [placed 6 (4, 7) card_14, placed 2 (2, 7) card_31, placed 1 (1, 2) card_181, placed 2 (2, 7) card_367, inline_114, placed 3 (6, 2) card_435, placed 1 (1, 2) card_474] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_479 : Valid card_479 := by
  rw [eq_card_479]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 7) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_31
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_181
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_367
  rcases hc with rfl | hc
  · exact valid_inline_114
  rcases hc with rfl | hc
  · exact placed_valid 3 (6, 2) valid_435
  subst c
  exact placed_valid 1 (1, 2) valid_474

theorem eq_card_480 : card_480 = combine (3, 3) [placed 2 (2, 7) card_13, placed 2 (2, 7) card_14, placed 4 (4, 1) card_192, placed 1 (0, 1) card_298, placed 7 (6, 6) card_435, placed 7 (5, 6) card_474, placed 3 (5, 2) card_477] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_480 : Valid card_480 := by
  rw [eq_card_480]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_192
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_298
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 6) valid_435
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 6) valid_474
  subst c
  exact placed_valid 3 (5, 2) valid_477

theorem eq_card_481 : card_481 = combine (2, 4) [placed 0 (1, 1) card_13, placed 4 (3, 1) card_14, placed 0 (1, 1) card_33, placed 2 (1, 6) card_457, placed 1 (0, 2) card_477] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_481 : Valid card_481 := by
  rw [eq_card_481]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 1) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_33
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_457
  subst c
  exact placed_valid 1 (0, 2) valid_477

theorem eq_card_482 : card_482 = combine (2, 2) [placed 1 (0, 2) card_7, placed 0 (1, 1) card_24, placed 1 (0, 1) card_124, placed 0 (0, 0) card_472] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_482 : Valid card_482 := by
  rw [eq_card_482]
  apply combination_rule (2, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_24
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_124
  subst c
  exact placed_valid 0 (0, 0) valid_472

theorem eq_card_483 : card_483 = combine (2, 5) [placed 0 (1, 1) card_13, placed 4 (3, 1) card_14, placed 0 (1, 1) card_33, placed 0 (1, 2) card_458, placed 5 (0, 6) card_474] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_483 : Valid card_483 := by
  rw [eq_card_483]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 1) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_33
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_458
  subst c
  exact placed_valid 5 (0, 6) valid_474

theorem eq_inline_115 : inline_115 = combine (2, 2) [placed 5 (1, 5) card_5, placed 5 (0, 5) card_96] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_115 : Valid inline_115 := by
  rw [eq_inline_115]
  apply combination_rule (2, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 5) valid_5
  subst c
  exact placed_valid 5 (0, 5) valid_96

theorem eq_inline_116 : inline_116 = combine (4, 4) [placed 0 (3, 2) card_18, placed 2 (3, 7) card_33, placed 6 (4, 5) card_130] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_116 : Valid inline_116 := by
  rw [eq_inline_116]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_18
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 7) valid_33
  subst c
  exact placed_valid 6 (4, 5) valid_130

theorem eq_inline_117 : inline_117 = combine (2, 2) [placed 5 (1, 5) card_5, placed 5 (0, 5) card_223] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_117 : Valid inline_117 := by
  rw [eq_inline_117]
  apply combination_rule (2, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 5) valid_5
  subst c
  exact placed_valid 5 (0, 5) valid_223

theorem eq_inline_118 : inline_118 = combine (4, 2) [placed 0 (3, 1) card_39, placed 4 (5, 0) card_268, inline_117] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_118 : Valid inline_118 := by
  rw [eq_inline_118]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_39
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 0) valid_268
  subst c
  exact valid_inline_117

theorem eq_inline_119 : inline_119 = combine (3, 2) [inline_115, inline_116, inline_118] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_119 : Valid inline_119 := by
  rw [eq_inline_119]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact valid_inline_115
  rcases hc with rfl | hc
  · exact valid_inline_116
  subst c
  exact valid_inline_118

theorem eq_inline_120 : inline_120 = combine (4, 4) [placed 0 (1, 2) card_58, placed 6 (5, 6) card_168, placed 6 (4, 5) card_357] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_120 : Valid inline_120 := by
  rw [eq_inline_120]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_58
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 6) valid_168
  subst c
  exact placed_valid 6 (4, 5) valid_357

theorem eq_inline_121 : inline_121 = combine (2, 4) [placed 3 (2, 2) card_314, inline_120] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_121 : Valid inline_121 := by
  rw [eq_inline_121]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (2, 2) valid_314
  subst c
  exact valid_inline_120

theorem eq_card_484 : card_484 = combine (4, 5) [placed 1 (0, 2) card_81, placed 2 (0, 8) card_204, inline_119, inline_121] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_484 : Valid card_484 := by
  rw [eq_card_484]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_81
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 8) valid_204
  rcases hc with rfl | hc
  · exact valid_inline_119
  subst c
  exact valid_inline_121

theorem eq_inline_122 : inline_122 = combine (4, 5) [placed 1 (0, 2) card_81, placed 2 (0, 8) card_204, placed 0 (0, 0) card_353, placed 2 (2, 8) card_481] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_122 : Valid inline_122 := by
  rw [eq_inline_122]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_81
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 8) valid_204
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_353
  subst c
  exact placed_valid 2 (2, 8) valid_481

theorem eq_inline_123 : inline_123 = combine (4, 4) [placed 4 (5, 1) card_14, placed 0 (3, 1) card_189, placed 4 (5, 1) card_192, placed 4 (5, 1) card_193, placed 0 (3, 2) card_457, placed 5 (2, 6) card_477] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_123 : Valid inline_123 := by
  rw [eq_inline_123]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 1) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_189
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 1) valid_192
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 1) valid_193
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_457
  subst c
  exact placed_valid 5 (2, 6) valid_477

theorem eq_inline_124 : inline_124 = combine (2, 4) [placed 0 (1, 1) card_166, placed 3 (2, 2) card_314] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_124 : Valid inline_124 := by
  rw [eq_inline_124]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_166
  subst c
  exact placed_valid 3 (2, 2) valid_314

theorem eq_inline_125 : inline_125 = combine (4, 5) [placed 1 (0, 2) card_81, placed 1 (0, 2) card_167, inline_123, inline_124] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_125 : Valid inline_125 := by
  rw [eq_inline_125]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_81
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_167
  rcases hc with rfl | hc
  · exact valid_inline_123
  subst c
  exact valid_inline_124

theorem eq_card_485 : card_485 = combine (4, 3) [placed 5 (0, 5) card_313, placed 0 (0, 1) card_469, inline_122, inline_125, placed 0 (0, 0) card_484] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_485 : Valid card_485 := by
  rw [eq_card_485]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_313
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_469
  rcases hc with rfl | hc
  · exact valid_inline_122
  rcases hc with rfl | hc
  · exact valid_inline_125
  subst c
  exact placed_valid 0 (0, 0) valid_484

theorem eq_inline_126 : inline_126 = combine (1, 4) [placed 4 (4, 3) card_5, placed 5 (0, 4) card_156] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_126 : Valid inline_126 := by
  rw [eq_inline_126]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 3) valid_5
  subst c
  exact placed_valid 5 (0, 4) valid_156

theorem eq_inline_127 : inline_127 = combine (4, 2) [placed 2 (1, 3) card_5, inline_126] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_127 : Valid inline_127 := by
  rw [eq_inline_127]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 3) valid_5
  subst c
  exact valid_inline_126

theorem eq_inline_128 : inline_128 = combine (1, 2) [placed 6 (4, 3) card_5, inline_127] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_128 : Valid inline_128 := by
  rw [eq_inline_128]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 3) valid_5
  subst c
  exact valid_inline_127

theorem eq_card_486 : card_486 = combine (4, 3) [placed 1 (0, 2) card_19, placed 1 (0, 2) card_84, placed 0 (1, 2) card_314, inline_128] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_486 : Valid card_486 := by
  rw [eq_card_486]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_19
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_84
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_314
  subst c
  exact valid_inline_128

theorem eq_card_487 : card_487 = combine (2, 3) [placed 3 (3, 0) card_5, placed 0 (0, 0) card_486] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_487 : Valid card_487 := by
  rw [eq_card_487]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (3, 0) valid_5
  subst c
  exact placed_valid 0 (0, 0) valid_486

theorem eq_inline_129 : inline_129 = combine (1, 6) [placed 1 (1, 3) card_5, placed 5 (0, 6) card_34] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_129 : Valid inline_129 := by
  rw [eq_inline_129]
  apply combination_rule (1, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 3) valid_5
  subst c
  exact placed_valid 5 (0, 6) valid_34

theorem eq_inline_130 : inline_130 = combine (2, 6) [placed 1 (1, 2) card_4, inline_129] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_130 : Valid inline_130 := by
  rw [eq_inline_130]
  apply combination_rule (2, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 2) valid_4
  subst c
  exact valid_inline_129

theorem eq_inline_131 : inline_131 = combine (4, 4) [placed 0 (4, 2) card_7, placed 4 (5, 2) card_9, placed 0 (1, 3) card_357] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_131 : Valid inline_131 := by
  rw [eq_inline_131]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 2) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 2) valid_9
  subst c
  exact placed_valid 0 (1, 3) valid_357

theorem eq_card_488 : card_488 = combine (4, 6) [placed 6 (5, 9) card_95, inline_130, inline_131] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_488 : Valid card_488 := by
  rw [eq_card_488]
  apply combination_rule (4, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 9) valid_95
  rcases hc with rfl | hc
  · exact valid_inline_130
  subst c
  exact valid_inline_131

theorem eq_inline_132 : inline_132 = combine (5, 7) [placed 0 (4, 4) card_10, placed 6 (5, 8) card_44, placed 0 (4, 4) card_63, placed 5 (2, 8) card_486] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_132 : Valid inline_132 := by
  rw [eq_inline_132]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 4) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 8) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 4) valid_63
  subst c
  exact placed_valid 5 (2, 8) valid_486

theorem eq_inline_133 : inline_133 = combine (5, 6) [placed 0 (2, 5) card_5, inline_132] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_133 : Valid inline_133 := by
  rw [eq_inline_133]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 5) valid_5
  subst c
  exact valid_inline_132

theorem eq_inline_134 : inline_134 = combine (5, 8) [placed 0 (2, 4) card_81, placed 0 (2, 4) card_167, placed 3 (8, 6) card_481, placed 1 (0, 4) card_488] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_134 : Valid inline_134 := by
  rw [eq_inline_134]
  apply combination_rule (5, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 4) valid_81
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 4) valid_167
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 6) valid_481
  subst c
  exact placed_valid 1 (0, 4) valid_488

theorem eq_card_489 : card_489 = combine (3, 8) [placed 4 (5, 4) card_313, placed 2 (1, 10) card_470, inline_133, inline_134] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_489 : Valid card_489 := by
  rw [eq_card_489]
  apply combination_rule (3, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 4) valid_313
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 10) valid_470
  rcases hc with rfl | hc
  · exact valid_inline_133
  subst c
  exact valid_inline_134

theorem eq_card_490 : card_490 = combine (5, 7) [placed 0 (2, 3) card_321, placed 2 (2, 11) card_321, placed 1 (0, 6) card_485, placed 5 (0, 8) card_485, placed 0 (0, 2) card_489, placed 2 (0, 12) card_489] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_490 : Valid card_490 := by
  rw [eq_card_490]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 3) valid_321
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 11) valid_321
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 6) valid_485
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 8) valid_485
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_489
  subst c
  exact placed_valid 2 (0, 12) valid_489

theorem eq_inline_135 : inline_135 = combine (5, 3) [placed 5 (2, 4) card_60, placed 7 (6, 4) card_60, placed 2 (3, 4) card_83, placed 1 (1, 2) card_106] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_135 : Valid inline_135 := by
  rw [eq_inline_135]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 4) valid_60
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 4) valid_60
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 4) valid_83
  subst c
  exact placed_valid 1 (1, 2) valid_106

theorem eq_inline_136 : inline_136 = combine (5, 3) [placed 5 (2, 4) card_60, placed 7 (5, 3) card_70, placed 2 (2, 5) card_345] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_136 : Valid inline_136 := by
  rw [eq_inline_136]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 4) valid_60
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 3) valid_70
  subst c
  exact placed_valid 2 (2, 5) valid_345

theorem eq_card_491 : card_491 = combine (3, 3) [placed 4 (4, 0) card_44, placed 0 (1, 1) card_270, inline_135, inline_136] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_491 : Valid card_491 := by
  rw [eq_card_491]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 0) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_270
  rcases hc with rfl | hc
  · exact valid_inline_135
  subst c
  exact valid_inline_136

theorem eq_inline_137 : inline_137 = combine (2, 3) [placed 6 (4, 3) card_0, placed 3 (4, 1) card_32] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_137 : Valid inline_137 := by
  rw [eq_inline_137]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 3) valid_0
  subst c
  exact placed_valid 3 (4, 1) valid_32

theorem eq_inline_138 : inline_138 = combine (1, 3) [placed 7 (1, 5) card_0, inline_137] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_138 : Valid inline_138 := by
  rw [eq_inline_138]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 5) valid_0
  subst c
  exact valid_inline_137

theorem eq_card_492 : card_492 = combine (1, 2) [placed 7 (4, 4) card_78, inline_138] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_492 : Valid card_492 := by
  rw [eq_card_492]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 4) valid_78
  subst c
  exact valid_inline_138

theorem eq_card_493 : card_493 = combine (3, 3) [placed 0 (0, 0) card_87, placed 3 (4, 1) card_197, placed 0 (0, 0) card_492] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_493 : Valid card_493 := by
  rw [eq_card_493]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_87
  rcases hc with rfl | hc
  · exact placed_valid 3 (4, 1) valid_197
  subst c
  exact placed_valid 0 (0, 0) valid_492

theorem eq_card_494 : card_494 = combine (3, 3) [placed 0 (3, 0) card_7, placed 0 (0, 0) card_87, placed 0 (0, 0) card_286, placed 0 (0, 0) card_492] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_494 : Valid card_494 := by
  rw [eq_card_494]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 0) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_87
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_286
  subst c
  exact placed_valid 0 (0, 0) valid_492

theorem eq_inline_139 : inline_139 = combine (2, 2) [placed 3 (2, 2) card_5, placed 2 (0, 5) card_221] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_139 : Valid inline_139 := by
  rw [eq_inline_139]
  apply combination_rule (2, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (2, 2) valid_5
  subst c
  exact placed_valid 2 (0, 5) valid_221

theorem eq_card_495 : card_495 = combine (2, 4) [placed 0 (1, 2) card_10, placed 4 (2, 2) card_52, placed 6 (2, 6) card_52, inline_139] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_495 : Valid card_495 := by
  rw [eq_card_495]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 2) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 2) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 6 (2, 6) valid_52
  subst c
  exact valid_inline_139

theorem eq_inline_140 : inline_140 = combine (1, 2) [placed 5 (0, 5) card_0, placed 1 (0, 1) card_30] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_140 : Valid inline_140 := by
  rw [eq_inline_140]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 5) valid_0
  subst c
  exact placed_valid 1 (0, 1) valid_30

theorem eq_card_496 : card_496 = combine (1, 1) [placed 5 (0, 4) card_5, inline_140] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_496 : Valid card_496 := by
  rw [eq_card_496]
  apply combination_rule (1, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_5
  subst c
  exact valid_inline_140

theorem eq_card_497 : card_497 = combine (0, 3) [placed 1 (0, 1) card_5, placed 0 (0, 0) card_496] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_497 : Valid card_497 := by
  rw [eq_card_497]
  apply combination_rule (0, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_5
  subst c
  exact placed_valid 0 (0, 0) valid_496

theorem eq_card_498 : card_498 = combine (4, 3) [placed 1 (1, 1) card_114, placed 4 (4, 0) card_496] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_498 : Valid card_498 := by
  rw [eq_card_498]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_114
  subst c
  exact placed_valid 4 (4, 0) valid_496

theorem eq_inline_141 : inline_141 = combine (4, 3) [placed 6 (4, 3) card_1, placed 0 (1, 1) card_347] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_141 : Valid inline_141 := by
  rw [eq_inline_141]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 3) valid_1
  subst c
  exact placed_valid 0 (1, 1) valid_347

theorem eq_inline_142 : inline_142 = combine (3, 3) [placed 1 (0, 2) card_43, placed 0 (2, 0) card_52] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_142 : Valid inline_142 := by
  rw [eq_inline_142]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_43
  subst c
  exact placed_valid 0 (2, 0) valid_52

theorem eq_card_499 : card_499 = combine (2, 1) [placed 4 (2, 0) card_15, inline_141, inline_142] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_499 : Valid card_499 := by
  rw [eq_card_499]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 0) valid_15
  rcases hc with rfl | hc
  · exact valid_inline_141
  subst c
  exact valid_inline_142

theorem eq_inline_143 : inline_143 = combine (1, 1) [placed 3 (1, 1) card_5, placed 0 (0, 0) card_146] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_143 : Valid inline_143 := by
  rw [eq_inline_143]
  apply combination_rule (1, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (1, 1) valid_5
  subst c
  exact placed_valid 0 (0, 0) valid_146

theorem eq_card_500 : card_500 = combine (1, 2) [placed 7 (1, 5) card_0, inline_143] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_500 : Valid card_500 := by
  rw [eq_card_500]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 5) valid_0
  subst c
  exact valid_inline_143

theorem eq_card_501 : card_501 = combine (1, 3) [placed 4 (4, 3) card_2, placed 0 (0, 0) card_500] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_501 : Valid card_501 := by
  rw [eq_card_501]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 3) valid_2
  subst c
  exact placed_valid 0 (0, 0) valid_500

theorem eq_inline_144 : inline_144 = combine (2, 4) [placed 1 (0, 3) card_11, placed 2 (2, 6) card_53] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_144 : Valid inline_144 := by
  rw [eq_inline_144]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_11
  subst c
  exact placed_valid 2 (2, 6) valid_53

theorem eq_card_502 : card_502 = combine (4, 3) [placed 1 (0, 3) card_7, placed 2 (1, 5) card_69, inline_144] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_502 : Valid card_502 := by
  rw [eq_card_502]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 5) valid_69
  subst c
  exact valid_inline_144

theorem eq_card_503 : card_503 = combine (2, 3) [placed 2 (0, 3) card_0, placed 0 (0, 0) card_502] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_503 : Valid card_503 := by
  rw [eq_card_503]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 3) valid_0
  subst c
  exact placed_valid 0 (0, 0) valid_502

theorem eq_inline_145 : inline_145 = combine (2, 3) [placed 7 (3, 6) card_0, placed 1 (0, 1) card_56] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_145 : Valid inline_145 := by
  rw [eq_inline_145]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (3, 6) valid_0
  subst c
  exact placed_valid 1 (0, 1) valid_56

theorem eq_inline_146 : inline_146 = combine (3, 5) [placed 0 (3, 1) card_6, placed 0 (2, 2) card_18, inline_145] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_146 : Valid inline_146 := by
  rw [eq_inline_146]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_6
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_18
  subst c
  exact valid_inline_145

theorem eq_card_504 : card_504 = combine (3, 1) [placed 7 (4, 4) card_32, inline_146] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_504 : Valid card_504 := by
  rw [eq_card_504]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 4) valid_32
  subst c
  exact valid_inline_146

theorem eq_inline_147 : inline_147 = combine (4, 2) [placed 0 (1, 1) card_5, placed 0 (1, 0) card_350] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_147 : Valid inline_147 := by
  rw [eq_inline_147]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_5
  subst c
  exact placed_valid 0 (1, 0) valid_350

theorem eq_inline_148 : inline_148 = combine (4, 3) [placed 7 (4, 4) card_5, placed 0 (4, 1) card_6] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_148 : Valid inline_148 := by
  rw [eq_inline_148]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 4) valid_5
  subst c
  exact placed_valid 0 (4, 1) valid_6

theorem eq_inline_149 : inline_149 = combine (4, 2) [placed 0 (1, 1) card_5, inline_148] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_149 : Valid inline_149 := by
  rw [eq_inline_149]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_5
  subst c
  exact valid_inline_148

theorem eq_card_505 : card_505 = combine (4, 1) [placed 5 (0, 1) card_6, inline_147, inline_149] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_505 : Valid card_505 := by
  rw [eq_card_505]
  apply combination_rule (4, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 1) valid_6
  rcases hc with rfl | hc
  · exact valid_inline_147
  subst c
  exact valid_inline_149

theorem eq_inline_150 : inline_150 = combine (1, 2) [placed 2 (1, 6) card_7, placed 5 (0, 5) card_32] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_150 : Valid inline_150 := by
  rw [eq_inline_150]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_7
  subst c
  exact placed_valid 5 (0, 5) valid_32

theorem eq_card_506 : card_506 = combine (1, 5) [placed 2 (1, 6) card_44, placed 0 (0, 1) card_67, inline_150] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_506 : Valid card_506 := by
  rw [eq_card_506]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 6) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_67
  subst c
  exact valid_inline_150

theorem eq_inline_151 : inline_151 = combine (3, 5) [placed 6 (4, 7) card_33, placed 6 (3, 6) card_44, placed 5 (1, 6) card_47] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_151 : Valid inline_151 := by
  rw [eq_inline_151]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 7) valid_33
  rcases hc with rfl | hc
  · exact placed_valid 6 (3, 6) valid_44
  subst c
  exact placed_valid 5 (1, 6) valid_47

theorem eq_card_507 : card_507 = combine (3, 4) [placed 1 (0, 3) card_44, placed 0 (0, 0) card_274, placed 4 (4, 0) card_506, inline_151] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_507 : Valid card_507 := by
  rw [eq_card_507]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_274
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 0) valid_506
  subst c
  exact valid_inline_151

theorem eq_card_508 : card_508 = combine (4, 3) [placed 1 (0, 2) card_12, placed 1 (0, 2) card_13, placed 1 (0, 2) card_14, placed 0 (0, 0) card_297, placed 0 (0, 0) card_298, placed 2 (1, 5) card_474, placed 0 (1, 0) card_507] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_508 : Valid card_508 := by
  rw [eq_card_508]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_297
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_298
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 5) valid_474
  subst c
  exact placed_valid 0 (1, 0) valid_507

theorem eq_card_509 : card_509 = combine (4, 3) [placed 5 (0, 4) card_12, placed 1 (0, 2) card_127, placed 1 (0, 2) card_128, placed 0 (1, 1) card_474, placed 0 (1, 0) card_507] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_509 : Valid card_509 := by
  rw [eq_card_509]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_127
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_128
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_474
  subst c
  exact placed_valid 0 (1, 0) valid_507

theorem eq_inline_152 : inline_152 = combine (1, 4) [placed 4 (5, 3) card_0, placed 3 (4, 3) card_138] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_152 : Valid inline_152 := by
  rw [eq_inline_152]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 3) valid_0
  subst c
  exact placed_valid 3 (4, 3) valid_138

theorem eq_card_510 : card_510 = combine (4, 3) [placed 5 (1, 4) card_10, inline_152, placed 0 (1, 0) card_507] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_510 : Valid card_510 := by
  rw [eq_card_510]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_10
  rcases hc with rfl | hc
  · exact valid_inline_152
  subst c
  exact placed_valid 0 (1, 0) valid_507

theorem eq_inline_153 : inline_153 = combine (4, 4) [placed 6 (4, 4) card_2, placed 0 (3, 1) card_44] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_153 : Valid inline_153 := by
  rw [eq_inline_153]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 4) valid_2
  subst c
  exact placed_valid 0 (3, 1) valid_44

theorem eq_inline_154 : inline_154 = combine (3, 5) [placed 0 (3, 1) card_7, placed 4 (4, 1) card_9, placed 0 (1, 2) card_221] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_154 : Valid inline_154 := by
  rw [eq_inline_154]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_9
  subst c
  exact placed_valid 0 (1, 2) valid_221

theorem eq_inline_155 : inline_155 = combine (2, 4) [placed 6 (4, 4) card_0, inline_154] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_155 : Valid inline_155 := by
  rw [eq_inline_155]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 4) valid_0
  subst c
  exact valid_inline_154

theorem eq_inline_156 : inline_156 = combine (3, 4) [placed 4 (4, 0) card_13, placed 4 (4, 0) card_14, placed 0 (0, 1) card_240, inline_153, inline_155] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_156 : Valid inline_156 := by
  rw [eq_inline_156]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 0) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 0) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_240
  rcases hc with rfl | hc
  · exact valid_inline_153
  subst c
  exact valid_inline_155

theorem eq_card_511 : card_511 = combine (1, 4) [placed 6 (1, 5) card_15, inline_156] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_511 : Valid card_511 := by
  rw [eq_card_511]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (1, 5) valid_15
  subst c
  exact valid_inline_156

theorem block07_valid : Valid card_448 ∧ Valid card_449 ∧ Valid card_450 ∧ Valid card_451 ∧ Valid card_452 ∧ Valid card_453 ∧ Valid card_454 ∧ Valid card_455 ∧ Valid card_456 ∧ Valid card_457 ∧ Valid card_458 ∧ Valid card_459 ∧ Valid card_460 ∧ Valid card_461 ∧ Valid card_462 ∧ Valid card_463 ∧ Valid card_464 ∧ Valid card_465 ∧ Valid card_466 ∧ Valid card_467 ∧ Valid card_468 ∧ Valid card_469 ∧ Valid card_470 ∧ Valid card_471 ∧ Valid card_472 ∧ Valid card_473 ∧ Valid card_474 ∧ Valid card_475 ∧ Valid card_476 ∧ Valid card_477 ∧ Valid card_478 ∧ Valid card_479 ∧ Valid card_480 ∧ Valid card_481 ∧ Valid card_482 ∧ Valid card_483 ∧ Valid card_484 ∧ Valid card_485 ∧ Valid card_486 ∧ Valid card_487 ∧ Valid card_488 ∧ Valid card_489 ∧ Valid card_490 ∧ Valid card_491 ∧ Valid card_492 ∧ Valid card_493 ∧ Valid card_494 ∧ Valid card_495 ∧ Valid card_496 ∧ Valid card_497 ∧ Valid card_498 ∧ Valid card_499 ∧ Valid card_500 ∧ Valid card_501 ∧ Valid card_502 ∧ Valid card_503 ∧ Valid card_504 ∧ Valid card_505 ∧ Valid card_506 ∧ Valid card_507 ∧ Valid card_508 ∧ Valid card_509 ∧ Valid card_510 ∧ Valid card_511 ∧ True :=
  ⟨valid_448, valid_449, valid_450, valid_451, valid_452, valid_453, valid_454, valid_455, valid_456, valid_457, valid_458, valid_459, valid_460, valid_461, valid_462, valid_463, valid_464, valid_465, valid_466, valid_467, valid_468, valid_469, valid_470, valid_471, valid_472, valid_473, valid_474, valid_475, valid_476, valid_477, valid_478, valid_479, valid_480, valid_481, valid_482, valid_483, valid_484, valid_485, valid_486, valid_487, valid_488, valid_489, valid_490, valid_491, valid_492, valid_493, valid_494, valid_495, valid_496, valid_497, valid_498, valid_499, valid_500, valid_501, valid_502, valid_503, valid_504, valid_505, valid_506, valid_507, valid_508, valid_509, valid_510, valid_511, True.intro⟩

end OAI.Snaky21.Certificate
