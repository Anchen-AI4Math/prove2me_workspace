import Definitions.Def_Snaky21Data06
import Solutions.Snaky21.Geometry
import Solutions.Snaky21.Certificate05

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace OAI.Snaky21.Certificate
open OAI.Snaky21 OAI.SnakyPrototype

theorem eq_card_384 : card_384 = combine (3, 3) [placed 1 (2, 1) card_8, placed 7 (5, 4) card_383] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_384 : Valid card_384 := by
  rw [eq_card_384]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 1) valid_8
  subst c
  exact placed_valid 7 (5, 4) valid_383

theorem eq_card_385 : card_385 = combine (3, 3) [placed 1 (0, 1) card_115, placed 7 (5, 4) card_383] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_385 : Valid card_385 := by
  rw [eq_card_385]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_115
  subst c
  exact placed_valid 7 (5, 4) valid_383

theorem eq_inline_37 : inline_37 = combine (3, 4) [placed 3 (3, 1) card_5, placed 4 (3, 0) card_11] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_37 : Valid inline_37 := by
  rw [eq_inline_37]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (3, 1) valid_5
  subst c
  exact placed_valid 4 (3, 0) valid_11

theorem eq_inline_38 : inline_38 = combine (3, 3) [placed 0 (0, 2) card_5, inline_37] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_38 : Valid inline_38 := by
  rw [eq_inline_38]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_5
  subst c
  exact valid_inline_37

theorem eq_card_386 : card_386 = combine (3, 1) [placed 2 (0, 2) card_5, inline_38] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_386 : Valid card_386 := by
  rw [eq_card_386]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 2) valid_5
  subst c
  exact valid_inline_38

theorem eq_card_387 : card_387 = combine (4, 2) [placed 1 (0, 1) card_200, placed 1 (1, 0) card_376, placed 1 (0, 0) card_386] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_387 : Valid card_387 := by
  rw [eq_card_387]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_200
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 0) valid_376
  subst c
  exact placed_valid 1 (0, 0) valid_386

theorem eq_card_388 : card_388 = combine (2, 4) [placed 4 (2, 0) card_11, placed 0 (0, 1) card_387] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_388 : Valid card_388 := by
  rw [eq_card_388]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 0) valid_11
  subst c
  exact placed_valid 0 (0, 1) valid_387

theorem eq_inline_39 : inline_39 = combine (1, 3) [placed 1 (0, 0) card_5, placed 0 (0, 1) card_23] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_39 : Valid inline_39 := by
  rw [eq_inline_39]
  apply combination_rule (1, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 0) valid_5
  subst c
  exact placed_valid 0 (0, 1) valid_23

theorem eq_card_389 : card_389 = combine (0, 4) [placed 0 (0, 0) card_6, placed 0 (0, 1) card_21, placed 0 (0, 1) card_27, inline_39] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_389 : Valid card_389 := by
  rw [eq_card_389]
  apply combination_rule (0, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_6
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_21
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_27
  subst c
  exact valid_inline_39

theorem eq_card_390 : card_390 = combine (1, 7) [placed 4 (1, 3) card_11, placed 0 (0, 4) card_17, placed 6 (1, 7) card_389] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_390 : Valid card_390 := by
  rw [eq_card_390]
  apply combination_rule (1, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (1, 3) valid_11
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 4) valid_17
  subst c
  exact placed_valid 6 (1, 7) valid_389

theorem eq_inline_40 : inline_40 = combine (3, 1) [placed 4 (4, 1) card_0, placed 2 (2, 4) card_36] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_40 : Valid inline_40 := by
  rw [eq_inline_40]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_0
  subst c
  exact placed_valid 2 (2, 4) valid_36

theorem eq_inline_41 : inline_41 = combine (2, 1) [placed 5 (1, 4) card_5, inline_40] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_41 : Valid inline_41 := by
  rw [eq_inline_41]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_5
  subst c
  exact valid_inline_40

theorem eq_card_391 : card_391 = combine (2, 4) [placed 1 (1, 1) card_5, inline_41] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_391 : Valid card_391 := by
  rw [eq_card_391]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_5
  subst c
  exact valid_inline_41

theorem eq_card_392 : card_392 = combine (3, 3) [placed 6 (4, 3) card_0, placed 0 (0, 0) card_391] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_392 : Valid card_392 := by
  rw [eq_card_392]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 3) valid_0
  subst c
  exact placed_valid 0 (0, 0) valid_391

theorem eq_card_393 : card_393 = combine (1, 4) [placed 0 (1, 0) card_11, placed 0 (0, 1) card_20, placed 2 (0, 5) card_391] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_393 : Valid card_393 := by
  rw [eq_card_393]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_11
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_20
  subst c
  exact placed_valid 2 (0, 5) valid_391

theorem eq_card_394 : card_394 = combine (1, 4) [placed 0 (0, 1) card_17, placed 0 (0, 0) card_241, placed 0 (0, 0) card_392] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_394 : Valid card_394 := by
  rw [eq_card_394]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_17
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_241
  subst c
  exact placed_valid 0 (0, 0) valid_392

theorem eq_inline_42 : inline_42 = combine (3, 1) [placed 2 (0, 2) card_5, placed 0 (1, 0) card_217] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_42 : Valid inline_42 := by
  rw [eq_inline_42]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 2) valid_5
  subst c
  exact placed_valid 0 (1, 0) valid_217

theorem eq_card_395 : card_395 = combine (3, 3) [placed 0 (0, 2) card_5, inline_42] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_395 : Valid card_395 := by
  rw [eq_card_395]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_5
  subst c
  exact valid_inline_42

theorem eq_card_396 : card_396 = combine (2, 6) [placed 4 (2, 2) card_7, placed 4 (3, 2) card_9, placed 5 (0, 6) card_395] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_396 : Valid card_396 := by
  rw [eq_card_396]
  apply combination_rule (2, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 2) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 2) valid_9
  subst c
  exact placed_valid 5 (0, 6) valid_395

theorem eq_card_397 : card_397 = combine (3, 3) [placed 0 (0, 2) card_8, placed 0 (0, 0) card_161, placed 0 (0, 0) card_162, placed 0 (0, 1) card_395] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_397 : Valid card_397 := by
  rw [eq_card_397]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_161
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_162
  subst c
  exact placed_valid 0 (0, 1) valid_395

theorem eq_card_398 : card_398 = combine (3, 3) [placed 0 (0, 0) card_171, placed 0 (0, 2) card_197, placed 2 (0, 4) card_197, placed 0 (0, 0) card_285, placed 0 (0, 1) card_395] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_398 : Valid card_398 := by
  rw [eq_card_398]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_171
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_197
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 4) valid_197
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_285
  subst c
  exact placed_valid 0 (0, 1) valid_395

theorem eq_card_399 : card_399 = combine (2, 5) [placed 0 (1, 1) card_12, placed 0 (0, 1) card_135, placed 1 (0, 2) card_181, placed 0 (0, 0) card_396, placed 2 (0, 8) card_396] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_399 : Valid card_399 := by
  rw [eq_card_399]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_135
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_181
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_396
  subst c
  exact placed_valid 2 (0, 8) valid_396

theorem eq_card_400 : card_400 = combine (3, 2) [placed 6 (4, 2) card_5, placed 0 (1, 0) card_395] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_400 : Valid card_400 := by
  rw [eq_card_400]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 2) valid_5
  subst c
  exact placed_valid 0 (1, 0) valid_395

theorem eq_card_401 : card_401 = combine (2, 4) [placed 6 (4, 4) card_3, placed 2 (2, 7) card_397] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_401 : Valid card_401 := by
  rw [eq_card_401]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 4) valid_3
  subst c
  exact placed_valid 2 (2, 7) valid_397

theorem eq_inline_43 : inline_43 = combine (2, 4) [placed 3 (3, 0) card_0, placed 1 (1, 1) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_43 : Valid inline_43 := by
  rw [eq_inline_43]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (3, 0) valid_0
  subst c
  exact placed_valid 1 (1, 1) valid_5

theorem eq_card_402 : card_402 = combine (3, 1) [placed 5 (0, 4) card_38, inline_43] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_402 : Valid card_402 := by
  rw [eq_card_402]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_38
  subst c
  exact valid_inline_43

theorem eq_inline_44 : inline_44 = combine (2, 5) [placed 3 (3, 1) card_4, placed 3 (4, 2) card_381] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_44 : Valid inline_44 := by
  rw [eq_inline_44]
  apply combination_rule (2, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (3, 1) valid_4
  subst c
  exact placed_valid 3 (4, 2) valid_381

theorem eq_card_403 : card_403 = combine (1, 5) [placed 0 (0, 0) card_86, inline_44] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_403 : Valid card_403 := by
  rw [eq_card_403]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_86
  subst c
  exact valid_inline_44

theorem eq_inline_45 : inline_45 = combine (3, 1) [placed 4 (4, 1) card_0, placed 0 (0, 0) card_354] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_45 : Valid inline_45 := by
  rw [eq_inline_45]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_0
  subst c
  exact placed_valid 0 (0, 0) valid_354

theorem eq_inline_46 : inline_46 = combine (2, 1) [placed 5 (1, 4) card_5, inline_45] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_46 : Valid inline_46 := by
  rw [eq_inline_46]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_5
  subst c
  exact valid_inline_45

theorem eq_card_404 : card_404 = combine (2, 4) [placed 1 (1, 1) card_5, inline_46] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_404 : Valid card_404 := by
  rw [eq_card_404]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_5
  subst c
  exact valid_inline_46

theorem eq_card_405 : card_405 = combine (1, 4) [placed 7 (1, 5) card_0, placed 0 (0, 0) card_404] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_405 : Valid card_405 := by
  rw [eq_card_405]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 5) valid_0
  subst c
  exact placed_valid 0 (0, 0) valid_404

theorem eq_card_406 : card_406 = combine (1, 4) [placed 0 (0, 0) card_199, placed 2 (0, 6) card_199, placed 0 (0, 1) card_405, placed 2 (0, 5) card_405] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_406 : Valid card_406 := by
  rw [eq_card_406]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_199
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 6) valid_199
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_405
  subst c
  exact placed_valid 2 (0, 5) valid_405

theorem eq_inline_47 : inline_47 = combine (0, 4) [placed 3 (1, 1) card_5, placed 2 (0, 5) card_404] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_47 : Valid inline_47 := by
  rw [eq_inline_47]
  apply combination_rule (0, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (1, 1) valid_5
  subst c
  exact placed_valid 2 (0, 5) valid_404

theorem eq_card_407 : card_407 = combine (1, 4) [placed 0 (1, 0) card_7, placed 1 (0, 1) card_8, placed 4 (2, 0) card_9, inline_47] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_407 : Valid card_407 := by
  rw [eq_card_407]
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
  exact valid_inline_47

theorem eq_card_408 : card_408 = combine (1, 5) [placed 6 (1, 6) card_44, placed 0 (0, 1) card_127, placed 2 (0, 6) card_407] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_408 : Valid card_408 := by
  rw [eq_card_408]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (1, 6) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_127
  subst c
  exact placed_valid 2 (0, 6) valid_407

theorem eq_card_409 : card_409 = combine (1, 4) [placed 6 (1, 6) card_44, placed 0 (0, 1) card_127, placed 2 (0, 6) card_407] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_409 : Valid card_409 := by
  rw [eq_card_409]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (1, 6) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_127
  subst c
  exact placed_valid 2 (0, 6) valid_407

theorem eq_card_410 : card_410 = combine (1, 5) [placed 0 (0, 2) card_10, placed 4 (2, 1) card_12, placed 2 (0, 7) card_12, placed 2 (0, 6) card_407] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_410 : Valid card_410 := by
  rw [eq_card_410]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 1) valid_12
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 7) valid_12
  subst c
  exact placed_valid 2 (0, 6) valid_407

theorem eq_card_411 : card_411 = combine (1, 5) [placed 6 (1, 6) card_15, placed 2 (0, 7) card_65, placed 2 (0, 6) card_407] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_411 : Valid card_411 := by
  rw [eq_card_411]
  apply combination_rule (1, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (1, 6) valid_15
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 7) valid_65
  subst c
  exact placed_valid 2 (0, 6) valid_407

theorem eq_inline_48 : inline_48 = combine (3, 1) [placed 4 (4, 1) card_0, placed 0 (0, 0) card_358] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_48 : Valid inline_48 := by
  rw [eq_inline_48]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_0
  subst c
  exact placed_valid 0 (0, 0) valid_358

theorem eq_card_412 : card_412 = combine (2, 1) [placed 5 (1, 4) card_5, inline_48] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_412 : Valid card_412 := by
  rw [eq_card_412]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_5
  subst c
  exact valid_inline_48

theorem eq_inline_49 : inline_49 = combine (2, 3) [placed 7 (2, 4) card_5, placed 1 (0, 1) card_45] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_49 : Valid inline_49 := by
  rw [eq_inline_49]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (2, 4) valid_5
  subst c
  exact placed_valid 1 (0, 1) valid_45

theorem eq_card_413 : card_413 = combine (2, 4) [placed 1 (1, 1) card_5, inline_49] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_413 : Valid card_413 := by
  rw [eq_card_413]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_5
  subst c
  exact valid_inline_49

theorem eq_card_414 : card_414 = combine (1, 4) [placed 5 (1, 5) card_0, placed 0 (0, 0) card_413] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_414 : Valid card_414 := by
  rw [eq_card_414]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 5) valid_0
  subst c
  exact placed_valid 0 (0, 0) valid_413

theorem eq_card_415 : card_415 = combine (3, 2) [placed 2 (0, 2) card_2, placed 4 (5, 0) card_414] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_415 : Valid card_415 := by
  rw [eq_card_415]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 2) valid_2
  subst c
  exact placed_valid 4 (5, 0) valid_414

theorem eq_inline_50 : inline_50 = combine (3, 1) [placed 2 (0, 2) card_5, placed 2 (0, 5) card_239] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_50 : Valid inline_50 := by
  rw [eq_inline_50]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 2) valid_5
  subst c
  exact placed_valid 2 (0, 5) valid_239

theorem eq_card_416 : card_416 = combine (3, 3) [placed 0 (0, 2) card_5, inline_50] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_416 : Valid card_416 := by
  rw [eq_card_416]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_5
  subst c
  exact valid_inline_50

theorem eq_card_417 : card_417 = combine (3, 2) [placed 4 (4, 2) card_0, placed 0 (0, 0) card_416] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_417 : Valid card_417 := by
  rw [eq_card_417]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_0
  subst c
  exact placed_valid 0 (0, 0) valid_416

theorem eq_inline_51 : inline_51 = combine (2, 2) [placed 0 (0, 2) card_5, placed 4 (3, 0) card_29] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_51 : Valid inline_51 := by
  rw [eq_inline_51]
  apply combination_rule (2, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_5
  subst c
  exact placed_valid 4 (3, 0) valid_29

theorem eq_inline_52 : inline_52 = combine (3, 3) [placed 1 (2, 0) card_8, placed 3 (4, 0) card_25, placed 0 (2, 0) card_41, inline_51] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_52 : Valid inline_52 := by
  rw [eq_inline_52]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 0) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 3 (4, 0) valid_25
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 0) valid_41
  subst c
  exact valid_inline_51

theorem eq_inline_53 : inline_53 = combine (3, 2) [placed 0 (0, 1) card_5, inline_52] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_53 : Valid inline_53 := by
  rw [eq_inline_53]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_5
  subst c
  exact valid_inline_52

theorem eq_card_418 : card_418 = combine (3, 0) [placed 2 (0, 1) card_5, inline_53] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_418 : Valid card_418 := by
  rw [eq_card_418]
  apply combination_rule (3, 0) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 1) valid_5
  subst c
  exact valid_inline_53

theorem eq_card_419 : card_419 = combine (2, 1) [placed 5 (1, 4) card_5, placed 1 (0, 1) card_418] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_419 : Valid card_419 := by
  rw [eq_card_419]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_5
  subst c
  exact placed_valid 1 (0, 1) valid_418

theorem eq_card_420 : card_420 = combine (3, 1) [placed 4 (4, 1) card_0, placed 0 (0, 0) card_418] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_420 : Valid card_420 := by
  rw [eq_card_420]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_0
  subst c
  exact placed_valid 0 (0, 0) valid_418

theorem eq_card_421 : card_421 = combine (1, 4) [placed 1 (0, 1) card_8, placed 0 (1, 0) card_11, placed 0 (0, 0) card_419] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_421 : Valid card_421 := by
  rw [eq_card_421]
  apply combination_rule (1, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 1) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_11
  subst c
  exact placed_valid 0 (0, 0) valid_419

theorem eq_inline_54 : inline_54 = combine (4, 2) [placed 0 (1, 0) card_69, placed 3 (5, 1) card_413] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_54 : Valid inline_54 := by
  rw [eq_inline_54]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 0) valid_69
  subst c
  exact placed_valid 3 (5, 1) valid_413

theorem eq_card_422 : card_422 = combine (2, 2) [placed 0 (0, 2) card_0, inline_54] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_422 : Valid card_422 := by
  rw [eq_card_422]
  apply combination_rule (2, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_0
  subst c
  exact valid_inline_54

theorem eq_inline_55 : inline_55 = combine (1, 2) [placed 6 (4, 3) card_5, placed 0 (0, 0) card_244] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_55 : Valid inline_55 := by
  rw [eq_inline_55]
  apply combination_rule (1, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 3) valid_5
  subst c
  exact placed_valid 0 (0, 0) valid_244

theorem eq_card_423 : card_423 = combine (2, 3) [placed 2 (1, 5) card_383, inline_55] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_423 : Valid card_423 := by
  rw [eq_card_423]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 5) valid_383
  subst c
  exact valid_inline_55

theorem eq_inline_56 : inline_56 = combine (4, 2) [placed 2 (0, 3) card_2, placed 0 (3, 0) card_11] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_56 : Valid inline_56 := by
  rw [eq_inline_56]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 3) valid_2
  subst c
  exact placed_valid 0 (3, 0) valid_11

theorem eq_card_424 : card_424 = combine (3, 4) [placed 0 (3, 0) card_7, placed 3 (4, 1) card_25, inline_56] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_424 : Valid card_424 := by
  rw [eq_card_424]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 0) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 3 (4, 1) valid_25
  subst c
  exact valid_inline_56

theorem eq_inline_57 : inline_57 = combine (3, 2) [placed 0 (0, 2) card_2, placed 0 (3, 0) card_44] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_57 : Valid inline_57 := by
  rw [eq_inline_57]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_2
  subst c
  exact placed_valid 0 (3, 0) valid_44

theorem eq_card_425 : card_425 = combine (4, 3) [placed 6 (4, 3) card_2, inline_57] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_425 : Valid card_425 := by
  rw [eq_card_425]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 3) valid_2
  subst c
  exact valid_inline_57

theorem eq_inline_58 : inline_58 = combine (3, 3) [placed 6 (5, 3) card_0, placed 4 (4, 1) card_221] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_58 : Valid inline_58 := by
  rw [eq_inline_58]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 3) valid_0
  subst c
  exact placed_valid 4 (4, 1) valid_221

theorem eq_card_426 : card_426 = combine (2, 4) [placed 4 (2, 0) card_11, inline_58] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_426 : Valid card_426 := by
  rw [eq_card_426]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (2, 0) valid_11
  subst c
  exact valid_inline_58

theorem eq_inline_59 : inline_59 = combine (4, 3) [placed 5 (0, 4) card_70, placed 0 (1, 0) card_226] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_59 : Valid inline_59 := by
  rw [eq_inline_59]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_70
  subst c
  exact placed_valid 0 (1, 0) valid_226

theorem eq_inline_60 : inline_60 = combine (4, 1) [placed 0 (1, 1) card_5, inline_59] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_60 : Valid inline_60 := by
  rw [eq_inline_60]
  apply combination_rule (4, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_5
  subst c
  exact valid_inline_59

theorem eq_inline_61 : inline_61 = combine (4, 2) [placed 0 (0, 1) card_4, inline_60] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_61 : Valid inline_61 := by
  rw [eq_inline_61]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_4
  subst c
  exact valid_inline_60

theorem eq_inline_62 : inline_62 = combine (3, 3) [placed 4 (4, 3) card_0, placed 3 (3, 0) card_2] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_62 : Valid inline_62 := by
  rw [eq_inline_62]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 3) valid_0
  subst c
  exact placed_valid 3 (3, 0) valid_2

theorem eq_inline_63 : inline_63 = combine (2, 3) [placed 5 (2, 4) card_2, inline_62] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_63 : Valid inline_63 := by
  rw [eq_inline_63]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 4) valid_2
  subst c
  exact valid_inline_62

theorem eq_inline_64 : inline_64 = combine (3, 0) [placed 5 (0, 1) card_52, inline_63] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_64 : Valid inline_64 := by
  rw [eq_inline_64]
  apply combination_rule (3, 0) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 1) valid_52
  subst c
  exact valid_inline_63

theorem eq_inline_65 : inline_65 = combine (3, 1) [placed 5 (0, 2) card_17, placed 5 (0, 4) card_357, inline_61, inline_64] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_65 : Valid inline_65 := by
  rw [eq_inline_65]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 2) valid_17
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 4) valid_357
  rcases hc with rfl | hc
  · exact valid_inline_61
  subst c
  exact valid_inline_64

theorem eq_inline_66 : inline_66 = combine (0, 1) [placed 7 (1, 4) card_5, inline_65] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_66 : Valid inline_66 := by
  rw [eq_inline_66]
  apply combination_rule (0, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_5
  subst c
  exact valid_inline_65

theorem eq_inline_67 : inline_67 = combine (0, 4) [placed 3 (1, 1) card_5, inline_66] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_67 : Valid inline_67 := by
  rw [eq_inline_67]
  apply combination_rule (0, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (1, 1) valid_5
  subst c
  exact valid_inline_66

theorem eq_inline_68 : inline_68 = combine (2, 4) [placed 1 (1, 1) card_5, inline_67] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_68 : Valid inline_68 := by
  rw [eq_inline_68]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_5
  subst c
  exact valid_inline_67

theorem eq_card_427 : card_427 = combine (2, 1) [placed 5 (1, 4) card_5, inline_68] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_427 : Valid card_427 := by
  rw [eq_card_427]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_5
  subst c
  exact valid_inline_68

theorem eq_card_428 : card_428 = combine (1, 4) [placed 0 (1, 0) card_7, placed 1 (0, 1) card_8, placed 4 (2, 0) card_9, placed 2 (0, 5) card_427] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_428 : Valid card_428 := by
  rw [eq_card_428]
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
  exact placed_valid 2 (0, 5) valid_427

theorem eq_inline_69 : inline_69 = combine (4, 3) [placed 0 (0, 2) card_2, placed 3 (5, 1) card_46] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_69 : Valid inline_69 := by
  rw [eq_inline_69]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_2
  subst c
  exact placed_valid 3 (5, 1) valid_46

theorem eq_card_429 : card_429 = combine (3, 4) [placed 4 (3, 0) card_7, placed 1 (2, 1) card_8, placed 0 (2, 0) card_9, inline_69] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_429 : Valid card_429 := by
  rw [eq_card_429]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 0) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 1) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 0) valid_9
  subst c
  exact valid_inline_69

theorem eq_card_430 : card_430 = combine (3, 5) [placed 2 (2, 7) card_14, placed 2 (2, 7) card_31, placed 0 (0, 2) card_58, placed 2 (0, 6) card_100, placed 0 (0, 2) card_429] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_430 : Valid card_430 := by
  rw [eq_card_430]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 7) valid_31
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_58
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 6) valid_100
  subst c
  exact placed_valid 0 (0, 2) valid_429

theorem eq_card_431 : card_431 = combine (4, 4) [placed 7 (5, 4) card_160, placed 4 (5, 0) card_243, placed 0 (1, 1) card_429] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_431 : Valid card_431 := by
  rw [eq_card_431]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 4) valid_160
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 0) valid_243
  subst c
  exact placed_valid 0 (1, 1) valid_429

theorem eq_inline_70 : inline_70 = combine (4, 1) [placed 2 (1, 1) card_5, placed 3 (5, 0) card_146] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_70 : Valid inline_70 := by
  rw [eq_inline_70]
  apply combination_rule (4, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 1) valid_5
  subst c
  exact placed_valid 3 (5, 0) valid_146

theorem eq_card_432 : card_432 = combine (4, 0) [placed 2 (0, 1) card_4, inline_70] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_432 : Valid card_432 := by
  rw [eq_card_432]
  apply combination_rule (4, 0) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 1) valid_4
  subst c
  exact valid_inline_70

theorem eq_card_433 : card_433 = combine (3, 4) [placed 0 (0, 0) card_86, placed 3 (4, 1) card_432] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_433 : Valid card_433 := by
  rw [eq_card_433]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 0) valid_86
  subst c
  exact placed_valid 3 (4, 1) valid_432

theorem eq_inline_71 : inline_71 = combine (5, 1) [placed 2 (1, 2) card_1, placed 4 (5, 0) card_10] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_71 : Valid inline_71 := by
  rw [eq_inline_71]
  apply combination_rule (5, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 2) valid_1
  subst c
  exact placed_valid 4 (5, 0) valid_10

theorem eq_inline_72 : inline_72 = combine (4, 4) [placed 3 (5, 1) card_8, placed 0 (3, 1) card_41, placed 1 (1, 1) card_253, placed 3 (7, 1) card_256, placed 0 (3, 1) card_336] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_72 : Valid inline_72 := by
  rw [eq_inline_72]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 1) valid_8
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 1) valid_41
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_253
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 1) valid_256
  subst c
  exact placed_valid 0 (3, 1) valid_336

theorem eq_card_434 : card_434 = combine (3, 2) [placed 3 (5, 1) card_80, inline_71, inline_72] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_434 : Valid card_434 := by
  rw [eq_card_434]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 1) valid_80
  rcases hc with rfl | hc
  · exact valid_inline_71
  subst c
  exact valid_inline_72

theorem eq_inline_73 : inline_73 = combine (3, 2) [placed 2 (0, 3) card_0, placed 4 (4, 1) card_212] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_73 : Valid inline_73 := by
  rw [eq_inline_73]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 3) valid_0
  subst c
  exact placed_valid 4 (4, 1) valid_212

theorem eq_inline_74 : inline_74 = combine (3, 2) [placed 5 (3, 5) card_5, placed 4 (3, 1) card_11] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_74 : Valid inline_74 := by
  rw [eq_inline_74]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 5) valid_5
  subst c
  exact placed_valid 4 (3, 1) valid_11

theorem eq_inline_75 : inline_75 = combine (3, 5) [placed 4 (4, 2) card_76, placed 2 (3, 5) card_130, inline_74] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_75 : Valid inline_75 := by
  rw [eq_inline_75]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 2) valid_76
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 5) valid_130
  subst c
  exact valid_inline_74

theorem eq_inline_76 : inline_76 = combine (3, 4) [placed 1 (0, 3) card_52, placed 3 (4, 2) card_76, inline_73, inline_75] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_76 : Valid inline_76 := by
  rw [eq_inline_76]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 3 (4, 2) valid_76
  rcases hc with rfl | hc
  · exact valid_inline_73
  subst c
  exact valid_inline_75

theorem eq_card_435 : card_435 = combine (4, 2) [placed 5 (1, 3) card_130, placed 5 (0, 3) card_140, placed 2 (0, 5) card_183, inline_76] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_435 : Valid card_435 := by
  rw [eq_card_435]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 3) valid_130
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 3) valid_140
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 5) valid_183
  subst c
  exact valid_inline_76

theorem eq_card_436 : card_436 = combine (3, 5) [placed 0 (2, 2) card_10, placed 5 (1, 6) card_47, placed 6 (3, 6) card_52, placed 3 (6, 2) card_435] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_436 : Valid card_436 := by
  rw [eq_card_436]
  apply combination_rule (3, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 6) valid_47
  rcases hc with rfl | hc
  · exact placed_valid 6 (3, 6) valid_52
  subst c
  exact placed_valid 3 (6, 2) valid_435

theorem eq_card_437 : card_437 = combine (3, 4) [placed 0 (2, 2) card_10, placed 5 (1, 6) card_47, placed 6 (3, 6) card_52, placed 3 (6, 2) card_435] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_437 : Valid card_437 := by
  rw [eq_card_437]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 6) valid_47
  rcases hc with rfl | hc
  · exact placed_valid 6 (3, 6) valid_52
  subst c
  exact placed_valid 3 (6, 2) valid_435

theorem eq_card_438 : card_438 = combine (4, 3) [placed 7 (6, 4) card_10, placed 6 (6, 5) card_47, placed 0 (2, 0) card_436] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_438 : Valid card_438 := by
  rw [eq_card_438]
  apply combination_rule (4, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 4) valid_10
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 5) valid_47
  subst c
  exact placed_valid 0 (2, 0) valid_436

theorem eq_inline_77 : inline_77 = combine (4, 2) [placed 6 (4, 2) card_2, placed 5 (3, 5) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_77 : Valid inline_77 := by
  rw [eq_inline_77]
  apply combination_rule (4, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 2) valid_2
  subst c
  exact placed_valid 5 (3, 5) valid_5

theorem eq_inline_78 : inline_78 = combine (4, 1) [placed 5 (3, 4) card_5, placed 4 (4, 1) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_78 : Valid inline_78 := by
  rw [eq_inline_78]
  apply combination_rule (4, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 4) valid_5
  subst c
  exact placed_valid 4 (4, 1) valid_5

theorem eq_inline_79 : inline_79 = combine (3, 1) [placed 7 (3, 4) card_5, inline_78] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_79 : Valid inline_79 := by
  rw [eq_inline_79]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (3, 4) valid_5
  subst c
  exact valid_inline_78

theorem eq_inline_80 : inline_80 = combine (2, 1) [placed 7 (3, 5) card_4, inline_79] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_80 : Valid inline_80 := by
  rw [eq_inline_80]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (3, 5) valid_4
  subst c
  exact valid_inline_79

theorem eq_inline_81 : inline_81 = combine (3, 2) [placed 7 (4, 5) card_251, placed 7 (4, 5) card_432, inline_77, inline_80] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_81 : Valid inline_81 := by
  rw [eq_inline_81]
  apply combination_rule (3, 2) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 5) valid_251
  rcases hc with rfl | hc
  · exact placed_valid 7 (4, 5) valid_432
  rcases hc with rfl | hc
  · exact valid_inline_77
  subst c
  exact valid_inline_80

theorem eq_card_439 : card_439 = combine (3, 3) [placed 2 (0, 4) card_5, inline_81] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_439 : Valid card_439 := by
  rw [eq_card_439]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 4) valid_5
  subst c
  exact valid_inline_81

theorem eq_inline_82 : inline_82 = combine (1, 1) [placed 7 (1, 4) card_5, placed 7 (5, 4) card_439] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_82 : Valid inline_82 := by
  rw [eq_inline_82]
  apply combination_rule (1, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_5
  subst c
  exact placed_valid 7 (5, 4) valid_439

theorem eq_card_440 : card_440 = combine (0, 1) [placed 0 (0, 1) card_18, inline_82] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_440 : Valid card_440 := by
  rw [eq_card_440]
  apply combination_rule (0, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_18
  subst c
  exact valid_inline_82

theorem eq_card_441 : card_441 = combine (3, 3) [placed 1 (0, 2) card_28, placed 4 (4, 1) card_58, placed 0 (0, 0) card_440] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_441 : Valid card_441 := by
  rw [eq_card_441]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 2) valid_28
  rcases hc with rfl | hc
  · exact placed_valid 4 (4, 1) valid_58
  subst c
  exact placed_valid 0 (0, 0) valid_440

theorem eq_card_442 : card_442 = combine (3, 3) [placed 7 (5, 4) card_40, placed 7 (5, 4) card_149, placed 0 (0, 0) card_440] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_442 : Valid card_442 := by
  rw [eq_card_442]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 4) valid_40
  rcases hc with rfl | hc
  · exact placed_valid 7 (5, 4) valid_149
  subst c
  exact placed_valid 0 (0, 0) valid_440

theorem eq_inline_83 : inline_83 = combine (5, 3) [placed 4 (5, 3) card_3, placed 1 (4, 0) card_5] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_83 : Valid inline_83 := by
  rw [eq_inline_83]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (5, 3) valid_3
  subst c
  exact placed_valid 1 (4, 0) valid_5

theorem eq_inline_84 : inline_84 = combine (3, 3) [placed 3 (4, 0) card_5, inline_83] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_84 : Valid inline_84 := by
  rw [eq_inline_84]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (4, 0) valid_5
  subst c
  exact valid_inline_83

theorem eq_inline_85 : inline_85 = combine (4, 1) [placed 2 (1, 1) card_5, inline_84] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_85 : Valid inline_85 := by
  rw [eq_inline_85]
  apply combination_rule (4, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 1) valid_5
  subst c
  exact valid_inline_84

theorem eq_inline_86 : inline_86 = combine (2, 4) [placed 1 (1, 1) card_5, inline_85] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_86 : Valid inline_86 := by
  rw [eq_inline_86]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_5
  subst c
  exact valid_inline_85

theorem eq_inline_87 : inline_87 = combine (4, 0) [placed 2 (0, 1) card_4, inline_86] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_87 : Valid inline_87 := by
  rw [eq_inline_87]
  apply combination_rule (4, 0) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 1) valid_4
  subst c
  exact valid_inline_86

theorem eq_inline_88 : inline_88 = combine (3, 1) [placed 0 (0, 1) card_4, inline_87] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_88 : Valid inline_88 := by
  rw [eq_inline_88]
  apply combination_rule (3, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 1) valid_4
  subst c
  exact valid_inline_87

theorem eq_inline_89 : inline_89 = combine (0, 1) [placed 7 (1, 4) card_5, inline_88] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_89 : Valid inline_89 := by
  rw [eq_inline_89]
  apply combination_rule (0, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (1, 4) valid_5
  subst c
  exact valid_inline_88

theorem eq_card_443 : card_443 = combine (2, 1) [placed 5 (1, 4) card_5, inline_89] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_443 : Valid card_443 := by
  rw [eq_card_443]
  apply combination_rule (2, 1) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 4) valid_5
  subst c
  exact valid_inline_89

theorem eq_card_444 : card_444 = combine (1, 4) [placed 0 (1, 0) card_7, placed 1 (0, 1) card_8, placed 4 (2, 0) card_9, placed 2 (0, 5) card_443] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_444 : Valid card_444 := by
  rw [eq_card_444]
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
  exact placed_valid 2 (0, 5) valid_443

theorem eq_inline_90 : inline_90 = combine (3, 3) [placed 0 (2, 0) card_20, placed 4 (3, 0) card_29, placed 0 (1, 0) card_221] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_90 : Valid inline_90 := by
  rw [eq_inline_90]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 0) valid_20
  rcases hc with rfl | hc
  · exact placed_valid 4 (3, 0) valid_29
  subst c
  exact placed_valid 0 (1, 0) valid_221

theorem eq_card_445 : card_445 = combine (3, 0) [placed 2 (0, 1) card_5, inline_90] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_445 : Valid card_445 := by
  rw [eq_card_445]
  apply combination_rule (3, 0) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 1) valid_5
  subst c
  exact valid_inline_90

theorem eq_inline_91 : inline_91 = combine (2, 4) [placed 5 (1, 7) card_0, placed 2 (0, 5) card_72] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_91 : Valid inline_91 := by
  rw [eq_inline_91]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 7) valid_0
  subst c
  exact placed_valid 2 (0, 5) valid_72

theorem eq_card_446 : card_446 = combine (2, 3) [placed 5 (1, 6) card_5, inline_91] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_446 : Valid card_446 := by
  rw [eq_card_446]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 6) valid_5
  subst c
  exact valid_inline_91

theorem eq_inline_92 : inline_92 = combine (2, 3) [placed 1 (1, 0) card_0, placed 1 (0, 1) card_445] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_inline_92 : Valid inline_92 := by
  rw [eq_inline_92]
  apply combination_rule (2, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 0) valid_0
  subst c
  exact placed_valid 1 (0, 1) valid_445

theorem eq_card_447 : card_447 = combine (2, 4) [placed 1 (1, 1) card_5, inline_92] := by
  apply computed_card_ext <;> decide +kernel

theorem valid_447 : Valid card_447 := by
  rw [eq_card_447]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_5
  subst c
  exact valid_inline_92

theorem block06_valid : Valid card_384 ∧ Valid card_385 ∧ Valid card_386 ∧ Valid card_387 ∧ Valid card_388 ∧ Valid card_389 ∧ Valid card_390 ∧ Valid card_391 ∧ Valid card_392 ∧ Valid card_393 ∧ Valid card_394 ∧ Valid card_395 ∧ Valid card_396 ∧ Valid card_397 ∧ Valid card_398 ∧ Valid card_399 ∧ Valid card_400 ∧ Valid card_401 ∧ Valid card_402 ∧ Valid card_403 ∧ Valid card_404 ∧ Valid card_405 ∧ Valid card_406 ∧ Valid card_407 ∧ Valid card_408 ∧ Valid card_409 ∧ Valid card_410 ∧ Valid card_411 ∧ Valid card_412 ∧ Valid card_413 ∧ Valid card_414 ∧ Valid card_415 ∧ Valid card_416 ∧ Valid card_417 ∧ Valid card_418 ∧ Valid card_419 ∧ Valid card_420 ∧ Valid card_421 ∧ Valid card_422 ∧ Valid card_423 ∧ Valid card_424 ∧ Valid card_425 ∧ Valid card_426 ∧ Valid card_427 ∧ Valid card_428 ∧ Valid card_429 ∧ Valid card_430 ∧ Valid card_431 ∧ Valid card_432 ∧ Valid card_433 ∧ Valid card_434 ∧ Valid card_435 ∧ Valid card_436 ∧ Valid card_437 ∧ Valid card_438 ∧ Valid card_439 ∧ Valid card_440 ∧ Valid card_441 ∧ Valid card_442 ∧ Valid card_443 ∧ Valid card_444 ∧ Valid card_445 ∧ Valid card_446 ∧ Valid card_447 ∧ True :=
  ⟨valid_384, valid_385, valid_386, valid_387, valid_388, valid_389, valid_390, valid_391, valid_392, valid_393, valid_394, valid_395, valid_396, valid_397, valid_398, valid_399, valid_400, valid_401, valid_402, valid_403, valid_404, valid_405, valid_406, valid_407, valid_408, valid_409, valid_410, valid_411, valid_412, valid_413, valid_414, valid_415, valid_416, valid_417, valid_418, valid_419, valid_420, valid_421, valid_422, valid_423, valid_424, valid_425, valid_426, valid_427, valid_428, valid_429, valid_430, valid_431, valid_432, valid_433, valid_434, valid_435, valid_436, valid_437, valid_438, valid_439, valid_440, valid_441, valid_442, valid_443, valid_444, valid_445, valid_446, valid_447, True.intro⟩

end OAI.Snaky21.Certificate
